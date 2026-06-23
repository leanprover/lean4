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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_instToJsonModuleArtifacts_toJson(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedModuleArtifacts_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_runInitAttrsForModules(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_ModuleArtifacts_oleanParts(lean_object*);
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
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* l_IO_CancelToken_set(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Array_toPArray_x27___redArg(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_compacted_region_save(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_getRegularInitAttrModIdxs(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_runtime_forget(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* l_Lean_Options_mergeBy(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object*);
uint8_t lean_strict_or(uint8_t, uint8_t);
lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*, uint8_t);
lean_object* lean_enable_initializer_execution();
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Language_Lean_pushOpt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Linter_recordLints(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Lean_writeModule(lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0 = (const lean_object*)&l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0_value;
static const lean_string_object l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1 = (const lean_object*)&l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_runFrontend___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_runFrontend___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object*);
static const lean_closure_object l_Lean_Elab_runFrontend___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Elab_runFrontend_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Elab_runFrontend_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_runFrontend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__0_value;
static const lean_closure_object l_Lean_Elab_runFrontend___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__2, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_runFrontend___closed__0_value)} };
static const lean_object* l_Lean_Elab_runFrontend___closed__1 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__1_value;
static const lean_closure_object l_Lean_Elab_runFrontend___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__2 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__2_value;
static lean_once_cell_t l_Lean_Elab_runFrontend___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_runFrontend___closed__3;
static const lean_string_object l_Lean_Elab_runFrontend___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ".olean serialization"};
static const lean_object* l_Lean_Elab_runFrontend___closed__4 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__4_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object* v_as_441_, size_t v_i_442_, size_t v_stop_443_, lean_object* v_b_444_){
_start:
{
lean_object* v___y_446_; uint8_t v___x_450_; 
v___x_450_ = lean_usize_dec_eq(v_i_442_, v_stop_443_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
v___x_451_ = lean_array_uget_borrowed(v_as_441_, v_i_442_);
if (lean_obj_tag(v___x_451_) == 0)
{
v___y_446_ = v_b_444_;
goto v___jp_445_;
}
else
{
lean_object* v_val_452_; lean_object* v___x_453_; 
v_val_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_val_452_);
v___x_453_ = lean_array_push(v_b_444_, v_val_452_);
v___y_446_ = v___x_453_;
goto v___jp_445_;
}
}
else
{
return v_b_444_;
}
v___jp_445_:
{
size_t v___x_447_; size_t v___x_448_; 
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_442_, v___x_447_);
v_i_442_ = v___x_448_;
v_b_444_ = v___y_446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object* v_as_454_, lean_object* v_i_455_, lean_object* v_stop_456_, lean_object* v_b_457_){
_start:
{
size_t v_i_boxed_458_; size_t v_stop_boxed_459_; lean_object* v_res_460_; 
v_i_boxed_458_ = lean_unbox_usize(v_i_455_);
lean_dec(v_i_455_);
v_stop_boxed_459_ = lean_unbox_usize(v_stop_456_);
lean_dec(v_stop_456_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_454_, v_i_boxed_458_, v_stop_boxed_459_, v_b_457_);
lean_dec_ref(v_as_454_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object* v_as_463_, lean_object* v_start_464_, lean_object* v_stop_465_){
_start:
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_467_ = lean_nat_dec_lt(v_start_464_, v_stop_465_);
if (v___x_467_ == 0)
{
return v___x_466_;
}
else
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = lean_array_get_size(v_as_463_);
v___x_469_ = lean_nat_dec_le(v_stop_465_, v___x_468_);
if (v___x_469_ == 0)
{
uint8_t v___x_470_; 
v___x_470_ = lean_nat_dec_lt(v_start_464_, v___x_468_);
if (v___x_470_ == 0)
{
return v___x_466_;
}
else
{
size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_usize_of_nat(v_start_464_);
v___x_472_ = lean_usize_of_nat(v___x_468_);
v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_463_, v___x_471_, v___x_472_, v___x_466_);
return v___x_473_;
}
}
else
{
size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_usize_of_nat(v_start_464_);
v___x_475_ = lean_usize_of_nat(v_stop_465_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_463_, v___x_474_, v___x_475_, v___x_466_);
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object* v_as_477_, lean_object* v_start_478_, lean_object* v_stop_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v_as_477_, v_start_478_, v_stop_479_);
lean_dec(v_stop_479_);
lean_dec(v_start_478_);
lean_dec_ref(v_as_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t v_sz_481_, size_t v_i_482_, lean_object* v_bs_483_){
_start:
{
uint8_t v___x_484_; 
v___x_484_ = lean_usize_dec_lt(v_i_482_, v_sz_481_);
if (v___x_484_ == 0)
{
return v_bs_483_;
}
else
{
lean_object* v_v_485_; lean_object* v_elabSnap_486_; lean_object* v_infoTreeSnap_487_; lean_object* v___x_488_; lean_object* v_infoTree_x3f_489_; lean_object* v___x_490_; lean_object* v_bs_x27_491_; size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v_v_485_ = lean_array_uget_borrowed(v_bs_483_, v_i_482_);
v_elabSnap_486_ = lean_ctor_get(v_v_485_, 3);
v_infoTreeSnap_487_ = lean_ctor_get(v_elabSnap_486_, 3);
lean_inc_ref(v_infoTreeSnap_487_);
v___x_488_ = l_Lean_Language_SnapshotTask_get___redArg(v_infoTreeSnap_487_);
v_infoTree_x3f_489_ = lean_ctor_get(v___x_488_, 2);
lean_inc(v_infoTree_x3f_489_);
lean_dec(v___x_488_);
v___x_490_ = lean_unsigned_to_nat(0u);
v_bs_x27_491_ = lean_array_uset(v_bs_483_, v_i_482_, v___x_490_);
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_482_, v___x_492_);
v___x_494_ = lean_array_uset(v_bs_x27_491_, v_i_482_, v_infoTree_x3f_489_);
v_i_482_ = v___x_493_;
v_bs_483_ = v___x_494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object* v_sz_496_, lean_object* v_i_497_, lean_object* v_bs_498_){
_start:
{
size_t v_sz_boxed_499_; size_t v_i_boxed_500_; lean_object* v_res_501_; 
v_sz_boxed_499_ = lean_unbox_usize(v_sz_496_);
lean_dec(v_sz_496_);
v_i_boxed_500_ = lean_unbox_usize(v_i_497_);
lean_dec(v_i_497_);
v_res_501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_boxed_499_, v_i_boxed_500_, v_bs_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(lean_object* v_as_502_, size_t v_i_503_, size_t v_stop_504_, lean_object* v_b_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_usize_dec_eq(v_i_503_, v_stop_504_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; size_t v___x_509_; size_t v___x_510_; 
v___x_507_ = lean_array_uget_borrowed(v_as_502_, v_i_503_);
lean_inc(v___x_507_);
v___x_508_ = l_Lean_MessageLog_append(v_b_505_, v___x_507_);
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_503_, v___x_509_);
v_i_503_ = v___x_510_;
v_b_505_ = v___x_508_;
goto _start;
}
else
{
return v_b_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object* v_as_512_, lean_object* v_i_513_, lean_object* v_stop_514_, lean_object* v_b_515_){
_start:
{
size_t v_i_boxed_516_; size_t v_stop_boxed_517_; lean_object* v_res_518_; 
v_i_boxed_516_ = lean_unbox_usize(v_i_513_);
lean_dec(v_i_513_);
v_stop_boxed_517_ = lean_unbox_usize(v_stop_514_);
lean_dec(v_stop_514_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_as_512_, v_i_boxed_516_, v_stop_boxed_517_, v_b_515_);
lean_dec_ref(v_as_512_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t v_sz_519_, size_t v_i_520_, lean_object* v_bs_521_){
_start:
{
uint8_t v___x_522_; 
v___x_522_ = lean_usize_dec_lt(v_i_520_, v_sz_519_);
if (v___x_522_ == 0)
{
return v_bs_521_;
}
else
{
lean_object* v_v_523_; lean_object* v_stx_524_; lean_object* v___x_525_; lean_object* v_bs_x27_526_; size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; 
v_v_523_ = lean_array_uget_borrowed(v_bs_521_, v_i_520_);
v_stx_524_ = lean_ctor_get(v_v_523_, 1);
lean_inc(v_stx_524_);
v___x_525_ = lean_unsigned_to_nat(0u);
v_bs_x27_526_ = lean_array_uset(v_bs_521_, v_i_520_, v___x_525_);
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_add(v_i_520_, v___x_527_);
v___x_529_ = lean_array_uset(v_bs_x27_526_, v_i_520_, v_stx_524_);
v_i_520_ = v___x_528_;
v_bs_521_ = v___x_529_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object* v_sz_531_, lean_object* v_i_532_, lean_object* v_bs_533_){
_start:
{
size_t v_sz_boxed_534_; size_t v_i_boxed_535_; lean_object* v_res_536_; 
v_sz_boxed_534_ = lean_unbox_usize(v_sz_531_);
lean_dec(v_sz_531_);
v_i_boxed_535_ = lean_unbox_usize(v_i_532_);
lean_dec(v_i_532_);
v_res_536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_boxed_534_, v_i_boxed_535_, v_bs_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(size_t v_sz_537_, size_t v_i_538_, lean_object* v_bs_539_){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = lean_usize_dec_lt(v_i_538_, v_sz_537_);
if (v___x_540_ == 0)
{
return v_bs_539_;
}
else
{
lean_object* v_v_541_; lean_object* v_diagnostics_542_; lean_object* v_msgLog_543_; lean_object* v___x_544_; lean_object* v_bs_x27_545_; size_t v___x_546_; size_t v___x_547_; lean_object* v___x_548_; 
v_v_541_ = lean_array_uget_borrowed(v_bs_539_, v_i_538_);
v_diagnostics_542_ = lean_ctor_get(v_v_541_, 1);
v_msgLog_543_ = lean_ctor_get(v_diagnostics_542_, 0);
lean_inc_ref(v_msgLog_543_);
v___x_544_ = lean_unsigned_to_nat(0u);
v_bs_x27_545_ = lean_array_uset(v_bs_539_, v_i_538_, v___x_544_);
v___x_546_ = ((size_t)1ULL);
v___x_547_ = lean_usize_add(v_i_538_, v___x_546_);
v___x_548_ = lean_array_uset(v_bs_x27_545_, v_i_538_, v_msgLog_543_);
v_i_538_ = v___x_547_;
v_bs_539_ = v___x_548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3___boxed(lean_object* v_sz_550_, lean_object* v_i_551_, lean_object* v_bs_552_){
_start:
{
size_t v_sz_boxed_553_; size_t v_i_boxed_554_; lean_object* v_res_555_; 
v_sz_boxed_553_ = lean_unbox_usize(v_sz_550_);
lean_dec(v_sz_550_);
v_i_boxed_554_ = lean_unbox_usize(v_i_551_);
lean_dec(v_i_551_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_sz_boxed_553_, v_i_boxed_554_, v_bs_552_);
return v_res_555_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_unsigned_to_nat(32u);
v___x_557_ = lean_mk_empty_array_with_capacity(v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1(void){
_start:
{
size_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_559_ = ((size_t)5ULL);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_unsigned_to_nat(32u);
v___x_562_ = lean_mk_empty_array_with_capacity(v___x_561_);
v___x_563_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0);
v___x_564_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
lean_ctor_set(v___x_564_, 2, v___x_560_);
lean_ctor_set(v___x_564_, 3, v___x_560_);
lean_ctor_set_usize(v___x_564_, 4, v___x_559_);
return v___x_564_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = l_Lean_NameSet_empty;
v___x_566_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1);
v___x_567_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
lean_ctor_set(v___x_567_, 2, v___x_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(lean_object* v_inputCtx_568_, lean_object* v_initialSnap_569_, lean_object* v_t_570_, lean_object* v_commands_571_){
_start:
{
lean_object* v_snap_573_; lean_object* v_parserState_574_; lean_object* v_elabSnap_575_; lean_object* v_nextCmdSnap_x3f_576_; lean_object* v_commands_577_; 
v_snap_573_ = lean_task_get_own(v_t_570_);
v_parserState_574_ = lean_ctor_get(v_snap_573_, 2);
lean_inc_ref(v_parserState_574_);
v_elabSnap_575_ = lean_ctor_get(v_snap_573_, 3);
lean_inc_ref(v_elabSnap_575_);
v_nextCmdSnap_x3f_576_ = lean_ctor_get(v_snap_573_, 4);
lean_inc(v_nextCmdSnap_x3f_576_);
v_commands_577_ = lean_array_push(v_commands_571_, v_snap_573_);
if (lean_obj_tag(v_nextCmdSnap_x3f_576_) == 1)
{
lean_object* v_val_578_; lean_object* v_task_579_; 
lean_dec_ref(v_elabSnap_575_);
lean_dec_ref(v_parserState_574_);
v_val_578_ = lean_ctor_get(v_nextCmdSnap_x3f_576_, 0);
lean_inc(v_val_578_);
lean_dec_ref_known(v_nextCmdSnap_x3f_576_, 1);
v_task_579_ = lean_ctor_get(v_val_578_, 3);
lean_inc_ref(v_task_579_);
lean_dec(v_val_578_);
v_t_570_ = v_task_579_;
v_commands_571_ = v_commands_577_;
goto _start;
}
else
{
lean_object* v___x_581_; lean_object* v___y_583_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; size_t v_sz_629_; size_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
lean_dec(v_nextCmdSnap_x3f_576_);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
lean_inc_ref(v_initialSnap_569_);
v___x_627_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_initialSnap_569_);
v___x_628_ = l_Lean_Language_SnapshotTree_getAll(v___x_627_);
v_sz_629_ = lean_array_size(v___x_628_);
v___x_630_ = ((size_t)0ULL);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_sz_629_, v___x_630_, v___x_628_);
v___x_632_ = lean_array_get_size(v___x_631_);
v___x_633_ = lean_nat_dec_lt(v___x_581_, v___x_632_);
if (v___x_633_ == 0)
{
lean_dec_ref(v___x_631_);
v___y_583_ = v___x_626_;
goto v___jp_582_;
}
else
{
uint8_t v___x_634_; 
v___x_634_ = lean_nat_dec_le(v___x_632_, v___x_632_);
if (v___x_634_ == 0)
{
if (v___x_633_ == 0)
{
lean_dec_ref(v___x_631_);
v___y_583_ = v___x_626_;
goto v___jp_582_;
}
else
{
size_t v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_usize_of_nat(v___x_632_);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v___x_631_, v___x_630_, v___x_635_, v___x_626_);
lean_dec_ref(v___x_631_);
v___y_583_ = v___x_636_;
goto v___jp_582_;
}
}
else
{
size_t v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_usize_of_nat(v___x_632_);
v___x_638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v___x_631_, v___x_630_, v___x_637_, v___x_626_);
lean_dec_ref(v___x_631_);
v___y_583_ = v___x_638_;
goto v___jp_582_;
}
}
v___jp_582_:
{
size_t v_sz_584_; lean_object* v_resultSnap_585_; lean_object* v___x_586_; lean_object* v_cmdState_587_; lean_object* v_infoState_588_; lean_object* v_env_589_; lean_object* v_scopes_590_; lean_object* v_usedQuotCtxts_591_; lean_object* v_nextMacroScope_592_; lean_object* v_maxRecDepth_593_; lean_object* v_ngen_594_; lean_object* v_auxDeclNGen_595_; lean_object* v_traceState_596_; lean_object* v_snapshotTasks_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_624_; 
v_sz_584_ = lean_array_size(v_commands_577_);
v_resultSnap_585_ = lean_ctor_get(v_elabSnap_575_, 2);
lean_inc_ref(v_resultSnap_585_);
lean_dec_ref(v_elabSnap_575_);
v___x_586_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_585_);
v_cmdState_587_ = lean_ctor_get(v___x_586_, 1);
lean_inc_ref(v_cmdState_587_);
lean_dec(v___x_586_);
v_infoState_588_ = lean_ctor_get(v_cmdState_587_, 8);
v_env_589_ = lean_ctor_get(v_cmdState_587_, 0);
v_scopes_590_ = lean_ctor_get(v_cmdState_587_, 2);
v_usedQuotCtxts_591_ = lean_ctor_get(v_cmdState_587_, 3);
v_nextMacroScope_592_ = lean_ctor_get(v_cmdState_587_, 4);
v_maxRecDepth_593_ = lean_ctor_get(v_cmdState_587_, 5);
v_ngen_594_ = lean_ctor_get(v_cmdState_587_, 6);
v_auxDeclNGen_595_ = lean_ctor_get(v_cmdState_587_, 7);
v_traceState_596_ = lean_ctor_get(v_cmdState_587_, 9);
v_snapshotTasks_597_ = lean_ctor_get(v_cmdState_587_, 10);
v_isSharedCheck_624_ = !lean_is_exclusive(v_cmdState_587_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v_cmdState_587_, 1);
lean_dec(v_unused_625_);
v___x_599_ = v_cmdState_587_;
v_isShared_600_ = v_isSharedCheck_624_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_snapshotTasks_597_);
lean_inc(v_traceState_596_);
lean_inc(v_infoState_588_);
lean_inc(v_auxDeclNGen_595_);
lean_inc(v_ngen_594_);
lean_inc(v_maxRecDepth_593_);
lean_inc(v_nextMacroScope_592_);
lean_inc(v_usedQuotCtxts_591_);
lean_inc(v_scopes_590_);
lean_inc(v_env_589_);
lean_dec(v_cmdState_587_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_624_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
uint8_t v_enabled_601_; lean_object* v_assignment_602_; lean_object* v_lazyAssignment_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_622_; 
v_enabled_601_ = lean_ctor_get_uint8(v_infoState_588_, sizeof(void*)*3);
v_assignment_602_ = lean_ctor_get(v_infoState_588_, 0);
v_lazyAssignment_603_ = lean_ctor_get(v_infoState_588_, 1);
v_isSharedCheck_622_ = !lean_is_exclusive(v_infoState_588_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v_infoState_588_, 2);
lean_dec(v_unused_623_);
v___x_605_ = v_infoState_588_;
v_isShared_606_ = v_isSharedCheck_622_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_lazyAssignment_603_);
lean_inc(v_assignment_602_);
lean_dec(v_infoState_588_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_622_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_pos_607_; size_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v_trees_612_; lean_object* v___x_614_; 
v_pos_607_ = lean_ctor_get(v_parserState_574_, 0);
lean_inc(v_pos_607_);
v___x_608_ = ((size_t)0ULL);
lean_inc_ref(v_commands_577_);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_584_, v___x_608_, v_commands_577_);
v___x_610_ = lean_array_get_size(v___x_609_);
v___x_611_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v___x_609_, v___x_581_, v___x_610_);
lean_dec_ref(v___x_609_);
v_trees_612_ = l_Array_toPArray_x27___redArg(v___x_611_);
lean_dec_ref(v___x_611_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 2, v_trees_612_);
v___x_614_ = v___x_605_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_assignment_602_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_lazyAssignment_603_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_trees_612_);
lean_ctor_set_uint8(v_reuseFailAlloc_621_, sizeof(void*)*3, v_enabled_601_);
v___x_614_ = v_reuseFailAlloc_621_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 8, v___x_614_);
lean_ctor_set(v___x_599_, 1, v___y_583_);
v___x_616_ = v___x_599_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_env_589_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___y_583_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_scopes_590_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_usedQuotCtxts_591_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_nextMacroScope_592_);
lean_ctor_set(v_reuseFailAlloc_620_, 5, v_maxRecDepth_593_);
lean_ctor_set(v_reuseFailAlloc_620_, 6, v_ngen_594_);
lean_ctor_set(v_reuseFailAlloc_620_, 7, v_auxDeclNGen_595_);
lean_ctor_set(v_reuseFailAlloc_620_, 8, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_620_, 9, v_traceState_596_);
lean_ctor_set(v_reuseFailAlloc_620_, 10, v_snapshotTasks_597_);
v___x_616_ = v_reuseFailAlloc_620_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_584_, v___x_608_, v_commands_577_);
v___x_618_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v_parserState_574_);
lean_ctor_set(v___x_618_, 2, v_pos_607_);
lean_ctor_set(v___x_618_, 3, v___x_617_);
v___x_619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v_inputCtx_568_);
lean_ctor_set(v___x_619_, 2, v_initialSnap_569_);
return v___x_619_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___boxed(lean_object* v_inputCtx_639_, lean_object* v_initialSnap_640_, lean_object* v_t_641_, lean_object* v_commands_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_639_, v_initialSnap_640_, v_t_641_, v_commands_642_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object* v_inputCtx_647_, lean_object* v_parserState_648_, lean_object* v_commandState_649_, lean_object* v_old_x3f_650_){
_start:
{
lean_object* v___y_653_; 
if (lean_obj_tag(v_old_x3f_650_) == 0)
{
lean_object* v___x_658_; 
v___x_658_ = lean_box(0);
v___y_653_ = v___x_658_;
goto v___jp_652_;
}
else
{
lean_object* v_val_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_669_; 
v_val_659_ = lean_ctor_get(v_old_x3f_650_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v_old_x3f_650_);
if (v_isSharedCheck_669_ == 0)
{
v___x_661_ = v_old_x3f_650_;
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_val_659_);
lean_dec(v_old_x3f_650_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_669_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_inputCtx_663_; lean_object* v_initialSnap_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v_inputCtx_663_ = lean_ctor_get(v_val_659_, 1);
lean_inc_ref(v_inputCtx_663_);
v_initialSnap_664_ = lean_ctor_get(v_val_659_, 2);
lean_inc_ref(v_initialSnap_664_);
lean_dec(v_val_659_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_inputCtx_663_);
lean_ctor_set(v___x_665_, 1, v_initialSnap_664_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_665_);
v___x_667_ = v___x_661_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
v___y_653_ = v___x_667_;
goto v___jp_652_;
}
}
}
v___jp_652_:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = l_Lean_Language_Lean_processCommands(v_inputCtx_647_, v_parserState_648_, v_commandState_649_, v___y_653_);
lean_inc_ref(v___x_654_);
v___x_655_ = lean_task_get_own(v___x_654_);
v___x_656_ = ((lean_object*)(l_Lean_Elab_IO_processCommandsIncrementally___closed__0));
v___x_657_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_647_, v___x_655_, v___x_654_, v___x_656_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally___boxed(lean_object* v_inputCtx_670_, lean_object* v_parserState_671_, lean_object* v_commandState_672_, lean_object* v_old_x3f_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_670_, v_parserState_671_, v_commandState_672_, v_old_x3f_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object* v_inputCtx_676_, lean_object* v_parserState_677_, lean_object* v_commandState_678_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v_toState_682_; lean_object* v___x_683_; 
v___x_680_ = lean_box(0);
v___x_681_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_676_, v_parserState_677_, v_commandState_678_, v___x_680_);
v_toState_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc_ref(v_toState_682_);
lean_dec_ref(v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v_toState_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands___boxed(lean_object* v_inputCtx_684_, lean_object* v_parserState_685_, lean_object* v_commandState_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Elab_IO_processCommands(v_inputCtx_684_, v_parserState_685_, v_commandState_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object* v_input_694_, lean_object* v_env_695_, lean_object* v_opts_696_, lean_object* v_fileName_697_){
_start:
{
lean_object* v___y_700_; 
if (lean_obj_tag(v_fileName_697_) == 0)
{
lean_object* v___x_720_; 
v___x_720_ = ((lean_object*)(l_Lean_Elab_process___closed__1));
v___y_700_ = v___x_720_;
goto v___jp_699_;
}
else
{
lean_object* v_val_721_; 
v_val_721_ = lean_ctor_get(v_fileName_697_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v_fileName_697_, 1);
v___y_700_ = v_val_721_;
goto v___jp_699_;
}
v___jp_699_:
{
uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v_inputCtx_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_719_; 
v___x_701_ = 1;
v___x_702_ = lean_string_utf8_byte_size(v_input_694_);
v_inputCtx_703_ = l_Lean_Parser_mkInputContext___redArg(v_input_694_, v___y_700_, v___x_701_, v___x_702_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_process___closed__0));
v___x_705_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
v___x_706_ = l_Lean_Elab_Command_mkState(v_env_695_, v___x_705_, v_opts_696_);
v___x_707_ = l_Lean_Elab_IO_processCommands(v_inputCtx_703_, v___x_704_, v___x_706_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_719_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_719_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_719_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v_commandState_712_; lean_object* v_env_713_; lean_object* v_messages_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v_commandState_712_ = lean_ctor_get(v_a_708_, 0);
lean_inc_ref(v_commandState_712_);
lean_dec(v_a_708_);
v_env_713_ = lean_ctor_get(v_commandState_712_, 0);
lean_inc_ref(v_env_713_);
v_messages_714_ = lean_ctor_get(v_commandState_712_, 1);
lean_inc_ref(v_messages_714_);
lean_dec_ref(v_commandState_712_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v_env_713_);
lean_ctor_set(v___x_715_, 1, v_messages_714_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_715_);
v___x_717_ = v___x_710_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process___boxed(lean_object* v_input_722_, lean_object* v_env_723_, lean_object* v_opts_724_, lean_object* v_fileName_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Elab_process(v_input_722_, v_env_723_, v_opts_724_, v_fileName_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(lean_object* v_t_728_, lean_object* v_cmdStx_x3f_729_, lean_object* v_acc_730_){
_start:
{
lean_object* v_element_731_; lean_object* v_diagnostics_732_; lean_object* v_children_733_; lean_object* v_msgLog_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_752_; 
v_element_731_ = lean_ctor_get(v_t_728_, 0);
v_diagnostics_732_ = lean_ctor_get(v_element_731_, 1);
lean_inc_ref(v_diagnostics_732_);
v_children_733_ = lean_ctor_get(v_t_728_, 1);
lean_inc_ref(v_children_733_);
lean_dec_ref(v_t_728_);
v_msgLog_734_ = lean_ctor_get(v_diagnostics_732_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v_diagnostics_732_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v_diagnostics_732_, 1);
lean_dec(v_unused_753_);
v___x_736_ = v_diagnostics_732_;
v_isShared_737_ = v_isSharedCheck_752_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_msgLog_734_);
lean_dec(v_diagnostics_732_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_752_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
lean_inc(v_cmdStx_x3f_729_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 1, v_msgLog_734_);
lean_ctor_set(v___x_736_, 0, v_cmdStx_x3f_729_);
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_cmdStx_x3f_729_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_msgLog_734_);
v___x_739_ = v_reuseFailAlloc_751_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v_acc_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v_acc_740_ = lean_array_push(v_acc_730_, v___x_739_);
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_array_get_size(v_children_733_);
v___x_743_ = lean_nat_dec_lt(v___x_741_, v___x_742_);
if (v___x_743_ == 0)
{
lean_dec_ref(v_children_733_);
lean_dec(v_cmdStx_x3f_729_);
return v_acc_740_;
}
else
{
uint8_t v___x_744_; 
v___x_744_ = lean_nat_dec_le(v___x_742_, v___x_742_);
if (v___x_744_ == 0)
{
if (v___x_743_ == 0)
{
lean_dec_ref(v_children_733_);
lean_dec(v_cmdStx_x3f_729_);
return v_acc_740_;
}
else
{
size_t v___x_745_; size_t v___x_746_; lean_object* v___x_747_; 
v___x_745_ = ((size_t)0ULL);
v___x_746_ = lean_usize_of_nat(v___x_742_);
v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_729_, v_children_733_, v___x_745_, v___x_746_, v_acc_740_);
lean_dec_ref(v_children_733_);
return v___x_747_;
}
}
else
{
size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((size_t)0ULL);
v___x_749_ = lean_usize_of_nat(v___x_742_);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_729_, v_children_733_, v___x_748_, v___x_749_, v_acc_740_);
lean_dec_ref(v_children_733_);
return v___x_750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(lean_object* v_cmdStx_x3f_754_, lean_object* v_as_755_, size_t v_i_756_, size_t v_stop_757_, lean_object* v_b_758_){
_start:
{
lean_object* v___y_760_; uint8_t v___x_764_; 
v___x_764_ = lean_usize_dec_eq(v_i_756_, v_stop_757_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v_stx_x3f_766_; lean_object* v___x_767_; 
v___x_765_ = lean_array_uget_borrowed(v_as_755_, v_i_756_);
v_stx_x3f_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v___x_765_);
v___x_767_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_765_);
if (lean_obj_tag(v_stx_x3f_766_) == 0)
{
lean_object* v___x_768_; 
lean_inc(v_cmdStx_x3f_754_);
v___x_768_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_767_, v_cmdStx_x3f_754_, v_b_758_);
v___y_760_ = v___x_768_;
goto v___jp_759_;
}
else
{
lean_object* v___x_769_; 
lean_inc_ref(v_stx_x3f_766_);
v___x_769_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_767_, v_stx_x3f_766_, v_b_758_);
v___y_760_ = v___x_769_;
goto v___jp_759_;
}
}
else
{
lean_dec(v_cmdStx_x3f_754_);
return v_b_758_;
}
v___jp_759_:
{
size_t v___x_761_; size_t v___x_762_; 
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_756_, v___x_761_);
v_i_756_ = v___x_762_;
v_b_758_ = v___y_760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0___boxed(lean_object* v_cmdStx_x3f_770_, lean_object* v_as_771_, lean_object* v_i_772_, lean_object* v_stop_773_, lean_object* v_b_774_){
_start:
{
size_t v_i_boxed_775_; size_t v_stop_boxed_776_; lean_object* v_res_777_; 
v_i_boxed_775_ = lean_unbox_usize(v_i_772_);
lean_dec(v_i_772_);
v_stop_boxed_776_ = lean_unbox_usize(v_stop_773_);
lean_dec(v_stop_773_);
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_770_, v_as_771_, v_i_boxed_775_, v_stop_boxed_776_, v_b_774_);
lean_dec_ref(v_as_771_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3(lean_object* v_filePath_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_lean_x3f_780_; lean_object* v_olean_x3f_781_; lean_object* v_oleanServer_x3f_782_; lean_object* v_ilean_x3f_783_; lean_object* v_irSig_x3f_784_; lean_object* v_ir_x3f_785_; lean_object* v_c_x3f_786_; lean_object* v_bc_x3f_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
v_lean_x3f_780_ = lean_ctor_get(v_a_779_, 0);
v_olean_x3f_781_ = lean_ctor_get(v_a_779_, 1);
v_oleanServer_x3f_782_ = lean_ctor_get(v_a_779_, 2);
v_ilean_x3f_783_ = lean_ctor_get(v_a_779_, 4);
v_irSig_x3f_784_ = lean_ctor_get(v_a_779_, 5);
v_ir_x3f_785_ = lean_ctor_get(v_a_779_, 6);
v_c_x3f_786_ = lean_ctor_get(v_a_779_, 7);
v_bc_x3f_787_ = lean_ctor_get(v_a_779_, 8);
v_isSharedCheck_795_ = !lean_is_exclusive(v_a_779_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_a_779_, 3);
lean_dec(v_unused_796_);
v___x_789_ = v_a_779_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_bc_x3f_787_);
lean_inc(v_c_x3f_786_);
lean_inc(v_ir_x3f_785_);
lean_inc(v_irSig_x3f_784_);
lean_inc(v_ilean_x3f_783_);
lean_inc(v_oleanServer_x3f_782_);
lean_inc(v_olean_x3f_781_);
lean_inc(v_lean_x3f_780_);
lean_dec(v_a_779_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v_filePath_778_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 3, v___x_791_);
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_lean_x3f_780_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_olean_x3f_781_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_oleanServer_x3f_782_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_ilean_x3f_783_);
lean_ctor_set(v_reuseFailAlloc_794_, 5, v_irSig_x3f_784_);
lean_ctor_set(v_reuseFailAlloc_794_, 6, v_ir_x3f_785_);
lean_ctor_set(v_reuseFailAlloc_794_, 7, v_c_x3f_786_);
lean_ctor_set(v_reuseFailAlloc_794_, 8, v_bc_x3f_787_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1(lean_object* v_filePath_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_lean_x3f_799_; lean_object* v_olean_x3f_800_; lean_object* v_oleanServer_x3f_801_; lean_object* v_oleanPrivate_x3f_802_; lean_object* v_ilean_x3f_803_; lean_object* v_ir_x3f_804_; lean_object* v_c_x3f_805_; lean_object* v_bc_x3f_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v_lean_x3f_799_ = lean_ctor_get(v_a_798_, 0);
v_olean_x3f_800_ = lean_ctor_get(v_a_798_, 1);
v_oleanServer_x3f_801_ = lean_ctor_get(v_a_798_, 2);
v_oleanPrivate_x3f_802_ = lean_ctor_get(v_a_798_, 3);
v_ilean_x3f_803_ = lean_ctor_get(v_a_798_, 4);
v_ir_x3f_804_ = lean_ctor_get(v_a_798_, 6);
v_c_x3f_805_ = lean_ctor_get(v_a_798_, 7);
v_bc_x3f_806_ = lean_ctor_get(v_a_798_, 8);
v_isSharedCheck_814_ = !lean_is_exclusive(v_a_798_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v_a_798_, 5);
lean_dec(v_unused_815_);
v___x_808_ = v_a_798_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_bc_x3f_806_);
lean_inc(v_c_x3f_805_);
lean_inc(v_ir_x3f_804_);
lean_inc(v_ilean_x3f_803_);
lean_inc(v_oleanPrivate_x3f_802_);
lean_inc(v_oleanServer_x3f_801_);
lean_inc(v_olean_x3f_800_);
lean_inc(v_lean_x3f_799_);
lean_dec(v_a_798_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v_filePath_797_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 5, v___x_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_lean_x3f_799_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_olean_x3f_800_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_oleanServer_x3f_801_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_oleanPrivate_x3f_802_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v_ilean_x3f_803_);
lean_ctor_set(v_reuseFailAlloc_813_, 5, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_813_, 6, v_ir_x3f_804_);
lean_ctor_set(v_reuseFailAlloc_813_, 7, v_c_x3f_805_);
lean_ctor_set(v_reuseFailAlloc_813_, 8, v_bc_x3f_806_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4(lean_object* v_filePath_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_lean_x3f_818_; lean_object* v_olean_x3f_819_; lean_object* v_oleanPrivate_x3f_820_; lean_object* v_ilean_x3f_821_; lean_object* v_irSig_x3f_822_; lean_object* v_ir_x3f_823_; lean_object* v_c_x3f_824_; lean_object* v_bc_x3f_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_833_; 
v_lean_x3f_818_ = lean_ctor_get(v_a_817_, 0);
v_olean_x3f_819_ = lean_ctor_get(v_a_817_, 1);
v_oleanPrivate_x3f_820_ = lean_ctor_get(v_a_817_, 3);
v_ilean_x3f_821_ = lean_ctor_get(v_a_817_, 4);
v_irSig_x3f_822_ = lean_ctor_get(v_a_817_, 5);
v_ir_x3f_823_ = lean_ctor_get(v_a_817_, 6);
v_c_x3f_824_ = lean_ctor_get(v_a_817_, 7);
v_bc_x3f_825_ = lean_ctor_get(v_a_817_, 8);
v_isSharedCheck_833_ = !lean_is_exclusive(v_a_817_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v_a_817_, 2);
lean_dec(v_unused_834_);
v___x_827_ = v_a_817_;
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_bc_x3f_825_);
lean_inc(v_c_x3f_824_);
lean_inc(v_ir_x3f_823_);
lean_inc(v_irSig_x3f_822_);
lean_inc(v_ilean_x3f_821_);
lean_inc(v_oleanPrivate_x3f_820_);
lean_inc(v_olean_x3f_819_);
lean_inc(v_lean_x3f_818_);
lean_dec(v_a_817_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v_filePath_816_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 2, v___x_829_);
v___x_831_ = v___x_827_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_lean_x3f_818_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_olean_x3f_819_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v_oleanPrivate_x3f_820_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v_ilean_x3f_821_);
lean_ctor_set(v_reuseFailAlloc_832_, 5, v_irSig_x3f_822_);
lean_ctor_set(v_reuseFailAlloc_832_, 6, v_ir_x3f_823_);
lean_ctor_set(v_reuseFailAlloc_832_, 7, v_c_x3f_824_);
lean_ctor_set(v_reuseFailAlloc_832_, 8, v_bc_x3f_825_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(lean_object* v_a_835_, lean_object* v_x_836_){
_start:
{
if (lean_obj_tag(v_x_836_) == 0)
{
uint8_t v___x_837_; 
v___x_837_ = 0;
return v___x_837_;
}
else
{
lean_object* v_key_838_; lean_object* v_tail_839_; uint8_t v___x_840_; 
v_key_838_ = lean_ctor_get(v_x_836_, 0);
v_tail_839_ = lean_ctor_get(v_x_836_, 2);
v___x_840_ = lean_string_dec_eq(v_key_838_, v_a_835_);
if (v___x_840_ == 0)
{
v_x_836_ = v_tail_839_;
goto _start;
}
else
{
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg___boxed(lean_object* v_a_842_, lean_object* v_x_843_){
_start:
{
uint8_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_842_, v_x_843_);
lean_dec(v_x_843_);
lean_dec_ref(v_a_842_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(lean_object* v_m_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_buckets_848_; lean_object* v___x_849_; uint64_t v___x_850_; uint64_t v___x_851_; uint64_t v___x_852_; uint64_t v_fold_853_; uint64_t v___x_854_; uint64_t v___x_855_; uint64_t v___x_856_; size_t v___x_857_; size_t v___x_858_; size_t v___x_859_; size_t v___x_860_; size_t v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_buckets_848_ = lean_ctor_get(v_m_846_, 1);
v___x_849_ = lean_array_get_size(v_buckets_848_);
v___x_850_ = lean_string_hash(v_a_847_);
v___x_851_ = 32ULL;
v___x_852_ = lean_uint64_shift_right(v___x_850_, v___x_851_);
v_fold_853_ = lean_uint64_xor(v___x_850_, v___x_852_);
v___x_854_ = 16ULL;
v___x_855_ = lean_uint64_shift_right(v_fold_853_, v___x_854_);
v___x_856_ = lean_uint64_xor(v_fold_853_, v___x_855_);
v___x_857_ = lean_uint64_to_usize(v___x_856_);
v___x_858_ = lean_usize_of_nat(v___x_849_);
v___x_859_ = ((size_t)1ULL);
v___x_860_ = lean_usize_sub(v___x_858_, v___x_859_);
v___x_861_ = lean_usize_land(v___x_857_, v___x_860_);
v___x_862_ = lean_array_uget_borrowed(v_buckets_848_, v___x_861_);
v___x_863_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_847_, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg___boxed(lean_object* v_m_864_, lean_object* v_a_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_864_, v_a_865_);
lean_dec_ref(v_a_865_);
lean_dec_ref(v_m_864_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(lean_object* v_a_868_, lean_object* v_fallback_869_, lean_object* v_x_870_){
_start:
{
if (lean_obj_tag(v_x_870_) == 0)
{
lean_inc(v_fallback_869_);
return v_fallback_869_;
}
else
{
lean_object* v_key_871_; lean_object* v_value_872_; lean_object* v_tail_873_; uint8_t v___x_874_; 
v_key_871_ = lean_ctor_get(v_x_870_, 0);
v_value_872_ = lean_ctor_get(v_x_870_, 1);
v_tail_873_ = lean_ctor_get(v_x_870_, 2);
v___x_874_ = lean_string_dec_eq(v_key_871_, v_a_868_);
if (v___x_874_ == 0)
{
v_x_870_ = v_tail_873_;
goto _start;
}
else
{
lean_inc(v_value_872_);
return v_value_872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg___boxed(lean_object* v_a_876_, lean_object* v_fallback_877_, lean_object* v_x_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_876_, v_fallback_877_, v_x_878_);
lean_dec(v_x_878_);
lean_dec(v_fallback_877_);
lean_dec_ref(v_a_876_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(lean_object* v_m_880_, lean_object* v_a_881_, lean_object* v_fallback_882_){
_start:
{
lean_object* v_buckets_883_; lean_object* v___x_884_; uint64_t v___x_885_; uint64_t v___x_886_; uint64_t v___x_887_; uint64_t v_fold_888_; uint64_t v___x_889_; uint64_t v___x_890_; uint64_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_buckets_883_ = lean_ctor_get(v_m_880_, 1);
v___x_884_ = lean_array_get_size(v_buckets_883_);
v___x_885_ = lean_string_hash(v_a_881_);
v___x_886_ = 32ULL;
v___x_887_ = lean_uint64_shift_right(v___x_885_, v___x_886_);
v_fold_888_ = lean_uint64_xor(v___x_885_, v___x_887_);
v___x_889_ = 16ULL;
v___x_890_ = lean_uint64_shift_right(v_fold_888_, v___x_889_);
v___x_891_ = lean_uint64_xor(v_fold_888_, v___x_890_);
v___x_892_ = lean_uint64_to_usize(v___x_891_);
v___x_893_ = lean_usize_of_nat(v___x_884_);
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_sub(v___x_893_, v___x_894_);
v___x_896_ = lean_usize_land(v___x_892_, v___x_895_);
v___x_897_ = lean_array_uget_borrowed(v_buckets_883_, v___x_896_);
v___x_898_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_881_, v_fallback_882_, v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg___boxed(lean_object* v_m_899_, lean_object* v_a_900_, lean_object* v_fallback_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_899_, v_a_900_, v_fallback_901_);
lean_dec(v_fallback_901_);
lean_dec_ref(v_a_900_);
lean_dec_ref(v_m_899_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2(lean_object* v_filePath_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_lean_x3f_905_; lean_object* v_olean_x3f_906_; lean_object* v_oleanServer_x3f_907_; lean_object* v_oleanPrivate_x3f_908_; lean_object* v_ilean_x3f_909_; lean_object* v_irSig_x3f_910_; lean_object* v_c_x3f_911_; lean_object* v_bc_x3f_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_920_; 
v_lean_x3f_905_ = lean_ctor_get(v_a_904_, 0);
v_olean_x3f_906_ = lean_ctor_get(v_a_904_, 1);
v_oleanServer_x3f_907_ = lean_ctor_get(v_a_904_, 2);
v_oleanPrivate_x3f_908_ = lean_ctor_get(v_a_904_, 3);
v_ilean_x3f_909_ = lean_ctor_get(v_a_904_, 4);
v_irSig_x3f_910_ = lean_ctor_get(v_a_904_, 5);
v_c_x3f_911_ = lean_ctor_get(v_a_904_, 7);
v_bc_x3f_912_ = lean_ctor_get(v_a_904_, 8);
v_isSharedCheck_920_ = !lean_is_exclusive(v_a_904_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v_a_904_, 6);
lean_dec(v_unused_921_);
v___x_914_ = v_a_904_;
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_bc_x3f_912_);
lean_inc(v_c_x3f_911_);
lean_inc(v_irSig_x3f_910_);
lean_inc(v_ilean_x3f_909_);
lean_inc(v_oleanPrivate_x3f_908_);
lean_inc(v_oleanServer_x3f_907_);
lean_inc(v_olean_x3f_906_);
lean_inc(v_lean_x3f_905_);
lean_dec(v_a_904_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v_filePath_903_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 6, v___x_916_);
v___x_918_ = v___x_914_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_lean_x3f_905_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_olean_x3f_906_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_oleanServer_x3f_907_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_oleanPrivate_x3f_908_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_ilean_x3f_909_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v_irSig_x3f_910_);
lean_ctor_set(v_reuseFailAlloc_919_, 6, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_919_, 7, v_c_x3f_911_);
lean_ctor_set(v_reuseFailAlloc_919_, 8, v_bc_x3f_912_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0(lean_object* v_filePath_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_lean_x3f_924_; lean_object* v_oleanServer_x3f_925_; lean_object* v_oleanPrivate_x3f_926_; lean_object* v_ilean_x3f_927_; lean_object* v_irSig_x3f_928_; lean_object* v_ir_x3f_929_; lean_object* v_c_x3f_930_; lean_object* v_bc_x3f_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_939_; 
v_lean_x3f_924_ = lean_ctor_get(v_a_923_, 0);
v_oleanServer_x3f_925_ = lean_ctor_get(v_a_923_, 2);
v_oleanPrivate_x3f_926_ = lean_ctor_get(v_a_923_, 3);
v_ilean_x3f_927_ = lean_ctor_get(v_a_923_, 4);
v_irSig_x3f_928_ = lean_ctor_get(v_a_923_, 5);
v_ir_x3f_929_ = lean_ctor_get(v_a_923_, 6);
v_c_x3f_930_ = lean_ctor_get(v_a_923_, 7);
v_bc_x3f_931_ = lean_ctor_get(v_a_923_, 8);
v_isSharedCheck_939_ = !lean_is_exclusive(v_a_923_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v_a_923_, 1);
lean_dec(v_unused_940_);
v___x_933_ = v_a_923_;
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_bc_x3f_931_);
lean_inc(v_c_x3f_930_);
lean_inc(v_ir_x3f_929_);
lean_inc(v_irSig_x3f_928_);
lean_inc(v_ilean_x3f_927_);
lean_inc(v_oleanPrivate_x3f_926_);
lean_inc(v_oleanServer_x3f_925_);
lean_inc(v_lean_x3f_924_);
lean_dec(v_a_923_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_935_, 0, v_filePath_922_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_lean_x3f_924_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_938_, 2, v_oleanServer_x3f_925_);
lean_ctor_set(v_reuseFailAlloc_938_, 3, v_oleanPrivate_x3f_926_);
lean_ctor_set(v_reuseFailAlloc_938_, 4, v_ilean_x3f_927_);
lean_ctor_set(v_reuseFailAlloc_938_, 5, v_irSig_x3f_928_);
lean_ctor_set(v_reuseFailAlloc_938_, 6, v_ir_x3f_929_);
lean_ctor_set(v_reuseFailAlloc_938_, 7, v_c_x3f_930_);
lean_ctor_set(v_reuseFailAlloc_938_, 8, v_bc_x3f_931_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(lean_object* v_a_941_, lean_object* v_b_942_, lean_object* v_x_943_){
_start:
{
if (lean_obj_tag(v_x_943_) == 0)
{
lean_dec(v_b_942_);
lean_dec_ref(v_a_941_);
return v_x_943_;
}
else
{
lean_object* v_key_944_; lean_object* v_value_945_; lean_object* v_tail_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_958_; 
v_key_944_ = lean_ctor_get(v_x_943_, 0);
v_value_945_ = lean_ctor_get(v_x_943_, 1);
v_tail_946_ = lean_ctor_get(v_x_943_, 2);
v_isSharedCheck_958_ = !lean_is_exclusive(v_x_943_);
if (v_isSharedCheck_958_ == 0)
{
v___x_948_ = v_x_943_;
v_isShared_949_ = v_isSharedCheck_958_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_tail_946_);
lean_inc(v_value_945_);
lean_inc(v_key_944_);
lean_dec(v_x_943_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_958_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
uint8_t v___x_950_; 
v___x_950_ = lean_string_dec_eq(v_key_944_, v_a_941_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_941_, v_b_942_, v_tail_946_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 2, v___x_951_);
v___x_953_ = v___x_948_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_key_944_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_value_945_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
else
{
lean_object* v___x_956_; 
lean_dec(v_value_945_);
lean_dec(v_key_944_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_b_942_);
lean_ctor_set(v___x_948_, 0, v_a_941_);
v___x_956_ = v___x_948_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_941_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_b_942_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_tail_946_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
if (lean_obj_tag(v_x_960_) == 0)
{
return v_x_959_;
}
else
{
lean_object* v_key_961_; lean_object* v_value_962_; lean_object* v_tail_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_986_; 
v_key_961_ = lean_ctor_get(v_x_960_, 0);
v_value_962_ = lean_ctor_get(v_x_960_, 1);
v_tail_963_ = lean_ctor_get(v_x_960_, 2);
v_isSharedCheck_986_ = !lean_is_exclusive(v_x_960_);
if (v_isSharedCheck_986_ == 0)
{
v___x_965_ = v_x_960_;
v_isShared_966_ = v_isSharedCheck_986_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_tail_963_);
lean_inc(v_value_962_);
lean_inc(v_key_961_);
lean_dec(v_x_960_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_986_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; uint64_t v___x_968_; uint64_t v___x_969_; uint64_t v___x_970_; uint64_t v_fold_971_; uint64_t v___x_972_; uint64_t v___x_973_; uint64_t v___x_974_; size_t v___x_975_; size_t v___x_976_; size_t v___x_977_; size_t v___x_978_; size_t v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_967_ = lean_array_get_size(v_x_959_);
v___x_968_ = lean_string_hash(v_key_961_);
v___x_969_ = 32ULL;
v___x_970_ = lean_uint64_shift_right(v___x_968_, v___x_969_);
v_fold_971_ = lean_uint64_xor(v___x_968_, v___x_970_);
v___x_972_ = 16ULL;
v___x_973_ = lean_uint64_shift_right(v_fold_971_, v___x_972_);
v___x_974_ = lean_uint64_xor(v_fold_971_, v___x_973_);
v___x_975_ = lean_uint64_to_usize(v___x_974_);
v___x_976_ = lean_usize_of_nat(v___x_967_);
v___x_977_ = ((size_t)1ULL);
v___x_978_ = lean_usize_sub(v___x_976_, v___x_977_);
v___x_979_ = lean_usize_land(v___x_975_, v___x_978_);
v___x_980_ = lean_array_uget_borrowed(v_x_959_, v___x_979_);
lean_inc(v___x_980_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 2, v___x_980_);
v___x_982_ = v___x_965_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_key_961_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_value_962_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v___x_980_);
v___x_982_ = v_reuseFailAlloc_985_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; 
v___x_983_ = lean_array_uset(v_x_959_, v___x_979_, v___x_982_);
v_x_959_ = v___x_983_;
v_x_960_ = v_tail_963_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(lean_object* v_i_987_, lean_object* v_source_988_, lean_object* v_target_989_){
_start:
{
lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = lean_array_get_size(v_source_988_);
v___x_991_ = lean_nat_dec_lt(v_i_987_, v___x_990_);
if (v___x_991_ == 0)
{
lean_dec_ref(v_source_988_);
lean_dec(v_i_987_);
return v_target_989_;
}
else
{
lean_object* v_es_992_; lean_object* v___x_993_; lean_object* v_source_994_; lean_object* v_target_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_es_992_ = lean_array_fget(v_source_988_, v_i_987_);
v___x_993_ = lean_box(0);
v_source_994_ = lean_array_fset(v_source_988_, v_i_987_, v___x_993_);
v_target_995_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_target_989_, v_es_992_);
v___x_996_ = lean_unsigned_to_nat(1u);
v___x_997_ = lean_nat_add(v_i_987_, v___x_996_);
lean_dec(v_i_987_);
v_i_987_ = v___x_997_;
v_source_988_ = v_source_994_;
v_target_989_ = v_target_995_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(lean_object* v_data_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_nbuckets_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1000_ = lean_array_get_size(v_data_999_);
v___x_1001_ = lean_unsigned_to_nat(2u);
v_nbuckets_1002_ = lean_nat_mul(v___x_1000_, v___x_1001_);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_mk_array(v_nbuckets_1002_, v___x_1004_);
v___x_1006_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v___x_1003_, v_data_999_, v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object* v_m_1007_, lean_object* v_a_1008_, lean_object* v_b_1009_){
_start:
{
lean_object* v_size_1010_; lean_object* v_buckets_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1054_; 
v_size_1010_ = lean_ctor_get(v_m_1007_, 0);
v_buckets_1011_ = lean_ctor_get(v_m_1007_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_m_1007_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1013_ = v_m_1007_;
v_isShared_1014_ = v_isSharedCheck_1054_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_buckets_1011_);
lean_inc(v_size_1010_);
lean_dec(v_m_1007_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1054_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; uint64_t v___x_1016_; uint64_t v___x_1017_; uint64_t v___x_1018_; uint64_t v_fold_1019_; uint64_t v___x_1020_; uint64_t v___x_1021_; uint64_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; size_t v___x_1025_; size_t v___x_1026_; size_t v___x_1027_; lean_object* v_bkt_1028_; uint8_t v___x_1029_; 
v___x_1015_ = lean_array_get_size(v_buckets_1011_);
v___x_1016_ = lean_string_hash(v_a_1008_);
v___x_1017_ = 32ULL;
v___x_1018_ = lean_uint64_shift_right(v___x_1016_, v___x_1017_);
v_fold_1019_ = lean_uint64_xor(v___x_1016_, v___x_1018_);
v___x_1020_ = 16ULL;
v___x_1021_ = lean_uint64_shift_right(v_fold_1019_, v___x_1020_);
v___x_1022_ = lean_uint64_xor(v_fold_1019_, v___x_1021_);
v___x_1023_ = lean_uint64_to_usize(v___x_1022_);
v___x_1024_ = lean_usize_of_nat(v___x_1015_);
v___x_1025_ = ((size_t)1ULL);
v___x_1026_ = lean_usize_sub(v___x_1024_, v___x_1025_);
v___x_1027_ = lean_usize_land(v___x_1023_, v___x_1026_);
v_bkt_1028_ = lean_array_uget_borrowed(v_buckets_1011_, v___x_1027_);
v___x_1029_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1008_, v_bkt_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; lean_object* v_size_x27_1031_; lean_object* v___x_1032_; lean_object* v_buckets_x27_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1030_ = lean_unsigned_to_nat(1u);
v_size_x27_1031_ = lean_nat_add(v_size_1010_, v___x_1030_);
lean_dec(v_size_1010_);
lean_inc(v_bkt_1028_);
v___x_1032_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1032_, 0, v_a_1008_);
lean_ctor_set(v___x_1032_, 1, v_b_1009_);
lean_ctor_set(v___x_1032_, 2, v_bkt_1028_);
v_buckets_x27_1033_ = lean_array_uset(v_buckets_1011_, v___x_1027_, v___x_1032_);
v___x_1034_ = lean_unsigned_to_nat(4u);
v___x_1035_ = lean_nat_mul(v_size_x27_1031_, v___x_1034_);
v___x_1036_ = lean_unsigned_to_nat(3u);
v___x_1037_ = lean_nat_div(v___x_1035_, v___x_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_array_get_size(v_buckets_x27_1033_);
v___x_1039_ = lean_nat_dec_le(v___x_1037_, v___x_1038_);
lean_dec(v___x_1037_);
if (v___x_1039_ == 0)
{
lean_object* v_val_1040_; lean_object* v___x_1042_; 
v_val_1040_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_buckets_x27_1033_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v_val_1040_);
lean_ctor_set(v___x_1013_, 0, v_size_x27_1031_);
v___x_1042_ = v___x_1013_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_size_x27_1031_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_val_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
else
{
lean_object* v___x_1045_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v_buckets_x27_1033_);
lean_ctor_set(v___x_1013_, 0, v_size_x27_1031_);
v___x_1045_ = v___x_1013_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_size_x27_1031_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_buckets_x27_1033_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
else
{
lean_object* v___x_1047_; lean_object* v_buckets_x27_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
lean_inc(v_bkt_1028_);
v___x_1047_ = lean_box(0);
v_buckets_x27_1048_ = lean_array_uset(v_buckets_1011_, v___x_1027_, v___x_1047_);
v___x_1049_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1008_, v_b_1009_, v_bkt_1028_);
v___x_1050_ = lean_array_uset(v_buckets_x27_1048_, v___x_1027_, v___x_1049_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 1, v___x_1050_);
v___x_1052_ = v___x_1013_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_size_1010_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object* v_as_1063_, size_t v_sz_1064_, size_t v_i_1065_, lean_object* v_b_1066_){
_start:
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_usize_dec_lt(v_i_1065_, v_sz_1064_);
if (v___x_1067_ == 0)
{
return v_b_1066_;
}
else
{
lean_object* v_fst_1068_; lean_object* v_snd_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1119_; 
v_fst_1068_ = lean_ctor_get(v_b_1066_, 0);
v_snd_1069_ = lean_ctor_get(v_b_1066_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_b_1066_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1071_ = v_b_1066_;
v_isShared_1072_ = v_isSharedCheck_1119_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_snd_1069_);
lean_inc(v_fst_1068_);
lean_dec(v_b_1066_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1119_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v_order_1076_; lean_object* v_fst_1088_; lean_object* v_snd_1089_; lean_object* v_a_1092_; lean_object* v_filePath_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; 
v_a_1092_ = lean_array_uget_borrowed(v_as_1063_, v_i_1065_);
v_filePath_1093_ = lean_ctor_get(v_a_1092_, 0);
lean_inc_ref_n(v_filePath_1093_, 2);
v___f_1094_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1094_, 0, v_filePath_1093_);
v___x_1095_ = l_System_FilePath_extension(v_filePath_1093_);
if (lean_obj_tag(v___x_1095_) == 1)
{
lean_object* v_val_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v_val_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_val_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1));
v___x_1098_ = lean_string_dec_eq(v_val_1096_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2));
v___x_1100_ = lean_string_dec_eq(v_val_1096_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3));
v___x_1102_ = lean_string_dec_eq(v_val_1096_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4));
v___x_1104_ = lean_string_dec_eq(v_val_1096_, v___x_1103_);
lean_dec(v_val_1096_);
if (v___x_1104_ == 0)
{
lean_inc_ref(v_filePath_1093_);
v_fst_1088_ = v_filePath_1093_;
v_snd_1089_ = v___f_1094_;
goto v___jp_1087_;
}
else
{
lean_object* v___f_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
lean_dec_ref(v___f_1094_);
lean_inc_ref_n(v_filePath_1093_, 2);
v___f_1105_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1), 2, 1);
lean_closure_set(v___f_1105_, 0, v_filePath_1093_);
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1107_ = l_System_FilePath_withExtension(v_filePath_1093_, v___x_1106_);
v___x_1108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1109_ = l_System_FilePath_withExtension(v___x_1107_, v___x_1108_);
v_fst_1088_ = v___x_1109_;
v_snd_1089_ = v___f_1105_;
goto v___jp_1087_;
}
}
else
{
lean_object* v___f_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v_val_1096_);
lean_dec_ref(v___f_1094_);
lean_inc_ref_n(v_filePath_1093_, 2);
v___f_1110_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2), 2, 1);
lean_closure_set(v___f_1110_, 0, v_filePath_1093_);
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1112_ = l_System_FilePath_withExtension(v_filePath_1093_, v___x_1111_);
v_fst_1088_ = v___x_1112_;
v_snd_1089_ = v___f_1110_;
goto v___jp_1087_;
}
}
else
{
lean_object* v___f_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec(v_val_1096_);
lean_dec_ref(v___f_1094_);
lean_inc_ref_n(v_filePath_1093_, 2);
v___f_1113_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3), 2, 1);
lean_closure_set(v___f_1113_, 0, v_filePath_1093_);
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1115_ = l_System_FilePath_withExtension(v_filePath_1093_, v___x_1114_);
v_fst_1088_ = v___x_1115_;
v_snd_1089_ = v___f_1113_;
goto v___jp_1087_;
}
}
else
{
lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec(v_val_1096_);
lean_dec_ref(v___f_1094_);
lean_inc_ref_n(v_filePath_1093_, 2);
v___f_1116_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4), 2, 1);
lean_closure_set(v___f_1116_, 0, v_filePath_1093_);
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1118_ = l_System_FilePath_withExtension(v_filePath_1093_, v___x_1117_);
v_fst_1088_ = v___x_1118_;
v_snd_1089_ = v___f_1116_;
goto v___jp_1087_;
}
}
else
{
lean_dec(v___x_1095_);
lean_inc_ref(v_filePath_1093_);
v_fst_1088_ = v_filePath_1093_;
v_snd_1089_ = v___f_1094_;
goto v___jp_1087_;
}
v___jp_1073_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0));
v___x_1078_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_snd_1069_, v___y_1075_, v___x_1077_);
v___x_1079_ = lean_apply_1(v___y_1074_, v___x_1078_);
v___x_1080_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_snd_1069_, v___y_1075_, v___x_1079_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v___x_1080_);
lean_ctor_set(v___x_1071_, 0, v_order_1076_);
v___x_1082_ = v___x_1071_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_order_1076_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
size_t v___x_1083_; size_t v___x_1084_; 
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_i_1065_, v___x_1083_);
v_i_1065_ = v___x_1084_;
v_b_1066_ = v___x_1082_;
goto _start;
}
}
v___jp_1087_:
{
uint8_t v___x_1090_; 
v___x_1090_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1069_, v_fst_1088_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; 
lean_inc_ref(v_fst_1088_);
v___x_1091_ = lean_array_push(v_fst_1068_, v_fst_1088_);
v___y_1074_ = v_snd_1089_;
v___y_1075_ = v_fst_1088_;
v_order_1076_ = v___x_1091_;
goto v___jp_1073_;
}
else
{
v___y_1074_ = v_snd_1089_;
v___y_1075_ = v_fst_1088_;
v_order_1076_ = v_fst_1068_;
goto v___jp_1073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object* v_as_1120_, lean_object* v_sz_1121_, lean_object* v_i_1122_, lean_object* v_b_1123_){
_start:
{
size_t v_sz_boxed_1124_; size_t v_i_boxed_1125_; lean_object* v_res_1126_; 
v_sz_boxed_1124_ = lean_unbox_usize(v_sz_1121_);
lean_dec(v_sz_1121_);
v_i_boxed_1125_ = lean_unbox_usize(v_i_1122_);
lean_dec(v_i_1122_);
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_as_1120_, v_sz_boxed_1124_, v_i_boxed_1125_, v_b_1123_);
lean_dec_ref(v_as_1120_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(lean_object* v_msg_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1129_ = lean_panic_fn_borrowed(v___x_1128_, v_msg_1127_);
return v___x_1129_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1133_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2));
v___x_1134_ = lean_unsigned_to_nat(11u);
v___x_1135_ = lean_unsigned_to_nat(163u);
v___x_1136_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1));
v___x_1137_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0));
v___x_1138_ = l_mkPanicMessageWithDecl(v___x_1137_, v___x_1136_, v___x_1135_, v___x_1134_, v___x_1133_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(lean_object* v_a_1139_, lean_object* v_x_1140_){
_start:
{
if (lean_obj_tag(v_x_1140_) == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3);
v___x_1142_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(v___x_1141_);
return v___x_1142_;
}
else
{
lean_object* v_key_1143_; lean_object* v_value_1144_; lean_object* v_tail_1145_; uint8_t v___x_1146_; 
v_key_1143_ = lean_ctor_get(v_x_1140_, 0);
v_value_1144_ = lean_ctor_get(v_x_1140_, 1);
v_tail_1145_ = lean_ctor_get(v_x_1140_, 2);
v___x_1146_ = lean_string_dec_eq(v_key_1143_, v_a_1139_);
if (v___x_1146_ == 0)
{
v_x_1140_ = v_tail_1145_;
goto _start;
}
else
{
lean_inc(v_value_1144_);
return v_value_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___boxed(lean_object* v_a_1148_, lean_object* v_x_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1148_, v_x_1149_);
lean_dec(v_x_1149_);
lean_dec_ref(v_a_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object* v_m_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_buckets_1153_; lean_object* v___x_1154_; uint64_t v___x_1155_; uint64_t v___x_1156_; uint64_t v___x_1157_; uint64_t v_fold_1158_; uint64_t v___x_1159_; uint64_t v___x_1160_; uint64_t v___x_1161_; size_t v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; size_t v___x_1165_; size_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_buckets_1153_ = lean_ctor_get(v_m_1151_, 1);
v___x_1154_ = lean_array_get_size(v_buckets_1153_);
v___x_1155_ = lean_string_hash(v_a_1152_);
v___x_1156_ = 32ULL;
v___x_1157_ = lean_uint64_shift_right(v___x_1155_, v___x_1156_);
v_fold_1158_ = lean_uint64_xor(v___x_1155_, v___x_1157_);
v___x_1159_ = 16ULL;
v___x_1160_ = lean_uint64_shift_right(v_fold_1158_, v___x_1159_);
v___x_1161_ = lean_uint64_xor(v_fold_1158_, v___x_1160_);
v___x_1162_ = lean_uint64_to_usize(v___x_1161_);
v___x_1163_ = lean_usize_of_nat(v___x_1154_);
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_sub(v___x_1163_, v___x_1164_);
v___x_1166_ = lean_usize_land(v___x_1162_, v___x_1165_);
v___x_1167_ = lean_array_uget_borrowed(v_buckets_1153_, v___x_1166_);
v___x_1168_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1152_, v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object* v_m_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v_m_1169_, v_a_1170_);
lean_dec_ref(v_a_1170_);
lean_dec_ref(v_m_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object* v___x_1172_, size_t v_sz_1173_, size_t v_i_1174_, lean_object* v_bs_1175_){
_start:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_lt(v_i_1174_, v_sz_1173_);
if (v___x_1176_ == 0)
{
return v_bs_1175_;
}
else
{
lean_object* v_v_1177_; lean_object* v___x_1178_; lean_object* v_bs_x27_1179_; lean_object* v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; lean_object* v___x_1183_; 
v_v_1177_ = lean_array_uget(v_bs_1175_, v_i_1174_);
v___x_1178_ = lean_unsigned_to_nat(0u);
v_bs_x27_1179_ = lean_array_uset(v_bs_1175_, v_i_1174_, v___x_1178_);
v___x_1180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v___x_1172_, v_v_1177_);
lean_dec(v_v_1177_);
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_add(v_i_1174_, v___x_1181_);
v___x_1183_ = lean_array_uset(v_bs_x27_1179_, v_i_1174_, v___x_1180_);
v_i_1174_ = v___x_1182_;
v_bs_1175_ = v___x_1183_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object* v___x_1185_, lean_object* v_sz_1186_, lean_object* v_i_1187_, lean_object* v_bs_1188_){
_start:
{
size_t v_sz_boxed_1189_; size_t v_i_boxed_1190_; lean_object* v_res_1191_; 
v_sz_boxed_1189_ = lean_unbox_usize(v_sz_1186_);
lean_dec(v_sz_1186_);
v_i_boxed_1190_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v___x_1185_, v_sz_boxed_1189_, v_i_boxed_1190_, v_bs_1188_);
lean_dec_ref(v___x_1185_);
return v_res_1191_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_unsigned_to_nat(16u);
v___x_1196_ = lean_mk_array(v___x_1195_, v___x_1194_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v_byBase_1199_; 
v___x_1197_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1);
v___x_1198_ = lean_unsigned_to_nat(0u);
v_byBase_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byBase_1199_, 0, v___x_1198_);
lean_ctor_set(v_byBase_1199_, 1, v___x_1197_);
return v_byBase_1199_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3(void){
_start:
{
lean_object* v_byBase_1200_; lean_object* v_order_1201_; lean_object* v___x_1202_; 
v_byBase_1200_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2);
v_order_1201_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0));
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_order_1201_);
lean_ctor_set(v___x_1202_, 1, v_byBase_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object* v_regions_1203_){
_start:
{
lean_object* v___x_1204_; size_t v_sz_1205_; size_t v___x_1206_; lean_object* v___x_1207_; lean_object* v_fst_1208_; lean_object* v_snd_1209_; size_t v_sz_1210_; lean_object* v___x_1211_; 
v___x_1204_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3);
v_sz_1205_ = lean_array_size(v_regions_1203_);
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_regions_1203_, v_sz_1205_, v___x_1206_, v___x_1204_);
v_fst_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_fst_1208_);
v_snd_1209_ = lean_ctor_get(v___x_1207_, 1);
lean_inc(v_snd_1209_);
lean_dec_ref(v___x_1207_);
v_sz_1210_ = lean_array_size(v_fst_1208_);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v_snd_1209_, v_sz_1210_, v___x_1206_, v_fst_1208_);
lean_dec(v_snd_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object* v_regions_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1212_);
lean_dec_ref(v_regions_1212_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object* v_00_u03b2_1214_, lean_object* v_m_1215_, lean_object* v_a_1216_, lean_object* v_fallback_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_1215_, v_a_1216_, v_fallback_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object* v_00_u03b2_1219_, lean_object* v_m_1220_, lean_object* v_a_1221_, lean_object* v_fallback_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(v_00_u03b2_1219_, v_m_1220_, v_a_1221_, v_fallback_1222_);
lean_dec(v_fallback_1222_);
lean_dec_ref(v_a_1221_);
lean_dec_ref(v_m_1220_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object* v_00_u03b2_1224_, lean_object* v_m_1225_, lean_object* v_a_1226_, lean_object* v_b_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_1225_, v_a_1226_, v_b_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object* v_00_u03b2_1229_, lean_object* v_m_1230_, lean_object* v_a_1231_){
_start:
{
uint8_t v___x_1232_; 
v___x_1232_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_1230_, v_a_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object* v_00_u03b2_1233_, lean_object* v_m_1234_, lean_object* v_a_1235_){
_start:
{
uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(v_00_u03b2_1233_, v_m_1234_, v_a_1235_);
lean_dec_ref(v_a_1235_);
lean_dec_ref(v_m_1234_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object* v_00_u03b2_1238_, lean_object* v_a_1239_, lean_object* v_fallback_1240_, lean_object* v_x_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_1239_, v_fallback_1240_, v_x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1243_, lean_object* v_a_1244_, lean_object* v_fallback_1245_, lean_object* v_x_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(v_00_u03b2_1243_, v_a_1244_, v_fallback_1245_, v_x_1246_);
lean_dec(v_x_1246_);
lean_dec(v_fallback_1245_);
lean_dec_ref(v_a_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object* v_00_u03b2_1248_, lean_object* v_a_1249_, lean_object* v_x_1250_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1249_, v_x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1252_, lean_object* v_a_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v_res_1255_; lean_object* v_r_1256_; 
v_res_1255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(v_00_u03b2_1252_, v_a_1253_, v_x_1254_);
lean_dec(v_x_1254_);
lean_dec_ref(v_a_1253_);
v_r_1256_ = lean_box(v_res_1255_);
return v_r_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3(lean_object* v_00_u03b2_1257_, lean_object* v_data_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_data_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4(lean_object* v_00_u03b2_1260_, lean_object* v_a_1261_, lean_object* v_b_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1261_, v_b_1262_, v_x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1265_, lean_object* v_i_1266_, lean_object* v_source_1267_, lean_object* v_target_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v_i_1266_, v_source_1267_, v_target_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_x_1271_, v_x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(lean_object* v_as_1274_, size_t v_sz_1275_, size_t v_i_1276_, lean_object* v_b_1277_){
_start:
{
uint8_t v___x_1279_; 
v___x_1279_ = lean_usize_dec_lt(v_i_1276_, v_sz_1275_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v_b_1277_);
return v___x_1280_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1282_; 
v_a_1281_ = lean_array_uget_borrowed(v_as_1274_, v_i_1276_);
v___x_1282_ = lean_compacted_region_read(v_a_1281_, v_b_1277_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v_snd_1284_; lean_object* v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v_snd_1284_ = lean_ctor_get(v_a_1283_, 1);
lean_inc(v_snd_1284_);
lean_dec(v_a_1283_);
v___x_1285_ = lean_array_push(v_b_1277_, v_snd_1284_);
v___x_1286_ = ((size_t)1ULL);
v___x_1287_ = lean_usize_add(v_i_1276_, v___x_1286_);
v_i_1276_ = v___x_1287_;
v_b_1277_ = v___x_1285_;
goto _start;
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v_b_1277_);
v_a_1289_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1282_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1282_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0___boxed(lean_object* v_as_1297_, lean_object* v_sz_1298_, lean_object* v_i_1299_, lean_object* v_b_1300_, lean_object* v___y_1301_){
_start:
{
size_t v_sz_boxed_1302_; size_t v_i_boxed_1303_; lean_object* v_res_1304_; 
v_sz_boxed_1302_ = lean_unbox_usize(v_sz_1298_);
lean_dec(v_sz_1298_);
v_i_boxed_1303_ = lean_unbox_usize(v_i_1299_);
lean_dec(v_i_1299_);
v_res_1304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v_as_1297_, v_sz_boxed_1302_, v_i_boxed_1303_, v_b_1300_);
lean_dec_ref(v_as_1297_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(lean_object* v_arts_1307_){
_start:
{
lean_object* v_oleanRegions_1309_; lean_object* v___x_1310_; size_t v_sz_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v_oleanRegions_1309_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc_ref(v_arts_1307_);
v___x_1310_ = l_Lean_ModuleArtifacts_oleanParts(v_arts_1307_);
v_sz_1311_ = lean_array_size(v___x_1310_);
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1310_, v_sz_1311_, v___x_1312_, v_oleanRegions_1309_);
lean_dec_ref(v___x_1310_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1315_; size_t v_sz_1316_; lean_object* v___x_1317_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1313_, 1);
v___x_1315_ = l_Lean_ModuleArtifacts_irParts(v_arts_1307_);
v_sz_1316_ = lean_array_size(v___x_1315_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1315_, v_sz_1316_, v___x_1312_, v_oleanRegions_1309_);
lean_dec_ref(v___x_1315_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1326_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = l_Array_append___redArg(v_a_1314_, v_a_1318_);
lean_dec(v_a_1318_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1322_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
else
{
lean_dec(v_a_1314_);
return v___x_1317_;
}
}
else
{
lean_dec_ref(v_arts_1307_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___boxed(lean_object* v_arts_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v_arts_1327_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(lean_object* v_e_1330_){
_start:
{
if (lean_obj_tag(v_e_1330_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1341_; 
v_a_1332_ = lean_ctor_get(v_e_1330_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_e_1330_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1334_ = v_e_1330_;
v_isShared_1335_ = v_isSharedCheck_1341_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v_e_1330_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1341_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1336_ = lean_io_error_to_string(v_a_1332_);
v___x_1337_ = lean_mk_io_user_error(v___x_1336_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set_tag(v___x_1334_, 1);
lean_ctor_set(v___x_1334_, 0, v___x_1337_);
v___x_1339_ = v___x_1334_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
v_a_1342_ = lean_ctor_get(v_e_1330_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_e_1330_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v_e_1330_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v_e_1330_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 0);
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg___boxed(lean_object* v_e_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_object* v_00_u03b1_1353_, lean_object* v_e_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___boxed(lean_object* v_00_u03b1_1357_, lean_object* v_e_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(v_00_u03b1_1357_, v_e_1358_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object* v_a_1361_, lean_object* v___y_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_fst_1365_; lean_object* v_snd_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1394_; 
v_fst_1365_ = lean_ctor_get(v_a_1363_, 0);
v_snd_1366_ = lean_ctor_get(v_a_1363_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_a_1363_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1368_ = v_a_1363_;
v_isShared_1369_ = v_isSharedCheck_1394_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_snd_1366_);
lean_inc(v_fst_1365_);
lean_dec(v_a_1363_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1394_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = lean_array_get_size(v_a_1361_);
v___x_1371_ = lean_nat_dec_lt(v_snd_1366_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1373_; 
if (v_isShared_1369_ == 0)
{
v___x_1373_ = v___x_1368_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_fst_1365_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_snd_1366_);
v___x_1373_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1377_ = lean_array_get_borrowed(v___x_1376_, v_a_1361_, v_snd_1366_);
lean_inc(v___x_1377_);
v___x_1378_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v___x_1377_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = l_Array_append___redArg(v_fst_1365_, v_a_1379_);
lean_dec(v_a_1379_);
v___x_1381_ = lean_nat_add(v_snd_1366_, v___y_1362_);
lean_dec(v_snd_1366_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 1, v___x_1381_);
lean_ctor_set(v___x_1368_, 0, v___x_1380_);
v___x_1383_ = v___x_1368_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
v_a_1363_ = v___x_1383_;
goto _start;
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_del_object(v___x_1368_);
lean_dec(v_snd_1366_);
lean_dec(v_fst_1365_);
v_a_1386_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1378_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1378_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object* v_a_1395_, lean_object* v___y_1396_, lean_object* v_a_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1395_, v___y_1396_, v_a_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v_a_1395_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(lean_object* v_a_1400_, lean_object* v___y_1401_, lean_object* v___x_1402_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1400_, v___y_1401_, v___x_1402_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1413_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v_fst_1409_; lean_object* v___x_1411_; 
v_fst_1409_ = lean_ctor_get(v_a_1405_, 0);
lean_inc(v_fst_1409_);
lean_dec(v_a_1405_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 1);
lean_ctor_set(v___x_1407_, 0, v_fst_1409_);
v___x_1411_ = v___x_1407_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_fst_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_a_1414_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1404_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1404_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 0);
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed(lean_object* v_a_1422_, lean_object* v___y_1423_, lean_object* v___x_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(v_a_1422_, v___y_1423_, v___x_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v_a_1422_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(lean_object* v_upperBound_1427_, lean_object* v_a_1428_, lean_object* v___y_1429_, lean_object* v_a_1430_, lean_object* v_b_1431_){
_start:
{
uint8_t v___x_1433_; 
v___x_1433_ = lean_nat_dec_lt(v_a_1430_, v_upperBound_1427_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
lean_dec(v_a_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v_a_1428_);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v_b_1431_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc(v_a_1430_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
lean_ctor_set(v___x_1437_, 1, v_a_1430_);
lean_inc(v___y_1429_);
lean_inc_ref(v_a_1428_);
v___f_1438_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1438_, 0, v_a_1428_);
lean_closure_set(v___f_1438_, 1, v___y_1429_);
lean_closure_set(v___f_1438_, 2, v___x_1437_);
v___x_1439_ = lean_io_as_task(v___f_1438_, v___x_1435_);
v___x_1440_ = lean_array_push(v_b_1431_, v___x_1439_);
v___x_1441_ = lean_unsigned_to_nat(1u);
v___x_1442_ = lean_nat_add(v_a_1430_, v___x_1441_);
lean_dec(v_a_1430_);
v_a_1430_ = v___x_1442_;
v_b_1431_ = v___x_1440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___boxed(lean_object* v_upperBound_1444_, lean_object* v_a_1445_, lean_object* v___y_1446_, lean_object* v_a_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1444_, v_a_1445_, v___y_1446_, v_a_1447_, v_b_1448_);
lean_dec(v_upperBound_1444_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(lean_object* v_as_1451_, size_t v_sz_1452_, size_t v_i_1453_, lean_object* v_b_1454_){
_start:
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_usize_dec_lt(v_i_1453_, v_sz_1452_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_b_1454_);
return v___x_1457_;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_a_1458_ = lean_array_uget_borrowed(v_as_1451_, v_i_1453_);
lean_inc(v_a_1458_);
v___x_1459_ = lean_task_get_own(v_a_1458_);
v___x_1460_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v___x_1459_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; size_t v___x_1463_; size_t v___x_1464_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = l_Array_append___redArg(v_b_1454_, v_a_1461_);
lean_dec(v_a_1461_);
v___x_1463_ = ((size_t)1ULL);
v___x_1464_ = lean_usize_add(v_i_1453_, v___x_1463_);
v_i_1453_ = v___x_1464_;
v_b_1454_ = v___x_1462_;
goto _start;
}
else
{
lean_dec_ref(v_b_1454_);
return v___x_1460_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2___boxed(lean_object* v_as_1466_, lean_object* v_sz_1467_, lean_object* v_i_1468_, lean_object* v_b_1469_, lean_object* v___y_1470_){
_start:
{
size_t v_sz_boxed_1471_; size_t v_i_boxed_1472_; lean_object* v_res_1473_; 
v_sz_boxed_1471_ = lean_unbox_usize(v_sz_1467_);
lean_dec(v_sz_1467_);
v_i_boxed_1472_ = lean_unbox_usize(v_i_1468_);
lean_dec(v_i_1468_);
v_res_1473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_as_1466_, v_sz_boxed_1471_, v_i_boxed_1472_, v_b_1469_);
lean_dec_ref(v_as_1466_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t v_sz_1474_, size_t v_i_1475_, lean_object* v_bs_1476_){
_start:
{
uint8_t v___x_1477_; 
v___x_1477_ = lean_usize_dec_lt(v_i_1475_, v_sz_1474_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1478_, 0, v_bs_1476_);
return v___x_1478_;
}
else
{
lean_object* v_v_1479_; lean_object* v___x_1480_; 
v_v_1479_ = lean_array_uget_borrowed(v_bs_1476_, v_i_1475_);
lean_inc(v_v_1479_);
v___x_1480_ = l_Lean_instFromJsonModuleArtifacts_fromJson(v_v_1479_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v_bs_1476_);
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1490_; lean_object* v_bs_x27_1491_; size_t v___x_1492_; size_t v___x_1493_; lean_object* v___x_1494_; 
v_a_1489_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1480_, 1);
v___x_1490_ = lean_unsigned_to_nat(0u);
v_bs_x27_1491_ = lean_array_uset(v_bs_1476_, v_i_1475_, v___x_1490_);
v___x_1492_ = ((size_t)1ULL);
v___x_1493_ = lean_usize_add(v_i_1475_, v___x_1492_);
v___x_1494_ = lean_array_uset(v_bs_x27_1491_, v_i_1475_, v_a_1489_);
v_i_1475_ = v___x_1493_;
v_bs_1476_ = v___x_1494_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object* v_sz_1496_, lean_object* v_i_1497_, lean_object* v_bs_1498_){
_start:
{
size_t v_sz_boxed_1499_; size_t v_i_boxed_1500_; lean_object* v_res_1501_; 
v_sz_boxed_1499_ = lean_unbox_usize(v_sz_1496_);
lean_dec(v_sz_1496_);
v_i_boxed_1500_ = lean_unbox_usize(v_i_1497_);
lean_dec(v_i_1497_);
v_res_1501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_boxed_1499_, v_i_boxed_1500_, v_bs_1498_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object* v_x_1504_){
_start:
{
if (lean_obj_tag(v_x_1504_) == 4)
{
lean_object* v_elems_1505_; size_t v_sz_1506_; size_t v___x_1507_; lean_object* v___x_1508_; 
v_elems_1505_ = lean_ctor_get(v_x_1504_, 0);
lean_inc_ref(v_elems_1505_);
lean_dec_ref_known(v_x_1504_, 1);
v_sz_1506_ = lean_array_size(v_elems_1505_);
v___x_1507_ = ((size_t)0ULL);
v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_1506_, v___x_1507_, v_elems_1505_);
return v___x_1508_;
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1509_ = ((lean_object*)(l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0));
v___x_1510_ = lean_unsigned_to_nat(80u);
v___x_1511_ = l_Lean_Json_pretty(v_x_1504_, v___x_1510_);
v___x_1512_ = lean_string_append(v___x_1509_, v___x_1511_);
lean_dec_ref(v___x_1511_);
v___x_1513_ = ((lean_object*)(l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1));
v___x_1514_ = lean_string_append(v___x_1512_, v___x_1513_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
}
}
static uint32_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3(void){
_start:
{
lean_object* v___x_1519_; uint32_t v___x_1520_; 
v___x_1519_ = lean_box(0);
v___x_1520_ = lean_internal_get_hardware_concurrency(v___x_1519_);
return v___x_1520_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4(void){
_start:
{
uint32_t v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_uint32_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3);
v___x_1522_ = lean_uint32_to_nat(v___x_1521_);
return v___x_1522_;
}
}
static uint8_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1524_ = lean_unsigned_to_nat(4u);
v___x_1525_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1526_ = lean_nat_dec_le(v___x_1525_, v___x_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(lean_object* v_fname_1527_){
_start:
{
lean_object* v___x_1529_; lean_object* v_depsFile_1530_; lean_object* v___x_1531_; 
v___x_1529_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
lean_inc_ref(v_fname_1527_);
v_depsFile_1530_ = l_System_FilePath_addExtension(v_fname_1527_, v___x_1529_);
v___x_1531_ = l_IO_FS_readFile(v_depsFile_1530_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1618_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1534_ = v___x_1531_;
v_isShared_1535_ = v_isSharedCheck_1618_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1531_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1618_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v_a_1537_; lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_Json_parse(v_a_1532_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; 
lean_dec_ref(v_fname_1527_);
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v_a_1537_ = v_a_1548_;
goto v___jp_1536_;
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1550_; 
v_a_1549_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1547_, 1);
v___x_1550_ = l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(v_a_1549_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; 
lean_dec_ref(v_fname_1527_);
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v_a_1537_ = v_a_1551_;
goto v___jp_1536_;
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___y_1556_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1607_; uint8_t v___x_1617_; 
lean_del_object(v___x_1534_);
lean_dec_ref(v_depsFile_1530_);
v_a_1552_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1553_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1554_ = lean_unsigned_to_nat(4u);
v___x_1617_ = lean_uint8_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6);
if (v___x_1617_ == 0)
{
v___y_1607_ = v___x_1554_;
goto v___jp_1606_;
}
else
{
v___y_1607_ = v___x_1553_;
goto v___jp_1606_;
}
v___jp_1555_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_mk_empty_array_with_capacity(v___y_1556_);
v___x_1558_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_1552_);
lean_inc(v___y_1556_);
v___x_1559_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v___y_1556_, v_a_1552_, v___y_1556_, v___x_1558_, v___x_1557_);
lean_dec(v___y_1556_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; size_t v_sz_1564_; size_t v___x_1565_; lean_object* v___x_1566_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1559_, 1);
v___x_1561_ = lean_array_get_size(v_a_1552_);
lean_dec(v_a_1552_);
v___x_1562_ = lean_nat_mul(v___x_1561_, v___x_1554_);
v___x_1563_ = lean_mk_empty_array_with_capacity(v___x_1562_);
lean_dec(v___x_1562_);
v_sz_1564_ = lean_array_size(v_a_1560_);
v___x_1565_ = ((size_t)0ULL);
v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_a_1560_, v_sz_1564_, v___x_1565_, v___x_1563_);
lean_dec(v_a_1560_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v___x_1568_ = lean_compacted_region_read(v_fname_1527_, v_a_1567_);
lean_dec(v_a_1567_);
lean_dec_ref(v_fname_1527_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1577_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1577_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v_fst_1573_; lean_object* v___x_1575_; 
v_fst_1573_ = lean_ctor_get(v_a_1569_, 0);
lean_inc(v_fst_1573_);
lean_dec(v_a_1569_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v_fst_1573_);
v___x_1575_ = v___x_1571_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_fst_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
v_a_1578_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1568_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1568_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v_fname_1527_);
v_a_1586_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1566_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1566_);
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
lean_dec(v_a_1552_);
lean_dec_ref(v_fname_1527_);
v_a_1594_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1559_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1559_);
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
v___jp_1602_:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_nat_dec_le(v___y_1603_, v___y_1604_);
if (v___x_1605_ == 0)
{
lean_dec(v___y_1604_);
v___y_1556_ = v___y_1603_;
goto v___jp_1555_;
}
else
{
lean_dec(v___y_1603_);
v___y_1556_ = v___y_1604_;
goto v___jp_1555_;
}
}
v___jp_1606_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1608_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5));
v___x_1609_ = lean_io_getenv(v___x_1608_);
v___x_1610_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v___x_1609_) == 0)
{
v___y_1603_ = v___x_1610_;
v___y_1604_ = v___y_1607_;
goto v___jp_1602_;
}
else
{
lean_object* v_val_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v_val_1611_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_val_1611_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = lean_string_utf8_byte_size(v_val_1611_);
v___x_1614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1614_, 0, v_val_1611_);
lean_ctor_set(v___x_1614_, 1, v___x_1612_);
lean_ctor_set(v___x_1614_, 2, v___x_1613_);
v___x_1615_ = l_String_Slice_toNat_x3f(v___x_1614_);
lean_dec_ref_known(v___x_1614_, 3);
if (lean_obj_tag(v___x_1615_) == 0)
{
v___y_1603_ = v___x_1610_;
v___y_1604_ = v___y_1607_;
goto v___jp_1602_;
}
else
{
lean_object* v_val_1616_; 
lean_dec(v___y_1607_);
v_val_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_val_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v___y_1603_ = v___x_1610_;
v___y_1604_ = v_val_1616_;
goto v___jp_1602_;
}
}
}
}
}
v___jp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1538_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1));
v___x_1539_ = lean_string_append(v___x_1538_, v_depsFile_1530_);
lean_dec_ref(v_depsFile_1530_);
v___x_1540_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2));
v___x_1541_ = lean_string_append(v___x_1539_, v___x_1540_);
v___x_1542_ = lean_string_append(v___x_1541_, v_a_1537_);
lean_dec_ref(v_a_1537_);
v___x_1543_ = lean_mk_io_user_error(v___x_1542_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 1);
lean_ctor_set(v___x_1534_, 0, v___x_1543_);
v___x_1545_ = v___x_1534_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v_depsFile_1530_);
lean_dec_ref(v_fname_1527_);
v_a_1619_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1531_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1531_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___boxed(lean_object* v_fname_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_fname_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object* v_a_1630_, lean_object* v___y_1631_, lean_object* v_inst_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1630_, v___y_1631_, v_a_1633_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object* v_a_1636_, lean_object* v___y_1637_, lean_object* v_inst_1638_, lean_object* v_a_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(v_a_1636_, v___y_1637_, v_inst_1638_, v_a_1639_);
lean_dec(v___y_1637_);
lean_dec_ref(v_a_1636_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object* v_upperBound_1642_, lean_object* v_a_1643_, lean_object* v___y_1644_, lean_object* v_inst_1645_, lean_object* v_R_1646_, lean_object* v_a_1647_, lean_object* v_b_1648_, lean_object* v_c_1649_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1642_, v_a_1643_, v___y_1644_, v_a_1647_, v_b_1648_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object* v_upperBound_1652_, lean_object* v_a_1653_, lean_object* v___y_1654_, lean_object* v_inst_1655_, lean_object* v_R_1656_, lean_object* v_a_1657_, lean_object* v_b_1658_, lean_object* v_c_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(v_upperBound_1652_, v_a_1653_, v___y_1654_, v_inst_1655_, v_R_1656_, v_a_1657_, v_b_1658_, v_c_1659_);
lean_dec(v_upperBound_1652_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object* v_as_1662_, size_t v_sz_1663_, size_t v_i_1664_, lean_object* v_b_1665_){
_start:
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_usize_dec_lt(v_i_1664_, v_sz_1663_);
if (v___x_1667_ == 0)
{
return v_b_1665_;
}
else
{
lean_object* v_a_1668_; lean_object* v_cancelTk_x3f_1669_; lean_object* v___x_1670_; 
v_a_1668_ = lean_array_uget_borrowed(v_as_1662_, v_i_1664_);
v_cancelTk_x3f_1669_ = lean_ctor_get(v_a_1668_, 2);
v___x_1670_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_1669_) == 1)
{
lean_object* v_val_1677_; lean_object* v___x_1678_; 
v_val_1677_ = lean_ctor_get(v_cancelTk_x3f_1669_, 0);
v___x_1678_ = l_IO_CancelToken_set(v_val_1677_);
goto v___jp_1671_;
}
else
{
goto v___jp_1671_;
}
v___jp_1671_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; size_t v___x_1674_; size_t v___x_1675_; 
lean_inc(v_a_1668_);
v___x_1672_ = l_Lean_Language_SnapshotTask_get___redArg(v_a_1668_);
v___x_1673_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___x_1672_);
lean_dec(v___x_1672_);
v___x_1674_ = ((size_t)1ULL);
v___x_1675_ = lean_usize_add(v_i_1664_, v___x_1674_);
v_i_1664_ = v___x_1675_;
v_b_1665_ = v___x_1670_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object* v_s_1679_){
_start:
{
lean_object* v_children_1681_; lean_object* v___x_1682_; size_t v_sz_1683_; size_t v___x_1684_; lean_object* v___x_1685_; 
v_children_1681_ = lean_ctor_get(v_s_1679_, 1);
v___x_1682_ = lean_box(0);
v_sz_1683_ = lean_array_size(v_children_1681_);
v___x_1684_ = ((size_t)0ULL);
v___x_1685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_children_1681_, v_sz_1683_, v___x_1684_, v___x_1682_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object* v_s_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v_s_1686_);
lean_dec_ref(v_s_1686_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object* v_as_1689_, lean_object* v_sz_1690_, lean_object* v_i_1691_, lean_object* v_b_1692_, lean_object* v___y_1693_){
_start:
{
size_t v_sz_boxed_1694_; size_t v_i_boxed_1695_; lean_object* v_res_1696_; 
v_sz_boxed_1694_ = lean_unbox_usize(v_sz_1690_);
lean_dec(v_sz_1690_);
v_i_boxed_1695_ = lean_unbox_usize(v_i_1691_);
lean_dec(v_i_1691_);
v_res_1696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_as_1689_, v_sz_boxed_1694_, v_i_boxed_1695_, v_b_1692_);
lean_dec_ref(v_as_1689_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(lean_object* v_snap_1697_, lean_object* v_m_1698_){
_start:
{
lean_object* v_result_x3f_1699_; 
v_result_x3f_1699_ = lean_ctor_get(v_snap_1697_, 4);
lean_inc(v_result_x3f_1699_);
if (lean_obj_tag(v_result_x3f_1699_) == 1)
{
lean_object* v_val_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1798_; 
v_val_1700_ = lean_ctor_get(v_result_x3f_1699_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_result_x3f_1699_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1702_ = v_result_x3f_1699_;
v_isShared_1703_ = v_isSharedCheck_1798_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_val_1700_);
lean_dec(v_result_x3f_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1798_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v_toSnapshot_1704_; lean_object* v_metaSnap_1705_; lean_object* v_ictx_1706_; lean_object* v_stx_1707_; lean_object* v_parserState_1708_; lean_object* v_processedSnap_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1797_; 
v_toSnapshot_1704_ = lean_ctor_get(v_snap_1697_, 0);
v_metaSnap_1705_ = lean_ctor_get(v_snap_1697_, 1);
v_ictx_1706_ = lean_ctor_get(v_snap_1697_, 2);
v_stx_1707_ = lean_ctor_get(v_snap_1697_, 3);
v_parserState_1708_ = lean_ctor_get(v_val_1700_, 0);
v_processedSnap_1709_ = lean_ctor_get(v_val_1700_, 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_val_1700_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1711_ = v_val_1700_;
v_isShared_1712_ = v_isSharedCheck_1797_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_processedSnap_1709_);
lean_inc(v_parserState_1708_);
lean_dec(v_val_1700_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1797_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_processed_1713_; lean_object* v_result_x3f_1714_; 
v_processed_1713_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_1709_);
v_result_x3f_1714_ = lean_ctor_get(v_processed_1713_, 2);
lean_inc(v_result_x3f_1714_);
if (lean_obj_tag(v_result_x3f_1714_) == 1)
{
lean_object* v_val_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1796_; 
v_val_1715_ = lean_ctor_get(v_result_x3f_1714_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_result_x3f_1714_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1717_ = v_result_x3f_1714_;
v_isShared_1718_ = v_isSharedCheck_1796_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_val_1715_);
lean_dec(v_result_x3f_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1796_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v_cmdState_1719_; lean_object* v_toSnapshot_1720_; lean_object* v_metaSnap_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1794_; 
v_cmdState_1719_ = lean_ctor_get(v_val_1715_, 0);
lean_inc_ref(v_cmdState_1719_);
v_toSnapshot_1720_ = lean_ctor_get(v_processed_1713_, 0);
v_metaSnap_1721_ = lean_ctor_get(v_processed_1713_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_processed_1713_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v_processed_1713_, 2);
lean_dec(v_unused_1795_);
v___x_1723_ = v_processed_1713_;
v_isShared_1724_ = v_isSharedCheck_1794_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_metaSnap_1721_);
lean_inc(v_toSnapshot_1720_);
lean_dec(v_processed_1713_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1794_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_firstCmdSnap_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1792_; 
v_firstCmdSnap_1725_ = lean_ctor_get(v_val_1715_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_val_1715_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v_val_1715_, 0);
lean_dec(v_unused_1793_);
v___x_1727_ = v_val_1715_;
v_isShared_1728_ = v_isSharedCheck_1792_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_firstCmdSnap_1725_);
lean_dec(v_val_1715_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1792_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_env_1729_; lean_object* v_messages_1730_; lean_object* v_scopes_1731_; lean_object* v_usedQuotCtxts_1732_; lean_object* v_nextMacroScope_1733_; lean_object* v_maxRecDepth_1734_; lean_object* v_ngen_1735_; lean_object* v_auxDeclNGen_1736_; lean_object* v_infoState_1737_; lean_object* v_traceState_1738_; lean_object* v_snapshotTasks_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1791_; 
v_env_1729_ = lean_ctor_get(v_cmdState_1719_, 0);
v_messages_1730_ = lean_ctor_get(v_cmdState_1719_, 1);
v_scopes_1731_ = lean_ctor_get(v_cmdState_1719_, 2);
v_usedQuotCtxts_1732_ = lean_ctor_get(v_cmdState_1719_, 3);
v_nextMacroScope_1733_ = lean_ctor_get(v_cmdState_1719_, 4);
v_maxRecDepth_1734_ = lean_ctor_get(v_cmdState_1719_, 5);
v_ngen_1735_ = lean_ctor_get(v_cmdState_1719_, 6);
v_auxDeclNGen_1736_ = lean_ctor_get(v_cmdState_1719_, 7);
v_infoState_1737_ = lean_ctor_get(v_cmdState_1719_, 8);
v_traceState_1738_ = lean_ctor_get(v_cmdState_1719_, 9);
v_snapshotTasks_1739_ = lean_ctor_get(v_cmdState_1719_, 10);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_cmdState_1719_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1741_ = v_cmdState_1719_;
v_isShared_1742_ = v_isSharedCheck_1791_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_snapshotTasks_1739_);
lean_inc(v_traceState_1738_);
lean_inc(v_infoState_1737_);
lean_inc(v_auxDeclNGen_1736_);
lean_inc(v_ngen_1735_);
lean_inc(v_maxRecDepth_1734_);
lean_inc(v_nextMacroScope_1733_);
lean_inc(v_usedQuotCtxts_1732_);
lean_inc(v_scopes_1731_);
lean_inc(v_messages_1730_);
lean_inc(v_env_1729_);
lean_dec(v_cmdState_1719_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1791_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v_mainModule_1744_; uint8_t v___x_1745_; 
v___x_1743_ = l_Lean_Environment_header(v_env_1729_);
v_mainModule_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_mainModule_1744_);
lean_dec_ref(v___x_1743_);
v___x_1745_ = lean_name_eq(v_mainModule_1744_, v_m_1698_);
lean_dec(v_mainModule_1744_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1785_; 
lean_inc(v_stx_1707_);
lean_inc_ref(v_ictx_1706_);
lean_inc_ref(v_metaSnap_1705_);
lean_inc_ref(v_toSnapshot_1704_);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_snap_1697_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; lean_object* v_unused_1787_; lean_object* v_unused_1788_; lean_object* v_unused_1789_; lean_object* v_unused_1790_; 
v_unused_1786_ = lean_ctor_get(v_snap_1697_, 4);
lean_dec(v_unused_1786_);
v_unused_1787_ = lean_ctor_get(v_snap_1697_, 3);
lean_dec(v_unused_1787_);
v_unused_1788_ = lean_ctor_get(v_snap_1697_, 2);
lean_dec(v_unused_1788_);
v_unused_1789_ = lean_ctor_get(v_snap_1697_, 1);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v_snap_1697_, 0);
lean_dec(v_unused_1790_);
v___x_1747_ = v_snap_1697_;
v_isShared_1748_ = v_isSharedCheck_1785_;
goto v_resetjp_1746_;
}
else
{
lean_dec(v_snap_1697_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1785_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v_idx_1749_; lean_object* v_parentIdxs_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1783_; 
v_idx_1749_ = lean_ctor_get(v_auxDeclNGen_1736_, 1);
v_parentIdxs_1750_ = lean_ctor_get(v_auxDeclNGen_1736_, 2);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_auxDeclNGen_1736_);
if (v_isSharedCheck_1783_ == 0)
{
lean_object* v_unused_1784_; 
v_unused_1784_ = lean_ctor_get(v_auxDeclNGen_1736_, 0);
lean_dec(v_unused_1784_);
v___x_1752_ = v_auxDeclNGen_1736_;
v_isShared_1753_ = v_isSharedCheck_1783_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_parentIdxs_1750_);
lean_inc(v_idx_1749_);
lean_dec(v_auxDeclNGen_1736_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1783_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v_newEnv_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v_newEnv_1754_ = l_Lean_Environment_setMainModule(v_env_1729_, v_m_1698_);
v___x_1755_ = lean_box(0);
v___x_1756_ = l_Lean_mkPrivateName(v_newEnv_1754_, v___x_1755_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1756_);
v___x_1758_ = v___x_1752_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_idx_1749_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_parentIdxs_1750_);
v___x_1758_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v_newCmdState_1760_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 7, v___x_1758_);
lean_ctor_set(v___x_1741_, 0, v_newEnv_1754_);
v_newCmdState_1760_ = v___x_1741_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_newEnv_1754_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_messages_1730_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v_scopes_1731_);
lean_ctor_set(v_reuseFailAlloc_1781_, 3, v_usedQuotCtxts_1732_);
lean_ctor_set(v_reuseFailAlloc_1781_, 4, v_nextMacroScope_1733_);
lean_ctor_set(v_reuseFailAlloc_1781_, 5, v_maxRecDepth_1734_);
lean_ctor_set(v_reuseFailAlloc_1781_, 6, v_ngen_1735_);
lean_ctor_set(v_reuseFailAlloc_1781_, 7, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1781_, 8, v_infoState_1737_);
lean_ctor_set(v_reuseFailAlloc_1781_, 9, v_traceState_1738_);
lean_ctor_set(v_reuseFailAlloc_1781_, 10, v_snapshotTasks_1739_);
v_newCmdState_1760_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1762_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v_newCmdState_1760_);
v___x_1762_ = v___x_1727_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_newCmdState_1760_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_firstCmdSnap_1725_);
v___x_1762_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1764_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1762_);
v___x_1764_ = v___x_1717_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v_newProcessed_1766_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 2, v___x_1764_);
v_newProcessed_1766_ = v___x_1723_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_toSnapshot_1720_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_metaSnap_1721_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v___x_1764_);
v_newProcessed_1766_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1767_ = lean_box(0);
v___x_1768_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1767_, v_newProcessed_1766_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v___x_1768_);
v___x_1770_ = v___x_1711_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_parserState_1708_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 0, v___x_1770_);
v___x_1772_ = v___x_1702_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 4, v___x_1772_);
v___x_1774_ = v___x_1747_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_toSnapshot_1704_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_metaSnap_1705_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v_ictx_1706_);
lean_ctor_set(v_reuseFailAlloc_1775_, 3, v_stx_1707_);
lean_ctor_set(v_reuseFailAlloc_1775_, 4, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
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
lean_del_object(v___x_1741_);
lean_dec_ref(v_snapshotTasks_1739_);
lean_dec_ref(v_traceState_1738_);
lean_dec_ref(v_infoState_1737_);
lean_dec_ref(v_auxDeclNGen_1736_);
lean_dec_ref(v_ngen_1735_);
lean_dec(v_maxRecDepth_1734_);
lean_dec(v_nextMacroScope_1733_);
lean_dec(v_usedQuotCtxts_1732_);
lean_dec(v_scopes_1731_);
lean_dec_ref(v_messages_1730_);
lean_dec_ref(v_env_1729_);
lean_del_object(v___x_1727_);
lean_dec_ref(v_firstCmdSnap_1725_);
lean_del_object(v___x_1723_);
lean_dec_ref(v_metaSnap_1721_);
lean_dec_ref(v_toSnapshot_1720_);
lean_del_object(v___x_1717_);
lean_del_object(v___x_1711_);
lean_dec_ref(v_parserState_1708_);
lean_del_object(v___x_1702_);
lean_dec(v_m_1698_);
return v_snap_1697_;
}
}
}
}
}
}
else
{
lean_dec(v_result_x3f_1714_);
lean_dec(v_processed_1713_);
lean_del_object(v___x_1711_);
lean_dec_ref(v_parserState_1708_);
lean_del_object(v___x_1702_);
lean_dec(v_m_1698_);
return v_snap_1697_;
}
}
}
}
else
{
lean_dec(v_result_x3f_1699_);
lean_dec(v_m_1698_);
return v_snap_1697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object* v_incrFile_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_incrFile_1799_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object* v_incrFile_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(v_incrFile_1802_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object* v_opts_1805_, lean_object* v_incr_1806_, lean_object* v_res_1807_){
_start:
{
lean_object* v_cmdState_1809_; lean_object* v_env_1810_; lean_object* v_initModIdxs_1811_; lean_object* v___x_1812_; 
v_cmdState_1809_ = lean_ctor_get(v_res_1807_, 0);
lean_inc_ref(v_cmdState_1809_);
lean_dec_ref(v_res_1807_);
v_env_1810_ = lean_ctor_get(v_cmdState_1809_, 0);
lean_inc_ref(v_env_1810_);
lean_dec_ref(v_cmdState_1809_);
v_initModIdxs_1811_ = lean_ctor_get(v_incr_1806_, 1);
v___x_1812_ = l_Lean_runInitAttrsForModules(v_env_1810_, v_initModIdxs_1811_, v_opts_1805_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object* v_opts_1813_, lean_object* v_incr_1814_, lean_object* v_res_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(v_opts_1813_, v_incr_1814_, v_res_1815_);
lean_dec_ref(v_incr_1814_);
lean_dec_ref(v_opts_1813_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7(){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_enable_initializer_execution();
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(lean_object* v_env_1825_, lean_object* v_incrFile_1826_, lean_object* v_toSave_1827_){
_start:
{
lean_object* v___x_1829_; lean_object* v_regions_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; lean_object* v___x_1834_; 
v___x_1829_ = l_Lean_Environment_header(v_env_1825_);
v_regions_1830_ = lean_ctor_get(v___x_1829_, 2);
lean_inc_ref(v_regions_1830_);
lean_dec_ref(v___x_1829_);
v___x_1831_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1832_ = lean_box(0);
v___x_1833_ = 1;
v___x_1834_ = lean_compacted_region_save(v_incrFile_1826_, v___x_1831_, v_toSave_1827_, v_regions_1830_, v___x_1832_, v___x_1833_);
lean_dec_ref(v_regions_1830_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___boxed(lean_object* v_env_1835_, lean_object* v_incrFile_1836_, lean_object* v_toSave_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(v_env_1835_, v_incrFile_1836_, v_toSave_1837_);
lean_dec_ref(v_toSave_1837_);
lean_dec_ref(v_incrFile_1836_);
lean_dec_ref(v_env_1835_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__3(lean_object* v_opts_1840_, lean_object* v_opt_1841_){
_start:
{
lean_object* v_name_1842_; lean_object* v_map_1843_; lean_object* v___x_1844_; 
v_name_1842_ = lean_ctor_get(v_opt_1841_, 0);
v_map_1843_ = lean_ctor_get(v_opts_1840_, 0);
v___x_1844_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1843_, v_name_1842_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v___x_1845_; 
v___x_1845_ = lean_box(0);
return v___x_1845_;
}
else
{
lean_object* v_val_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1855_; 
v_val_1846_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1848_ = v___x_1844_;
v_isShared_1849_ = v_isSharedCheck_1855_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_val_1846_);
lean_dec(v___x_1844_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1855_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
if (lean_obj_tag(v_val_1846_) == 0)
{
lean_object* v_v_1850_; lean_object* v___x_1852_; 
v_v_1850_ = lean_ctor_get(v_val_1846_, 0);
lean_inc_ref(v_v_1850_);
lean_dec_ref_known(v_val_1846_, 1);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v_v_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_v_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
else
{
lean_object* v___x_1854_; 
lean_del_object(v___x_1848_);
lean_dec(v_val_1846_);
v___x_1854_ = lean_box(0);
return v___x_1854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object* v_opts_1856_, lean_object* v_opt_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__3(v_opts_1856_, v_opt_1857_);
lean_dec_ref(v_opt_1857_);
lean_dec_ref(v_opts_1856_);
return v_res_1858_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(lean_object* v_opts_1859_, lean_object* v_opt_1860_){
_start:
{
lean_object* v_name_1861_; lean_object* v_defValue_1862_; lean_object* v_map_1863_; lean_object* v___x_1864_; 
v_name_1861_ = lean_ctor_get(v_opt_1860_, 0);
v_defValue_1862_ = lean_ctor_get(v_opt_1860_, 1);
v_map_1863_ = lean_ctor_get(v_opts_1859_, 0);
v___x_1864_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1863_, v_name_1861_);
if (lean_obj_tag(v___x_1864_) == 0)
{
uint8_t v___x_1865_; 
v___x_1865_ = lean_unbox(v_defValue_1862_);
return v___x_1865_;
}
else
{
lean_object* v_val_1866_; 
v_val_1866_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v___x_1864_, 1);
if (lean_obj_tag(v_val_1866_) == 1)
{
uint8_t v_v_1867_; 
v_v_1867_ = lean_ctor_get_uint8(v_val_1866_, 0);
lean_dec_ref_known(v_val_1866_, 0);
return v_v_1867_;
}
else
{
uint8_t v___x_1868_; 
lean_dec(v_val_1866_);
v___x_1868_ = lean_unbox(v_defValue_1862_);
return v___x_1868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_opts_1869_, lean_object* v_opt_1870_){
_start:
{
uint8_t v_res_1871_; lean_object* v_r_1872_; 
v_res_1871_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(v_opts_1869_, v_opt_1870_);
lean_dec_ref(v_opt_1870_);
lean_dec_ref(v_opts_1869_);
v_r_1872_ = lean_box(v_res_1871_);
return v_r_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_s_1875_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = ((lean_object*)(l_Lean_Elab_runFrontend___lam__0___closed__0));
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v_s_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v___f_1879_, lean_object* v_s_1880_){
_start:
{
lean_object* v_toSnapshot_1881_; lean_object* v_metaSnap_1882_; lean_object* v_result_x3f_1883_; lean_object* v___y_1885_; 
v_toSnapshot_1881_ = lean_ctor_get(v_s_1880_, 0);
lean_inc_ref(v_toSnapshot_1881_);
v_metaSnap_1882_ = lean_ctor_get(v_s_1880_, 1);
lean_inc_ref(v_metaSnap_1882_);
v_result_x3f_1883_ = lean_ctor_get(v_s_1880_, 2);
lean_inc(v_result_x3f_1883_);
lean_dec_ref(v_s_1880_);
if (lean_obj_tag(v_result_x3f_1883_) == 0)
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_box(0);
v___y_1885_ = v___x_1895_;
goto v___jp_1884_;
}
else
{
lean_object* v_val_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1909_; 
v_val_1896_ = lean_ctor_get(v_result_x3f_1883_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_result_x3f_1883_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1898_ = v_result_x3f_1883_;
v_isShared_1899_ = v_isSharedCheck_1909_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_val_1896_);
lean_dec(v_result_x3f_1883_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1909_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_firstCmdSnap_1900_; lean_object* v_stx_x3f_1901_; lean_object* v_reportingRange_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v_firstCmdSnap_1900_ = lean_ctor_get(v_val_1896_, 1);
lean_inc_ref(v_firstCmdSnap_1900_);
lean_dec(v_val_1896_);
v_stx_x3f_1901_ = lean_ctor_get(v_firstCmdSnap_1900_, 0);
lean_inc(v_stx_x3f_1901_);
v_reportingRange_1902_ = lean_ctor_get(v_firstCmdSnap_1900_, 1);
lean_inc(v_reportingRange_1902_);
v___x_1903_ = ((lean_object*)(l_Lean_Elab_runFrontend___lam__2___closed__0));
v___x_1904_ = 1;
v___x_1905_ = l_Lean_Language_SnapshotTask_map___redArg(v_firstCmdSnap_1900_, v___x_1903_, v_stx_x3f_1901_, v_reportingRange_1902_, v___x_1904_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1905_);
v___x_1907_ = v___x_1898_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v___y_1885_ = v___x_1907_;
goto v___jp_1884_;
}
}
}
v___jp_1884_:
{
lean_object* v_stx_x3f_1886_; lean_object* v_reportingRange_1887_; uint8_t v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_stx_x3f_1886_ = lean_ctor_get(v_metaSnap_1882_, 0);
lean_inc(v_stx_x3f_1886_);
v_reportingRange_1887_ = lean_ctor_get(v_metaSnap_1882_, 1);
lean_inc(v_reportingRange_1887_);
v___x_1888_ = 1;
v___x_1889_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_1882_, v___f_1879_, v_stx_x3f_1886_, v_reportingRange_1887_, v___x_1888_);
v___x_1890_ = lean_unsigned_to_nat(1u);
v___x_1891_ = lean_mk_empty_array_with_capacity(v___x_1890_);
v___x_1892_ = lean_array_push(v___x_1891_, v___x_1889_);
v___x_1893_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_1885_, v___x_1892_);
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_toSnapshot_1881_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
return v___x_1894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_x_1910_, lean_object* v_x_1911_, lean_object* v_hOpt_1912_){
_start:
{
lean_inc_ref(v_hOpt_1912_);
return v_hOpt_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object* v_x_1913_, lean_object* v_x_1914_, lean_object* v_hOpt_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_Elab_runFrontend___lam__1(v_x_1913_, v_x_1914_, v_hOpt_1915_);
lean_dec_ref(v_hOpt_1915_);
lean_dec_ref(v_x_1914_);
lean_dec(v_x_1913_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Elab_runFrontend_spec__2_spec__3(size_t v_sz_1917_, size_t v_i_1918_, lean_object* v_bs_1919_){
_start:
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_usize_dec_lt(v_i_1918_, v_sz_1917_);
if (v___x_1920_ == 0)
{
return v_bs_1919_;
}
else
{
lean_object* v_v_1921_; lean_object* v___x_1922_; lean_object* v_bs_x27_1923_; lean_object* v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v_v_1921_ = lean_array_uget(v_bs_1919_, v_i_1918_);
v___x_1922_ = lean_unsigned_to_nat(0u);
v_bs_x27_1923_ = lean_array_uset(v_bs_1919_, v_i_1918_, v___x_1922_);
v___x_1924_ = l_Lean_instToJsonModuleArtifacts_toJson(v_v_1921_);
v___x_1925_ = ((size_t)1ULL);
v___x_1926_ = lean_usize_add(v_i_1918_, v___x_1925_);
v___x_1927_ = lean_array_uset(v_bs_x27_1923_, v_i_1918_, v___x_1924_);
v_i_1918_ = v___x_1926_;
v_bs_1919_ = v___x_1927_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object* v_sz_1929_, lean_object* v_i_1930_, lean_object* v_bs_1931_){
_start:
{
size_t v_sz_boxed_1932_; size_t v_i_boxed_1933_; lean_object* v_res_1934_; 
v_sz_boxed_1932_ = lean_unbox_usize(v_sz_1929_);
lean_dec(v_sz_1929_);
v_i_boxed_1933_ = lean_unbox_usize(v_i_1930_);
lean_dec(v_i_1930_);
v_res_1934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_sz_boxed_1932_, v_i_boxed_1933_, v_bs_1931_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_a_1935_){
_start:
{
size_t v_sz_1936_; size_t v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_sz_1936_ = lean_array_size(v_a_1935_);
v___x_1937_ = ((size_t)0ULL);
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_sz_1936_, v___x_1937_, v_a_1935_);
v___x_1939_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_env_1940_, lean_object* v_incrFile_1941_, lean_object* v_snapToSave_1942_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = l_Lean_getRegularInitAttrModIdxs(v_env_1940_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v_snapToSave_1942_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(v_env_1940_, v_incrFile_1941_, v___x_1945_);
lean_dec_ref_known(v___x_1945_, 2);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1948_; lean_object* v_regions_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v___x_1948_ = l_Lean_Environment_header(v_env_1940_);
v_regions_1949_ = lean_ctor_get(v___x_1948_, 2);
lean_inc_ref(v_regions_1949_);
lean_dec_ref(v___x_1948_);
v___x_1950_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1949_);
lean_dec_ref(v_regions_1949_);
v___x_1951_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
v___x_1952_ = l_System_FilePath_addExtension(v_incrFile_1941_, v___x_1951_);
v___x_1953_ = l_Array_toJson___at___00Lean_Elab_runFrontend_spec__2(v___x_1950_);
v___x_1954_ = l_Lean_Json_compress(v___x_1953_);
v___x_1955_ = l_IO_FS_writeFile(v___x_1952_, v___x_1954_);
lean_dec_ref(v___x_1954_);
lean_dec_ref(v___x_1952_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1963_; 
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; 
v_unused_1964_ = lean_ctor_get(v___x_1955_, 0);
lean_dec(v_unused_1964_);
v___x_1957_ = v___x_1955_;
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
else
{
lean_dec(v___x_1955_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1963_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1959_ = lean_runtime_forget(v_a_1947_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1959_);
v___x_1961_ = v___x_1957_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
else
{
lean_dec(v_a_1947_);
return v___x_1955_;
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v_incrFile_1941_);
v_a_1965_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1946_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1946_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_env_1973_, lean_object* v_incrFile_1974_, lean_object* v_snapToSave_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Elab_runFrontend___lam__3(v_env_1973_, v_incrFile_1974_, v_snapToSave_1975_);
lean_dec_ref(v_env_1973_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* v_fileMap_1978_, lean_object* v_env_1979_, lean_object* v___x_1980_, lean_object* v_opts_1981_, lean_object* v_val_1982_, uint8_t v___x_1983_, uint8_t v_a_1984_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1986_ = l_Lean_Linter_recordLints(v_fileMap_1978_, v_env_1979_, v___x_1980_);
v___x_1987_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1988_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(v_opts_1981_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_writeModule(v___x_1986_, v_val_1982_, v___x_1983_);
return v___x_1989_;
}
else
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_writeModule(v___x_1986_, v_val_1982_, v_a_1984_);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object* v_fileMap_1991_, lean_object* v_env_1992_, lean_object* v___x_1993_, lean_object* v_opts_1994_, lean_object* v_val_1995_, lean_object* v___x_1996_, lean_object* v_a_1997_, lean_object* v___y_1998_){
_start:
{
uint8_t v___x_6614__boxed_1999_; uint8_t v_a_6615__boxed_2000_; lean_object* v_res_2001_; 
v___x_6614__boxed_1999_ = lean_unbox(v___x_1996_);
v_a_6615__boxed_2000_ = lean_unbox(v_a_1997_);
v_res_2001_ = l_Lean_Elab_runFrontend___lam__4(v_fileMap_1991_, v_env_1992_, v___x_1993_, v_opts_1994_, v_val_1995_, v___x_6614__boxed_1999_, v_a_6615__boxed_2000_);
lean_dec_ref(v_opts_1994_);
lean_dec_ref(v___x_1993_);
lean_dec_ref(v_fileMap_1991_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_2002_, size_t v_i_2003_, size_t v_stop_2004_, lean_object* v_b_2005_){
_start:
{
uint8_t v___x_2007_; 
v___x_2007_ = lean_usize_dec_eq(v_i_2003_, v_stop_2004_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_array_uget_borrowed(v_as_2002_, v_i_2003_);
lean_inc(v___x_2008_);
v___x_2009_ = lean_load_dynlib(v___x_2008_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; size_t v___x_2011_; size_t v___x_2012_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2011_ = ((size_t)1ULL);
v___x_2012_ = lean_usize_add(v_i_2003_, v___x_2011_);
v_i_2003_ = v___x_2012_;
v_b_2005_ = v_a_2010_;
goto _start;
}
else
{
return v___x_2009_;
}
}
else
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_b_2005_);
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_2015_, lean_object* v_i_2016_, lean_object* v_stop_2017_, lean_object* v_b_2018_, lean_object* v___y_2019_){
_start:
{
size_t v_i_boxed_2020_; size_t v_stop_boxed_2021_; lean_object* v_res_2022_; 
v_i_boxed_2020_ = lean_unbox_usize(v_i_2016_);
lean_dec(v_i_2016_);
v_stop_boxed_2021_ = lean_unbox_usize(v_stop_2017_);
lean_dec(v_stop_2017_);
v_res_2022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_2015_, v_i_boxed_2020_, v_stop_boxed_2021_, v_b_2018_);
lean_dec_ref(v_as_2015_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object* v_setup_x3f_2023_, lean_object* v___f_2024_, lean_object* v___x_2025_, lean_object* v_plugins_2026_, uint32_t v_trustLevel_2027_, uint8_t v___x_2028_, lean_object* v_mainModuleName_2029_, lean_object* v_stx_2030_, lean_object* v___y_2031_){
_start:
{
uint8_t v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; 
if (lean_obj_tag(v_setup_x3f_2023_) == 1)
{
lean_object* v_val_2047_; lean_object* v_name_2048_; lean_object* v_package_x3f_2049_; uint8_t v_isModule_2050_; lean_object* v_imports_x3f_2051_; lean_object* v_importArts_2052_; lean_object* v_dynlibs_2053_; lean_object* v_plugins_2054_; lean_object* v_options_2055_; lean_object* v___y_2062_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
lean_dec(v_mainModuleName_2029_);
v_val_2047_ = lean_ctor_get(v_setup_x3f_2023_, 0);
lean_inc(v_val_2047_);
lean_dec_ref_known(v_setup_x3f_2023_, 1);
v_name_2048_ = lean_ctor_get(v_val_2047_, 0);
lean_inc(v_name_2048_);
v_package_x3f_2049_ = lean_ctor_get(v_val_2047_, 1);
lean_inc(v_package_x3f_2049_);
v_isModule_2050_ = lean_ctor_get_uint8(v_val_2047_, sizeof(void*)*7);
v_imports_x3f_2051_ = lean_ctor_get(v_val_2047_, 2);
lean_inc(v_imports_x3f_2051_);
v_importArts_2052_ = lean_ctor_get(v_val_2047_, 3);
lean_inc(v_importArts_2052_);
v_dynlibs_2053_ = lean_ctor_get(v_val_2047_, 4);
lean_inc_ref(v_dynlibs_2053_);
v_plugins_2054_ = lean_ctor_get(v_val_2047_, 5);
lean_inc_ref(v_plugins_2054_);
v_options_2055_ = lean_ctor_get(v_val_2047_, 6);
lean_inc(v_options_2055_);
lean_dec(v_val_2047_);
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_array_get_size(v_dynlibs_2053_);
v___x_2073_ = lean_nat_dec_lt(v___x_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_dec_ref(v_dynlibs_2053_);
goto v___jp_2056_;
}
else
{
lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2074_ = lean_box(0);
v___x_2075_ = lean_nat_dec_le(v___x_2072_, v___x_2072_);
if (v___x_2075_ == 0)
{
if (v___x_2073_ == 0)
{
lean_dec_ref(v_dynlibs_2053_);
goto v___jp_2056_;
}
else
{
size_t v___x_2076_; size_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = ((size_t)0ULL);
v___x_2077_ = lean_usize_of_nat(v___x_2072_);
v___x_2078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2053_, v___x_2076_, v___x_2077_, v___x_2074_);
lean_dec_ref(v_dynlibs_2053_);
v___y_2062_ = v___x_2078_;
goto v___jp_2061_;
}
}
else
{
size_t v___x_2079_; size_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = ((size_t)0ULL);
v___x_2080_ = lean_usize_of_nat(v___x_2072_);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2053_, v___x_2079_, v___x_2080_, v___x_2074_);
lean_dec_ref(v_dynlibs_2053_);
v___y_2062_ = v___x_2081_;
goto v___jp_2061_;
}
}
v___jp_2056_:
{
uint8_t v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2030_);
v___x_2058_ = lean_strict_or(v_isModule_2050_, v___x_2057_);
if (lean_obj_tag(v_imports_x3f_2051_) == 0)
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2030_, v___x_2028_);
v___y_2034_ = v___x_2058_;
v___y_2035_ = v_name_2048_;
v___y_2036_ = v_options_2055_;
v___y_2037_ = v_package_x3f_2049_;
v___y_2038_ = v_plugins_2054_;
v___y_2039_ = v_importArts_2052_;
v___y_2040_ = v___x_2059_;
goto v___jp_2033_;
}
else
{
lean_object* v_val_2060_; 
lean_dec(v_stx_2030_);
v_val_2060_ = lean_ctor_get(v_imports_x3f_2051_, 0);
lean_inc(v_val_2060_);
lean_dec_ref_known(v_imports_x3f_2051_, 1);
v___y_2034_ = v___x_2058_;
v___y_2035_ = v_name_2048_;
v___y_2036_ = v_options_2055_;
v___y_2037_ = v_package_x3f_2049_;
v___y_2038_ = v_plugins_2054_;
v___y_2039_ = v_importArts_2052_;
v___y_2040_ = v_val_2060_;
goto v___jp_2033_;
}
}
v___jp_2061_:
{
if (lean_obj_tag(v___y_2062_) == 0)
{
lean_dec_ref_known(v___y_2062_, 1);
goto v___jp_2056_;
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_options_2055_);
lean_dec_ref(v_plugins_2054_);
lean_dec(v_importArts_2052_);
lean_dec(v_imports_x3f_2051_);
lean_dec(v_package_x3f_2049_);
lean_dec(v_name_2048_);
lean_dec(v_stx_2030_);
lean_dec_ref(v_plugins_2026_);
lean_dec_ref(v___x_2025_);
lean_dec_ref(v___f_2024_);
v_a_2063_ = lean_ctor_get(v___y_2062_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___y_2062_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___y_2062_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___y_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
}
else
{
lean_object* v___x_2082_; uint8_t v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec_ref(v___f_2024_);
lean_dec(v_setup_x3f_2023_);
v___x_2082_ = lean_box(0);
v___x_2083_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2030_);
v___x_2084_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2030_, v___x_2028_);
v___x_2085_ = lean_box(1);
v___x_2086_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2086_, 0, v_mainModuleName_2029_);
lean_ctor_set(v___x_2086_, 1, v___x_2082_);
lean_ctor_set(v___x_2086_, 2, v___x_2084_);
lean_ctor_set(v___x_2086_, 3, v___x_2025_);
lean_ctor_set(v___x_2086_, 4, v___x_2085_);
lean_ctor_set(v___x_2086_, 5, v_plugins_2026_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*6 + 4, v___x_2083_);
lean_ctor_set_uint32(v___x_2086_, sizeof(void*)*6, v_trustLevel_2027_);
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
v___jp_2033_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2041_ = l_Lean_LeanOptions_toOptions(v___y_2036_);
v___x_2042_ = l_Lean_Options_mergeBy(v___f_2024_, v___x_2025_, v___x_2041_);
v___x_2043_ = l_Array_append___redArg(v_plugins_2026_, v___y_2038_);
lean_dec_ref(v___y_2038_);
v___x_2044_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2044_, 0, v___y_2035_);
lean_ctor_set(v___x_2044_, 1, v___y_2037_);
lean_ctor_set(v___x_2044_, 2, v___y_2040_);
lean_ctor_set(v___x_2044_, 3, v___x_2042_);
lean_ctor_set(v___x_2044_, 4, v___y_2039_);
lean_ctor_set(v___x_2044_, 5, v___x_2043_);
lean_ctor_set_uint8(v___x_2044_, sizeof(void*)*6 + 4, v___y_2034_);
lean_ctor_set_uint32(v___x_2044_, sizeof(void*)*6, v_trustLevel_2027_);
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5___boxed(lean_object* v_setup_x3f_2089_, lean_object* v___f_2090_, lean_object* v___x_2091_, lean_object* v_plugins_2092_, lean_object* v_trustLevel_2093_, lean_object* v___x_2094_, lean_object* v_mainModuleName_2095_, lean_object* v_stx_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint32_t v_trustLevel_boxed_2099_; uint8_t v___x_6659__boxed_2100_; lean_object* v_res_2101_; 
v_trustLevel_boxed_2099_ = lean_unbox_uint32(v_trustLevel_2093_);
lean_dec(v_trustLevel_2093_);
v___x_6659__boxed_2100_ = lean_unbox(v___x_2094_);
v_res_2101_ = l_Lean_Elab_runFrontend___lam__5(v_setup_x3f_2089_, v___f_2090_, v___x_2091_, v_plugins_2092_, v_trustLevel_boxed_2099_, v___x_6659__boxed_2100_, v_mainModuleName_2095_, v_stx_2096_, v___y_2097_);
lean_dec_ref(v___y_2097_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_2105_, lean_object* v_k_2106_, uint8_t v_v_2107_){
_start:
{
lean_object* v_map_2108_; uint8_t v_hasTrace_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2123_; 
v_map_2108_ = lean_ctor_get(v_o_2105_, 0);
v_hasTrace_2109_ = lean_ctor_get_uint8(v_o_2105_, sizeof(void*)*1);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_o_2105_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2111_ = v_o_2105_;
v_isShared_2112_ = v_isSharedCheck_2123_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_map_2108_);
lean_dec(v_o_2105_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2123_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2113_, 0, v_v_2107_);
lean_inc(v_k_2106_);
v___x_2114_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2106_, v___x_2113_, v_map_2108_);
if (v_hasTrace_2109_ == 0)
{
lean_object* v___x_2115_; uint8_t v___x_2116_; lean_object* v___x_2118_; 
v___x_2115_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_2116_ = l_Lean_Name_isPrefixOf(v___x_2115_, v_k_2106_);
lean_dec(v_k_2106_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2114_);
v___x_2118_ = v___x_2111_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2114_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_ctor_set_uint8(v___x_2118_, sizeof(void*)*1, v___x_2116_);
return v___x_2118_;
}
}
else
{
lean_object* v___x_2121_; 
lean_dec(v_k_2106_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2114_);
v___x_2121_ = v___x_2111_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2114_);
lean_ctor_set_uint8(v_reuseFailAlloc_2122_, sizeof(void*)*1, v_hasTrace_2109_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_2124_, lean_object* v_k_2125_, lean_object* v_v_2126_){
_start:
{
uint8_t v_v_boxed_2127_; lean_object* v_res_2128_; 
v_v_boxed_2127_ = lean_unbox(v_v_2126_);
v_res_2128_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2124_, v_k_2125_, v_v_boxed_2127_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_2129_, lean_object* v_opt_2130_, uint8_t v_val_2131_){
_start:
{
lean_object* v_name_2132_; lean_object* v___x_2133_; 
v_name_2132_ = lean_ctor_get(v_opt_2130_, 0);
lean_inc(v_name_2132_);
lean_dec_ref(v_opt_2130_);
v___x_2133_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_2129_, v_name_2132_, v_val_2131_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_2134_, lean_object* v_opt_2135_, lean_object* v_val_2136_){
_start:
{
uint8_t v_val_boxed_2137_; lean_object* v_res_2138_; 
v_val_boxed_2137_ = lean_unbox(v_val_2136_);
v_res_2138_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2134_, v_opt_2135_, v_val_boxed_2137_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_2139_, lean_object* v_opt_2140_, uint8_t v_val_2141_){
_start:
{
lean_object* v_name_2142_; lean_object* v_map_2143_; uint8_t v___x_2144_; 
v_name_2142_ = lean_ctor_get(v_opt_2140_, 0);
v_map_2143_ = lean_ctor_get(v_opts_2139_, 0);
v___x_2144_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_2142_, v_map_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2139_, v_opt_2140_, v_val_2141_);
return v___x_2145_;
}
else
{
lean_dec_ref(v_opt_2140_);
return v_opts_2139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_2146_, lean_object* v_opt_2147_, lean_object* v_val_2148_){
_start:
{
uint8_t v_val_boxed_2149_; lean_object* v_res_2150_; 
v_val_boxed_2149_ = lean_unbox(v_val_2148_);
v_res_2150_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2146_, v_opt_2147_, v_val_boxed_2149_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_as_2151_, size_t v_i_2152_, size_t v_stop_2153_, lean_object* v_b_2154_){
_start:
{
lean_object* v___y_2156_; uint8_t v___x_2160_; 
v___x_2160_ = lean_usize_dec_eq(v_i_2152_, v_stop_2153_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; lean_object* v_infoTree_x3f_2162_; 
v___x_2161_ = lean_array_uget_borrowed(v_as_2151_, v_i_2152_);
v_infoTree_x3f_2162_ = lean_ctor_get(v___x_2161_, 2);
if (lean_obj_tag(v_infoTree_x3f_2162_) == 1)
{
lean_object* v_val_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_val_2163_ = lean_ctor_get(v_infoTree_x3f_2162_, 0);
v___x_2164_ = lean_unsigned_to_nat(1u);
v___x_2165_ = lean_mk_empty_array_with_capacity(v___x_2164_);
lean_inc(v_val_2163_);
v___x_2166_ = lean_array_push(v___x_2165_, v_val_2163_);
v___x_2167_ = l_Array_append___redArg(v_b_2154_, v___x_2166_);
lean_dec_ref(v___x_2166_);
v___y_2156_ = v___x_2167_;
goto v___jp_2155_;
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_2169_ = l_Array_append___redArg(v_b_2154_, v___x_2168_);
v___y_2156_ = v___x_2169_;
goto v___jp_2155_;
}
}
else
{
return v_b_2154_;
}
v___jp_2155_:
{
size_t v___x_2157_; size_t v___x_2158_; 
v___x_2157_ = ((size_t)1ULL);
v___x_2158_ = lean_usize_add(v_i_2152_, v___x_2157_);
v_i_2152_ = v___x_2158_;
v_b_2154_ = v___y_2156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_as_2170_, lean_object* v_i_2171_, lean_object* v_stop_2172_, lean_object* v_b_2173_){
_start:
{
size_t v_i_boxed_2174_; size_t v_stop_boxed_2175_; lean_object* v_res_2176_; 
v_i_boxed_2174_ = lean_unbox_usize(v_i_2171_);
lean_dec(v_i_2171_);
v_stop_boxed_2175_ = lean_unbox_usize(v_stop_2172_);
lean_dec(v_stop_2172_);
v_res_2176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v_as_2170_, v_i_boxed_2174_, v_stop_boxed_2175_, v_b_2173_);
lean_dec_ref(v_as_2170_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__4(size_t v_sz_2177_, size_t v_i_2178_, lean_object* v_bs_2179_){
_start:
{
uint8_t v___x_2180_; 
v___x_2180_ = lean_usize_dec_lt(v_i_2178_, v_sz_2177_);
if (v___x_2180_ == 0)
{
return v_bs_2179_;
}
else
{
lean_object* v_v_2181_; lean_object* v_traces_2182_; lean_object* v___x_2183_; lean_object* v_bs_x27_2184_; size_t v___x_2185_; size_t v___x_2186_; lean_object* v___x_2187_; 
v_v_2181_ = lean_array_uget_borrowed(v_bs_2179_, v_i_2178_);
v_traces_2182_ = lean_ctor_get(v_v_2181_, 3);
lean_inc_ref(v_traces_2182_);
v___x_2183_ = lean_unsigned_to_nat(0u);
v_bs_x27_2184_ = lean_array_uset(v_bs_2179_, v_i_2178_, v___x_2183_);
v___x_2185_ = ((size_t)1ULL);
v___x_2186_ = lean_usize_add(v_i_2178_, v___x_2185_);
v___x_2187_ = lean_array_uset(v_bs_x27_2184_, v_i_2178_, v_traces_2182_);
v_i_2178_ = v___x_2186_;
v_bs_2179_ = v___x_2187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_sz_2189_, lean_object* v_i_2190_, lean_object* v_bs_2191_){
_start:
{
size_t v_sz_boxed_2192_; size_t v_i_boxed_2193_; lean_object* v_res_2194_; 
v_sz_boxed_2192_ = lean_unbox_usize(v_sz_2189_);
lean_dec(v_sz_2189_);
v_i_boxed_2193_ = lean_unbox_usize(v_i_2190_);
lean_dec(v_i_2190_);
v_res_2194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__4(v_sz_boxed_2192_, v_i_boxed_2193_, v_bs_2191_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_2195_, size_t v_i_2196_, size_t v_stop_2197_, lean_object* v_b_2198_){
_start:
{
uint8_t v___x_2199_; 
v___x_2199_ = lean_usize_dec_eq(v_i_2196_, v_stop_2197_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; size_t v___x_2204_; size_t v___x_2205_; 
v___x_2200_ = lean_array_uget_borrowed(v_as_2195_, v_i_2196_);
v___x_2201_ = 2;
v___x_2202_ = lean_box(v___x_2201_);
lean_inc(v___x_2200_);
v___x_2203_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2200_, v___x_2202_, v_b_2198_);
v___x_2204_ = ((size_t)1ULL);
v___x_2205_ = lean_usize_add(v_i_2196_, v___x_2204_);
v_i_2196_ = v___x_2205_;
v_b_2198_ = v___x_2203_;
goto _start;
}
else
{
return v_b_2198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_2207_, lean_object* v_i_2208_, lean_object* v_stop_2209_, lean_object* v_b_2210_){
_start:
{
size_t v_i_boxed_2211_; size_t v_stop_boxed_2212_; lean_object* v_res_2213_; 
v_i_boxed_2211_ = lean_unbox_usize(v_i_2208_);
lean_dec(v_i_2208_);
v_stop_boxed_2212_ = lean_unbox_usize(v_stop_2209_);
lean_dec(v_stop_2209_);
v_res_2213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_2207_, v_i_boxed_2211_, v_stop_boxed_2212_, v_b_2210_);
lean_dec_ref(v_as_2207_);
return v_res_2213_;
}
}
static double _init_l_Lean_Elab_runFrontend___closed__3(void){
_start:
{
lean_object* v___x_2218_; double v___x_2219_; 
v___x_2218_ = lean_unsigned_to_nat(1000000000u);
v___x_2219_ = lean_float_of_nat(v___x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_2221_, lean_object* v_opts_2222_, lean_object* v_fileName_2223_, lean_object* v_mainModuleName_2224_, uint32_t v_trustLevel_2225_, lean_object* v_oleanFileName_x3f_2226_, lean_object* v_ileanFileName_x3f_2227_, uint8_t v_jsonOutput_2228_, lean_object* v_errorOnKinds_2229_, lean_object* v_plugins_2230_, uint8_t v_printStats_2231_, lean_object* v_setup_x3f_2232_, lean_object* v_incrSaveFileName_x3f_2233_, lean_object* v_incrLoadFileName_x3f_2234_, lean_object* v_incrHeaderSaveFileName_x3f_2235_){
_start:
{
lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___x_2243_; lean_object* v___f_2244_; lean_object* v___f_2245_; lean_object* v___f_2246_; lean_object* v___x_2247_; double v___x_2248_; double v___x_2249_; double v___x_2250_; uint8_t v___x_2251_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2364_; lean_object* v___y_2365_; uint8_t v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; uint8_t v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2396_; lean_object* v___y_2397_; uint8_t v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; uint8_t v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; uint8_t v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; uint8_t v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v_a_2514_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v___y_2543_; 
v___x_2243_ = lean_io_mono_nanos_now();
v___f_2244_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___f_2245_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__1));
v___f_2246_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__2));
v___x_2247_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2248_ = lean_float_of_nat(v___x_2243_);
v___x_2249_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__3, &l_Lean_Elab_runFrontend___closed__3_once, _init_l_Lean_Elab_runFrontend___closed__3);
v___x_2250_ = lean_float_div(v___x_2248_, v___x_2249_);
v___x_2251_ = 1;
v___x_2314_ = lean_string_utf8_byte_size(v_input_2221_);
v___x_2315_ = l_Lean_Parser_mkInputContext___redArg(v_input_2221_, v_fileName_2223_, v___x_2251_, v___x_2314_);
v___x_2541_ = l_Lean_internal_cmdlineSnapshots;
if (lean_obj_tag(v_incrSaveFileName_x3f_2233_) == 0)
{
v___y_2543_ = v___x_2251_;
goto v___jp_2542_;
}
else
{
uint8_t v___x_2586_; 
v___x_2586_ = 0;
v___y_2543_ = v___x_2586_;
goto v___jp_2542_;
}
v___jp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2240_ = lean_runtime_forget(v___y_2239_);
v___x_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2241_, 0, v___y_2238_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
return v___x_2242_;
}
v___jp_2252_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = l_Lean_trace_profiler_output;
v___x_2258_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__3(v___y_2256_, v___x_2257_);
if (lean_obj_tag(v___x_2258_) == 1)
{
lean_object* v_val_2259_; lean_object* v___x_2260_; size_t v_sz_2261_; size_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_dec_ref(v___y_2254_);
v_val_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_val_2259_);
lean_dec_ref_known(v___x_2258_, 1);
lean_inc_ref(v___y_2255_);
v___x_2260_ = l_Lean_Language_SnapshotTree_getAll(v___y_2255_);
v_sz_2261_ = lean_array_size(v___x_2260_);
v___x_2262_ = ((size_t)0ULL);
v___x_2263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__4(v_sz_2261_, v___x_2262_, v___x_2260_);
v___x_2264_ = l_Lean_Name_toString(v_mainModuleName_2224_, v___x_2251_);
v___x_2265_ = l_Lean_Firefox_Profile_export(v___x_2264_, v___x_2250_, v___x_2263_, v___y_2256_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v___x_2263_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2267_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2266_);
v___x_2268_ = l_Lean_Json_compress(v___x_2267_);
v___x_2269_ = l_IO_FS_writeFile(v_val_2259_, v___x_2268_);
lean_dec_ref(v___x_2268_);
lean_dec(v_val_2259_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_dec_ref_known(v___x_2269_, 1);
v___y_2238_ = v___y_2253_;
v___y_2239_ = v___y_2255_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v___y_2255_);
lean_dec_ref(v___y_2253_);
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_val_2259_);
lean_dec_ref(v___y_2255_);
lean_dec_ref(v___y_2253_);
v_a_2278_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2265_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2265_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v___x_2286_; uint8_t v___x_2287_; 
lean_dec(v___x_2258_);
v___x_2286_ = l_Lean_trace_profiler_serve;
v___x_2287_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(v___y_2254_, v___x_2286_);
lean_dec_ref(v___y_2254_);
if (v___x_2287_ == 0)
{
lean_dec_ref(v___y_2256_);
lean_dec(v_mainModuleName_2224_);
v___y_2238_ = v___y_2253_;
v___y_2239_ = v___y_2255_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2288_; size_t v_sz_2289_; size_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_inc_ref(v___y_2255_);
v___x_2288_ = l_Lean_Language_SnapshotTree_getAll(v___y_2255_);
v_sz_2289_ = lean_array_size(v___x_2288_);
v___x_2290_ = ((size_t)0ULL);
v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__4(v_sz_2289_, v___x_2290_, v___x_2288_);
v___x_2292_ = l_Lean_Name_toString(v_mainModuleName_2224_, v___x_2251_);
v___x_2293_ = l_Lean_Firefox_Profile_export(v___x_2292_, v___x_2250_, v___x_2291_, v___y_2256_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v___x_2291_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
v___x_2295_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2294_);
v___x_2296_ = l_Lean_Json_compress(v___x_2295_);
v___x_2297_ = l_Lean_Firefox_Profile_serve(v___x_2296_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_dec_ref_known(v___x_2297_, 1);
v___y_2238_ = v___y_2253_;
v___y_2239_ = v___y_2255_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v___y_2255_);
lean_dec_ref(v___y_2253_);
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v___y_2255_);
lean_dec_ref(v___y_2253_);
v_a_2306_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2293_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2293_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
}
v___jp_2316_:
{
lean_object* v_fileMap_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v_fst_2328_; lean_object* v_snd_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v_fileMap_2324_ = lean_ctor_get(v___x_2315_, 2);
lean_inc_ref(v_fileMap_2324_);
lean_dec_ref(v___x_2315_);
v___x_2325_ = 0;
v___x_2326_ = l_Lean_Server_findModuleRefs(v_fileMap_2324_, v___y_2323_, v___x_2325_, v___x_2325_);
lean_dec_ref(v___y_2323_);
v___x_2327_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_2326_);
v_fst_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_fst_2328_);
v_snd_2329_ = lean_ctor_get(v___x_2327_, 1);
lean_inc(v_snd_2329_);
lean_dec_ref(v___x_2327_);
v___x_2330_ = lean_unsigned_to_nat(5u);
v___x_2331_ = l_Lean_Server_collectImports(v___y_2317_);
lean_inc(v_mainModuleName_2224_);
v___x_2332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v_mainModuleName_2224_);
lean_ctor_set(v___x_2332_, 2, v___x_2331_);
lean_ctor_set(v___x_2332_, 3, v_fst_2328_);
lean_ctor_set(v___x_2332_, 4, v_snd_2329_);
v___x_2333_ = l_Lean_Server_instToJsonIlean_toJson(v___x_2332_);
v___x_2334_ = l_Lean_Json_compress(v___x_2333_);
v___x_2335_ = l_IO_FS_writeFile(v___y_2322_, v___x_2334_);
lean_dec_ref(v___x_2334_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_dec_ref_known(v___x_2335_, 1);
v___y_2253_ = v___y_2318_;
v___y_2254_ = v___y_2319_;
v___y_2255_ = v___y_2320_;
v___y_2256_ = v___y_2321_;
goto v___jp_2252_;
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v_mainModuleName_2224_);
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2335_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
v___jp_2344_:
{
if (lean_obj_tag(v_ileanFileName_x3f_2227_) == 1)
{
lean_object* v_val_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v_val_2351_ = lean_ctor_get(v_ileanFileName_x3f_2227_, 0);
lean_inc_ref(v___y_2348_);
v___x_2352_ = l_Lean_Language_SnapshotTree_getAll(v___y_2348_);
v___x_2353_ = lean_mk_empty_array_with_capacity(v___y_2350_);
v___x_2354_ = lean_array_get_size(v___x_2352_);
v___x_2355_ = lean_nat_dec_lt(v___y_2350_, v___x_2354_);
lean_dec(v___y_2350_);
if (v___x_2355_ == 0)
{
lean_dec_ref(v___x_2352_);
v___y_2317_ = v___y_2345_;
v___y_2318_ = v___y_2346_;
v___y_2319_ = v___y_2347_;
v___y_2320_ = v___y_2348_;
v___y_2321_ = v___y_2349_;
v___y_2322_ = v_val_2351_;
v___y_2323_ = v___x_2353_;
goto v___jp_2316_;
}
else
{
uint8_t v___x_2356_; 
v___x_2356_ = lean_nat_dec_le(v___x_2354_, v___x_2354_);
if (v___x_2356_ == 0)
{
if (v___x_2355_ == 0)
{
lean_dec_ref(v___x_2352_);
v___y_2317_ = v___y_2345_;
v___y_2318_ = v___y_2346_;
v___y_2319_ = v___y_2347_;
v___y_2320_ = v___y_2348_;
v___y_2321_ = v___y_2349_;
v___y_2322_ = v_val_2351_;
v___y_2323_ = v___x_2353_;
goto v___jp_2316_;
}
else
{
size_t v___x_2357_; size_t v___x_2358_; lean_object* v___x_2359_; 
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = lean_usize_of_nat(v___x_2354_);
v___x_2359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v___x_2352_, v___x_2357_, v___x_2358_, v___x_2353_);
lean_dec_ref(v___x_2352_);
v___y_2317_ = v___y_2345_;
v___y_2318_ = v___y_2346_;
v___y_2319_ = v___y_2347_;
v___y_2320_ = v___y_2348_;
v___y_2321_ = v___y_2349_;
v___y_2322_ = v_val_2351_;
v___y_2323_ = v___x_2359_;
goto v___jp_2316_;
}
}
else
{
size_t v___x_2360_; size_t v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = ((size_t)0ULL);
v___x_2361_ = lean_usize_of_nat(v___x_2354_);
v___x_2362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v___x_2352_, v___x_2360_, v___x_2361_, v___x_2353_);
lean_dec_ref(v___x_2352_);
v___y_2317_ = v___y_2345_;
v___y_2318_ = v___y_2346_;
v___y_2319_ = v___y_2347_;
v___y_2320_ = v___y_2348_;
v___y_2321_ = v___y_2349_;
v___y_2322_ = v_val_2351_;
v___y_2323_ = v___x_2362_;
goto v___jp_2316_;
}
}
}
else
{
lean_dec(v___y_2350_);
lean_dec(v___y_2345_);
lean_dec_ref(v___x_2315_);
v___y_2253_ = v___y_2346_;
v___y_2254_ = v___y_2347_;
v___y_2255_ = v___y_2348_;
v___y_2256_ = v___y_2349_;
goto v___jp_2252_;
}
}
v___jp_2363_:
{
if (v___y_2371_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_2226_) == 1)
{
lean_object* v_val_2374_; lean_object* v_fileMap_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___f_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_val_2374_ = lean_ctor_get(v_oleanFileName_x3f_2226_, 0);
lean_inc(v_val_2374_);
lean_dec_ref_known(v_oleanFileName_x3f_2226_, 1);
v_fileMap_2375_ = lean_ctor_get(v___x_2315_, 2);
lean_inc_ref(v_fileMap_2375_);
v___x_2376_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__4));
v___x_2377_ = lean_box(0);
v___x_2378_ = lean_mk_empty_array_with_capacity(v___y_2373_);
lean_inc_ref(v___y_2370_);
v___x_2379_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___y_2370_, v___x_2377_, v___x_2378_);
v___x_2380_ = lean_box(v___x_2251_);
v___x_2381_ = lean_box(v___y_2366_);
v___f_2382_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4___boxed), 8, 7);
lean_closure_set(v___f_2382_, 0, v_fileMap_2375_);
lean_closure_set(v___f_2382_, 1, v___y_2364_);
lean_closure_set(v___f_2382_, 2, v___x_2379_);
lean_closure_set(v___f_2382_, 3, v___y_2365_);
lean_closure_set(v___f_2382_, 4, v_val_2374_);
lean_closure_set(v___f_2382_, 5, v___x_2380_);
lean_closure_set(v___f_2382_, 6, v___x_2381_);
v___x_2383_ = lean_box(0);
v___x_2384_ = l_Lean_profileitIOUnsafe___redArg(v___x_2376_, v___y_2369_, v___f_2382_, v___x_2383_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_dec_ref_known(v___x_2384_, 1);
v___y_2345_ = v___y_2367_;
v___y_2346_ = v___y_2368_;
v___y_2347_ = v___y_2369_;
v___y_2348_ = v___y_2370_;
v___y_2349_ = v___y_2372_;
v___y_2350_ = v___y_2373_;
goto v___jp_2344_;
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec_ref(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___x_2315_);
lean_dec(v_mainModuleName_2224_);
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
lean_dec_ref(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v_oleanFileName_x3f_2226_);
v___y_2345_ = v___y_2367_;
v___y_2346_ = v___y_2368_;
v___y_2347_ = v___y_2369_;
v___y_2348_ = v___y_2370_;
v___y_2349_ = v___y_2372_;
v___y_2350_ = v___y_2373_;
goto v___jp_2344_;
}
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec_ref(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec_ref(v___x_2315_);
lean_dec(v_oleanFileName_x3f_2226_);
lean_dec(v_mainModuleName_2224_);
v___x_2393_ = lean_box(0);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
return v___x_2394_;
}
}
v___jp_2395_:
{
if (v_printStats_2231_ == 0)
{
v___y_2364_ = v___y_2396_;
v___y_2365_ = v___y_2397_;
v___y_2366_ = v___y_2398_;
v___y_2367_ = v___y_2399_;
v___y_2368_ = v___y_2400_;
v___y_2369_ = v___y_2401_;
v___y_2370_ = v___y_2403_;
v___y_2371_ = v___y_2402_;
v___y_2372_ = v___y_2404_;
v___y_2373_ = v___y_2405_;
goto v___jp_2363_;
}
else
{
lean_object* v___x_2406_; 
lean_inc_ref(v___y_2400_);
v___x_2406_ = l_Lean_Environment_displayStats(v___y_2400_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_dec_ref_known(v___x_2406_, 1);
v___y_2364_ = v___y_2396_;
v___y_2365_ = v___y_2397_;
v___y_2366_ = v___y_2398_;
v___y_2367_ = v___y_2399_;
v___y_2368_ = v___y_2400_;
v___y_2369_ = v___y_2401_;
v___y_2370_ = v___y_2403_;
v___y_2371_ = v___y_2402_;
v___y_2372_ = v___y_2404_;
v___y_2373_ = v___y_2405_;
goto v___jp_2363_;
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec_ref(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec_ref(v___x_2315_);
lean_dec(v_oleanFileName_x3f_2226_);
lean_dec(v_mainModuleName_2224_);
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
v___jp_2415_:
{
if (lean_obj_tag(v_incrHeaderSaveFileName_x3f_2235_) == 1)
{
lean_object* v_val_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_val_2427_ = lean_ctor_get(v_incrHeaderSaveFileName_x3f_2235_, 0);
lean_inc(v_val_2427_);
lean_dec_ref_known(v_incrHeaderSaveFileName_x3f_2235_, 1);
v___x_2428_ = l_Lean_Language_Lean_truncateToHeader(v___y_2421_);
v___x_2429_ = lean_apply_3(v___y_2417_, v_val_2427_, v___x_2428_, lean_box(0));
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_dec_ref_known(v___x_2429_, 1);
lean_inc_ref(v___y_2418_);
v___y_2396_ = v___y_2416_;
v___y_2397_ = v___y_2418_;
v___y_2398_ = v___y_2419_;
v___y_2399_ = v___y_2420_;
v___y_2400_ = v___y_2422_;
v___y_2401_ = v___y_2418_;
v___y_2402_ = v___y_2424_;
v___y_2403_ = v___y_2423_;
v___y_2404_ = v___y_2425_;
v___y_2405_ = v___y_2426_;
goto v___jp_2395_;
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec_ref(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2418_);
lean_dec_ref(v___y_2416_);
lean_dec_ref(v___x_2315_);
lean_dec(v_oleanFileName_x3f_2226_);
lean_dec(v_mainModuleName_2224_);
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
else
{
lean_dec_ref(v___y_2421_);
lean_dec_ref(v___y_2417_);
lean_dec(v_incrHeaderSaveFileName_x3f_2235_);
lean_inc_ref(v___y_2418_);
v___y_2396_ = v___y_2416_;
v___y_2397_ = v___y_2418_;
v___y_2398_ = v___y_2419_;
v___y_2399_ = v___y_2420_;
v___y_2400_ = v___y_2422_;
v___y_2401_ = v___y_2418_;
v___y_2402_ = v___y_2424_;
v___y_2403_ = v___y_2423_;
v___y_2404_ = v___y_2425_;
v___y_2405_ = v___y_2426_;
goto v___jp_2395_;
}
}
v___jp_2438_:
{
lean_object* v___x_2445_; 
lean_inc_ref(v___y_2441_);
v___x_2445_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_2441_, v___y_2442_, v_jsonOutput_2228_, v___y_2444_);
lean_dec(v___y_2444_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2476_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2476_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2476_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; 
lean_inc_ref(v___y_2440_);
v___x_2450_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___y_2440_);
if (lean_obj_tag(v___x_2450_) == 1)
{
lean_object* v_val_2451_; lean_object* v_env_2452_; lean_object* v_scopes_2453_; lean_object* v___x_2454_; lean_object* v_opts_2455_; lean_object* v___f_2456_; 
lean_del_object(v___x_2448_);
v_val_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_val_2451_);
lean_dec_ref_known(v___x_2450_, 1);
v_env_2452_ = lean_ctor_get(v_val_2451_, 0);
lean_inc_ref_n(v_env_2452_, 2);
v_scopes_2453_ = lean_ctor_get(v_val_2451_, 2);
lean_inc(v_scopes_2453_);
lean_dec(v_val_2451_);
lean_inc(v___y_2443_);
v___x_2454_ = l_List_get_x21Internal___redArg(v___x_2247_, v_scopes_2453_, v___y_2443_);
lean_dec(v_scopes_2453_);
v_opts_2455_ = lean_ctor_get(v___x_2454_, 1);
lean_inc_ref(v_opts_2455_);
lean_dec(v___x_2454_);
v___f_2456_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 4, 1);
lean_closure_set(v___f_2456_, 0, v_env_2452_);
if (lean_obj_tag(v_incrSaveFileName_x3f_2233_) == 1)
{
lean_object* v_val_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v_val_2457_ = lean_ctor_get(v_incrSaveFileName_x3f_2233_, 0);
lean_inc(v_val_2457_);
lean_dec_ref_known(v_incrSaveFileName_x3f_2233_, 1);
v___x_2458_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___y_2441_);
lean_inc_ref(v___y_2440_);
v___x_2459_ = l_Lean_Elab_runFrontend___lam__3(v_env_2452_, v_val_2457_, v___y_2440_);
if (lean_obj_tag(v___x_2459_) == 0)
{
uint8_t v___x_2460_; uint8_t v___x_2461_; 
lean_dec_ref_known(v___x_2459_, 1);
v___x_2460_ = lean_unbox(v_a_2446_);
v___x_2461_ = lean_unbox(v_a_2446_);
lean_dec(v_a_2446_);
lean_inc_ref(v_env_2452_);
v___y_2416_ = v_env_2452_;
v___y_2417_ = v___f_2456_;
v___y_2418_ = v_opts_2455_;
v___y_2419_ = v___x_2460_;
v___y_2420_ = v___y_2439_;
v___y_2421_ = v___y_2440_;
v___y_2422_ = v_env_2452_;
v___y_2423_ = v___y_2441_;
v___y_2424_ = v___x_2461_;
v___y_2425_ = v___y_2442_;
v___y_2426_ = v___y_2443_;
goto v___jp_2415_;
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v___f_2456_);
lean_dec_ref(v_opts_2455_);
lean_dec_ref(v_env_2452_);
lean_dec(v_a_2446_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___x_2315_);
lean_dec(v_incrHeaderSaveFileName_x3f_2235_);
lean_dec(v_oleanFileName_x3f_2226_);
lean_dec(v_mainModuleName_2224_);
v_a_2462_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2459_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2459_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
else
{
uint8_t v___x_2470_; uint8_t v___x_2471_; 
lean_dec(v_incrSaveFileName_x3f_2233_);
v___x_2470_ = lean_unbox(v_a_2446_);
v___x_2471_ = lean_unbox(v_a_2446_);
lean_dec(v_a_2446_);
lean_inc_ref(v_env_2452_);
v___y_2416_ = v_env_2452_;
v___y_2417_ = v___f_2456_;
v___y_2418_ = v_opts_2455_;
v___y_2419_ = v___x_2470_;
v___y_2420_ = v___y_2439_;
v___y_2421_ = v___y_2440_;
v___y_2422_ = v_env_2452_;
v___y_2423_ = v___y_2441_;
v___y_2424_ = v___x_2471_;
v___y_2425_ = v___y_2442_;
v___y_2426_ = v___y_2443_;
goto v___jp_2415_;
}
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v___x_2450_);
lean_dec(v_a_2446_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___x_2315_);
lean_dec(v_incrHeaderSaveFileName_x3f_2235_);
lean_dec(v_incrSaveFileName_x3f_2233_);
lean_dec(v_oleanFileName_x3f_2226_);
lean_dec(v_mainModuleName_2224_);
v___x_2472_ = lean_box(0);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2472_);
v___x_2474_ = v___x_2448_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___x_2315_);
lean_dec(v_incrHeaderSaveFileName_x3f_2235_);
lean_dec(v_incrSaveFileName_x3f_2233_);
lean_dec(v_oleanFileName_x3f_2226_);
lean_dec(v_mainModuleName_2224_);
v_a_2477_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2445_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2445_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
v___jp_2485_:
{
lean_object* v_stx_x3f_2492_; lean_object* v_reportingRange_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; 
v_stx_x3f_2492_ = lean_ctor_get(v___y_2488_, 0);
lean_inc(v_stx_x3f_2492_);
v_reportingRange_2493_ = lean_ctor_get(v___y_2488_, 1);
lean_inc(v_reportingRange_2493_);
v___x_2494_ = l_Lean_Language_SnapshotTask_map___redArg(v___y_2488_, v___f_2244_, v_stx_x3f_2492_, v_reportingRange_2493_, v___x_2251_);
v___x_2495_ = lean_unsigned_to_nat(1u);
v___x_2496_ = lean_mk_empty_array_with_capacity(v___x_2495_);
v___x_2497_ = lean_array_push(v___x_2496_, v___x_2494_);
v___x_2498_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2491_, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___y_2489_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_box(1);
v___x_2501_ = lean_unsigned_to_nat(0u);
v___x_2502_ = lean_array_get_size(v_errorOnKinds_2229_);
v___x_2503_ = lean_nat_dec_lt(v___x_2501_, v___x_2502_);
if (v___x_2503_ == 0)
{
v___y_2439_ = v___y_2486_;
v___y_2440_ = v___y_2487_;
v___y_2441_ = v___x_2499_;
v___y_2442_ = v___y_2490_;
v___y_2443_ = v___x_2501_;
v___y_2444_ = v___x_2500_;
goto v___jp_2438_;
}
else
{
uint8_t v___x_2504_; 
v___x_2504_ = lean_nat_dec_le(v___x_2502_, v___x_2502_);
if (v___x_2504_ == 0)
{
if (v___x_2503_ == 0)
{
v___y_2439_ = v___y_2486_;
v___y_2440_ = v___y_2487_;
v___y_2441_ = v___x_2499_;
v___y_2442_ = v___y_2490_;
v___y_2443_ = v___x_2501_;
v___y_2444_ = v___x_2500_;
goto v___jp_2438_;
}
else
{
size_t v___x_2505_; size_t v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = ((size_t)0ULL);
v___x_2506_ = lean_usize_of_nat(v___x_2502_);
v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_errorOnKinds_2229_, v___x_2505_, v___x_2506_, v___x_2500_);
v___y_2439_ = v___y_2486_;
v___y_2440_ = v___y_2487_;
v___y_2441_ = v___x_2499_;
v___y_2442_ = v___y_2490_;
v___y_2443_ = v___x_2501_;
v___y_2444_ = v___x_2507_;
goto v___jp_2438_;
}
}
else
{
size_t v___x_2508_; size_t v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = ((size_t)0ULL);
v___x_2509_ = lean_usize_of_nat(v___x_2502_);
v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_errorOnKinds_2229_, v___x_2508_, v___x_2509_, v___x_2500_);
v___y_2439_ = v___y_2486_;
v___y_2440_ = v___y_2487_;
v___y_2441_ = v___x_2499_;
v___y_2442_ = v___y_2490_;
v___y_2443_ = v___x_2501_;
v___y_2444_ = v___x_2510_;
goto v___jp_2438_;
}
}
}
v___jp_2511_:
{
lean_object* v___x_2515_; lean_object* v_result_x3f_2516_; 
v___x_2515_ = l_Lean_Language_Lean_process(v___y_2512_, v_a_2514_, v___x_2315_);
v_result_x3f_2516_ = lean_ctor_get(v___x_2515_, 4);
lean_inc(v_result_x3f_2516_);
if (lean_obj_tag(v_result_x3f_2516_) == 0)
{
lean_object* v_toSnapshot_2517_; lean_object* v_metaSnap_2518_; lean_object* v_stx_2519_; lean_object* v___x_2520_; 
v_toSnapshot_2517_ = lean_ctor_get(v___x_2515_, 0);
lean_inc_ref(v_toSnapshot_2517_);
v_metaSnap_2518_ = lean_ctor_get(v___x_2515_, 1);
lean_inc_ref(v_metaSnap_2518_);
v_stx_2519_ = lean_ctor_get(v___x_2515_, 3);
lean_inc(v_stx_2519_);
v___x_2520_ = lean_box(0);
v___y_2486_ = v_stx_2519_;
v___y_2487_ = v___x_2515_;
v___y_2488_ = v_metaSnap_2518_;
v___y_2489_ = v_toSnapshot_2517_;
v___y_2490_ = v___y_2513_;
v___y_2491_ = v___x_2520_;
goto v___jp_2485_;
}
else
{
lean_object* v_val_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2535_; 
v_val_2521_ = lean_ctor_get(v_result_x3f_2516_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_result_x3f_2516_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2523_ = v_result_x3f_2516_;
v_isShared_2524_ = v_isSharedCheck_2535_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_val_2521_);
lean_dec(v_result_x3f_2516_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2535_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v_processedSnap_2525_; lean_object* v_toSnapshot_2526_; lean_object* v_metaSnap_2527_; lean_object* v_stx_2528_; lean_object* v_stx_x3f_2529_; lean_object* v_reportingRange_2530_; lean_object* v___x_2531_; lean_object* v___x_2533_; 
v_processedSnap_2525_ = lean_ctor_get(v_val_2521_, 1);
lean_inc_ref(v_processedSnap_2525_);
lean_dec(v_val_2521_);
v_toSnapshot_2526_ = lean_ctor_get(v___x_2515_, 0);
lean_inc_ref(v_toSnapshot_2526_);
v_metaSnap_2527_ = lean_ctor_get(v___x_2515_, 1);
lean_inc_ref(v_metaSnap_2527_);
v_stx_2528_ = lean_ctor_get(v___x_2515_, 3);
lean_inc(v_stx_2528_);
v_stx_x3f_2529_ = lean_ctor_get(v_processedSnap_2525_, 0);
lean_inc(v_stx_x3f_2529_);
v_reportingRange_2530_ = lean_ctor_get(v_processedSnap_2525_, 1);
lean_inc(v_reportingRange_2530_);
v___x_2531_ = l_Lean_Language_SnapshotTask_map___redArg(v_processedSnap_2525_, v___f_2245_, v_stx_x3f_2529_, v_reportingRange_2530_, v___x_2251_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v___x_2531_);
v___x_2533_ = v___x_2523_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
v___y_2486_ = v_stx_2528_;
v___y_2487_ = v___x_2515_;
v___y_2488_ = v_metaSnap_2527_;
v___y_2489_ = v_toSnapshot_2526_;
v___y_2490_ = v___y_2513_;
v___y_2491_ = v___x_2533_;
goto v___jp_2485_;
}
}
}
}
v___jp_2536_:
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2540_, 0, v_a_2539_);
v___y_2512_ = v___y_2537_;
v___y_2513_ = v___y_2538_;
v_a_2514_ = v___x_2540_;
goto v___jp_2511_;
}
v___jp_2542_:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___f_2549_; 
v___x_2544_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2222_, v___x_2541_, v___y_2543_);
v___x_2545_ = l_Lean_Elab_async;
v___x_2546_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_2544_, v___x_2545_, v___x_2251_);
v___x_2547_ = lean_box_uint32(v_trustLevel_2225_);
v___x_2548_ = lean_box(v___x_2251_);
lean_inc(v_mainModuleName_2224_);
lean_inc_ref(v___x_2546_);
v___f_2549_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__5___boxed), 10, 7);
lean_closure_set(v___f_2549_, 0, v_setup_x3f_2232_);
lean_closure_set(v___f_2549_, 1, v___f_2246_);
lean_closure_set(v___f_2549_, 2, v___x_2546_);
lean_closure_set(v___f_2549_, 3, v_plugins_2230_);
lean_closure_set(v___f_2549_, 4, v___x_2547_);
lean_closure_set(v___f_2549_, 5, v___x_2548_);
lean_closure_set(v___f_2549_, 6, v_mainModuleName_2224_);
if (lean_obj_tag(v_incrLoadFileName_x3f_2234_) == 0)
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_box(0);
v___y_2512_ = v___f_2549_;
v___y_2513_ = v___x_2546_;
v_a_2514_ = v___x_2550_;
goto v___jp_2511_;
}
else
{
lean_object* v_val_2551_; lean_object* v___x_2552_; 
v_val_2551_ = lean_ctor_get(v_incrLoadFileName_x3f_2234_, 0);
lean_inc(v_val_2551_);
lean_dec_ref_known(v_incrLoadFileName_x3f_2234_, 1);
v___x_2552_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_val_2551_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v_snap_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v_snap_2554_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_mainModuleName_2224_);
lean_inc_ref(v_snap_2554_);
v___x_2555_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(v_snap_2554_, v_mainModuleName_2224_);
lean_inc_ref(v___x_2555_);
v___x_2556_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v___x_2555_);
v___x_2557_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_2556_);
if (lean_obj_tag(v___x_2557_) == 1)
{
lean_object* v_val_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v_val_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_val_2558_);
lean_dec_ref_known(v___x_2557_, 1);
lean_inc_ref(v___x_2546_);
v___x_2559_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed), 4, 3);
lean_closure_set(v___x_2559_, 0, v___x_2546_);
lean_closure_set(v___x_2559_, 1, v_a_2553_);
lean_closure_set(v___x_2559_, 2, v_val_2558_);
v___x_2560_ = l_Lean_withImporting___redArg(v___x_2559_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v___x_2561_; 
lean_dec_ref_known(v___x_2560_, 1);
v___x_2561_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_dec_ref_known(v___x_2561_, 1);
v___y_2537_ = v___f_2549_;
v___y_2538_ = v___x_2546_;
v_a_2539_ = v___x_2555_;
goto v___jp_2536_;
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec_ref(v___x_2555_);
lean_dec_ref(v___f_2549_);
lean_dec_ref(v___x_2546_);
lean_dec_ref(v___x_2315_);
lean_dec(v_incrHeaderSaveFileName_x3f_2235_);
lean_dec(v_incrSaveFileName_x3f_2233_);
lean_dec(v_oleanFileName_x3f_2226_);
lean_dec(v_mainModuleName_2224_);
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec_ref(v___x_2555_);
lean_dec_ref(v___f_2549_);
lean_dec_ref(v___x_2546_);
lean_dec_ref(v___x_2315_);
lean_dec(v_incrHeaderSaveFileName_x3f_2235_);
lean_dec(v_incrSaveFileName_x3f_2233_);
lean_dec(v_oleanFileName_x3f_2226_);
lean_dec(v_mainModuleName_2224_);
v_a_2570_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2560_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2560_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
else
{
lean_dec(v___x_2557_);
lean_dec(v_a_2553_);
v___y_2537_ = v___f_2549_;
v___y_2538_ = v___x_2546_;
v_a_2539_ = v___x_2555_;
goto v___jp_2536_;
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec_ref(v___f_2549_);
lean_dec_ref(v___x_2546_);
lean_dec_ref(v___x_2315_);
lean_dec(v_incrHeaderSaveFileName_x3f_2235_);
lean_dec(v_incrSaveFileName_x3f_2233_);
lean_dec(v_oleanFileName_x3f_2226_);
lean_dec(v_mainModuleName_2224_);
v_a_2578_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2552_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2552_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_2587_, lean_object* v_opts_2588_, lean_object* v_fileName_2589_, lean_object* v_mainModuleName_2590_, lean_object* v_trustLevel_2591_, lean_object* v_oleanFileName_x3f_2592_, lean_object* v_ileanFileName_x3f_2593_, lean_object* v_jsonOutput_2594_, lean_object* v_errorOnKinds_2595_, lean_object* v_plugins_2596_, lean_object* v_printStats_2597_, lean_object* v_setup_x3f_2598_, lean_object* v_incrSaveFileName_x3f_2599_, lean_object* v_incrLoadFileName_x3f_2600_, lean_object* v_incrHeaderSaveFileName_x3f_2601_, lean_object* v_a_2602_){
_start:
{
uint32_t v_trustLevel_boxed_2603_; uint8_t v_jsonOutput_boxed_2604_; uint8_t v_printStats_boxed_2605_; lean_object* v_res_2606_; 
v_trustLevel_boxed_2603_ = lean_unbox_uint32(v_trustLevel_2591_);
lean_dec(v_trustLevel_2591_);
v_jsonOutput_boxed_2604_ = lean_unbox(v_jsonOutput_2594_);
v_printStats_boxed_2605_ = lean_unbox(v_printStats_2597_);
v_res_2606_ = l_Lean_Elab_runFrontend(v_input_2587_, v_opts_2588_, v_fileName_2589_, v_mainModuleName_2590_, v_trustLevel_boxed_2603_, v_oleanFileName_x3f_2592_, v_ileanFileName_x3f_2593_, v_jsonOutput_boxed_2604_, v_errorOnKinds_2595_, v_plugins_2596_, v_printStats_boxed_2605_, v_setup_x3f_2598_, v_incrSaveFileName_x3f_2599_, v_incrLoadFileName_x3f_2600_, v_incrHeaderSaveFileName_x3f_2601_);
lean_dec_ref(v_errorOnKinds_2595_);
lean_dec(v_ileanFileName_x3f_2593_);
return v_res_2606_;
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
