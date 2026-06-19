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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Linter_recordLints(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Lean_writeModule(lean_object*, lean_object*, uint8_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* l_Lean_Options_mergeBy(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object*);
uint8_t lean_strict_or(uint8_t, uint8_t);
lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*, uint8_t);
lean_object* lean_enable_initializer_execution();
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_compacted_region_save(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Language_Lean_pushOpt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_getRegularInitAttrModIdxs(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_runtime_forget(lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 0, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "server"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "olean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5_value;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_snap"};
static const lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14___closed__0 = (const lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 190, 236, 193, 206, 64, 207, 210)}};
static const lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14___closed__1 = (const lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_runFrontend___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_runFrontend___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object*);
static const lean_closure_object l_Lean_Elab_runFrontend___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Elab_runFrontend_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Elab_runFrontend_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_runFrontend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__0_value;
static const lean_closure_object l_Lean_Elab_runFrontend___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__1 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__1_value;
static const lean_closure_object l_Lean_Elab_runFrontend___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__2, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_runFrontend___closed__1_value)} };
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
lean_object* v_lean_x3f_780_; lean_object* v_olean_x3f_781_; lean_object* v_oleanPrivate_x3f_782_; lean_object* v_ilean_x3f_783_; lean_object* v_ir_x3f_784_; lean_object* v_c_x3f_785_; lean_object* v_bc_x3f_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_794_; 
v_lean_x3f_780_ = lean_ctor_get(v_a_779_, 0);
v_olean_x3f_781_ = lean_ctor_get(v_a_779_, 1);
v_oleanPrivate_x3f_782_ = lean_ctor_get(v_a_779_, 3);
v_ilean_x3f_783_ = lean_ctor_get(v_a_779_, 4);
v_ir_x3f_784_ = lean_ctor_get(v_a_779_, 5);
v_c_x3f_785_ = lean_ctor_get(v_a_779_, 6);
v_bc_x3f_786_ = lean_ctor_get(v_a_779_, 7);
v_isSharedCheck_794_ = !lean_is_exclusive(v_a_779_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_a_779_, 2);
lean_dec(v_unused_795_);
v___x_788_ = v_a_779_;
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_bc_x3f_786_);
lean_inc(v_c_x3f_785_);
lean_inc(v_ir_x3f_784_);
lean_inc(v_ilean_x3f_783_);
lean_inc(v_oleanPrivate_x3f_782_);
lean_inc(v_olean_x3f_781_);
lean_inc(v_lean_x3f_780_);
lean_dec(v_a_779_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v_filePath_778_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 2, v___x_790_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_lean_x3f_780_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_olean_x3f_781_);
lean_ctor_set(v_reuseFailAlloc_793_, 2, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_793_, 3, v_oleanPrivate_x3f_782_);
lean_ctor_set(v_reuseFailAlloc_793_, 4, v_ilean_x3f_783_);
lean_ctor_set(v_reuseFailAlloc_793_, 5, v_ir_x3f_784_);
lean_ctor_set(v_reuseFailAlloc_793_, 6, v_c_x3f_785_);
lean_ctor_set(v_reuseFailAlloc_793_, 7, v_bc_x3f_786_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1(lean_object* v_filePath_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_lean_x3f_798_; lean_object* v_olean_x3f_799_; lean_object* v_oleanServer_x3f_800_; lean_object* v_oleanPrivate_x3f_801_; lean_object* v_ilean_x3f_802_; lean_object* v_c_x3f_803_; lean_object* v_bc_x3f_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_812_; 
v_lean_x3f_798_ = lean_ctor_get(v_a_797_, 0);
v_olean_x3f_799_ = lean_ctor_get(v_a_797_, 1);
v_oleanServer_x3f_800_ = lean_ctor_get(v_a_797_, 2);
v_oleanPrivate_x3f_801_ = lean_ctor_get(v_a_797_, 3);
v_ilean_x3f_802_ = lean_ctor_get(v_a_797_, 4);
v_c_x3f_803_ = lean_ctor_get(v_a_797_, 6);
v_bc_x3f_804_ = lean_ctor_get(v_a_797_, 7);
v_isSharedCheck_812_ = !lean_is_exclusive(v_a_797_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_a_797_, 5);
lean_dec(v_unused_813_);
v___x_806_ = v_a_797_;
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_bc_x3f_804_);
lean_inc(v_c_x3f_803_);
lean_inc(v_ilean_x3f_802_);
lean_inc(v_oleanPrivate_x3f_801_);
lean_inc(v_oleanServer_x3f_800_);
lean_inc(v_olean_x3f_799_);
lean_inc(v_lean_x3f_798_);
lean_dec(v_a_797_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v_filePath_796_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 5, v___x_808_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_lean_x3f_798_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_olean_x3f_799_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v_oleanServer_x3f_800_);
lean_ctor_set(v_reuseFailAlloc_811_, 3, v_oleanPrivate_x3f_801_);
lean_ctor_set(v_reuseFailAlloc_811_, 4, v_ilean_x3f_802_);
lean_ctor_set(v_reuseFailAlloc_811_, 5, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_811_, 6, v_c_x3f_803_);
lean_ctor_set(v_reuseFailAlloc_811_, 7, v_bc_x3f_804_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(lean_object* v_a_814_, lean_object* v_x_815_){
_start:
{
if (lean_obj_tag(v_x_815_) == 0)
{
uint8_t v___x_816_; 
v___x_816_ = 0;
return v___x_816_;
}
else
{
lean_object* v_key_817_; lean_object* v_tail_818_; uint8_t v___x_819_; 
v_key_817_ = lean_ctor_get(v_x_815_, 0);
v_tail_818_ = lean_ctor_get(v_x_815_, 2);
v___x_819_ = lean_string_dec_eq(v_key_817_, v_a_814_);
if (v___x_819_ == 0)
{
v_x_815_ = v_tail_818_;
goto _start;
}
else
{
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg___boxed(lean_object* v_a_821_, lean_object* v_x_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_821_, v_x_822_);
lean_dec(v_x_822_);
lean_dec_ref(v_a_821_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(lean_object* v_m_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_buckets_827_; lean_object* v___x_828_; uint64_t v___x_829_; uint64_t v___x_830_; uint64_t v___x_831_; uint64_t v_fold_832_; uint64_t v___x_833_; uint64_t v___x_834_; uint64_t v___x_835_; size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_buckets_827_ = lean_ctor_get(v_m_825_, 1);
v___x_828_ = lean_array_get_size(v_buckets_827_);
v___x_829_ = lean_string_hash(v_a_826_);
v___x_830_ = 32ULL;
v___x_831_ = lean_uint64_shift_right(v___x_829_, v___x_830_);
v_fold_832_ = lean_uint64_xor(v___x_829_, v___x_831_);
v___x_833_ = 16ULL;
v___x_834_ = lean_uint64_shift_right(v_fold_832_, v___x_833_);
v___x_835_ = lean_uint64_xor(v_fold_832_, v___x_834_);
v___x_836_ = lean_uint64_to_usize(v___x_835_);
v___x_837_ = lean_usize_of_nat(v___x_828_);
v___x_838_ = ((size_t)1ULL);
v___x_839_ = lean_usize_sub(v___x_837_, v___x_838_);
v___x_840_ = lean_usize_land(v___x_836_, v___x_839_);
v___x_841_ = lean_array_uget_borrowed(v_buckets_827_, v___x_840_);
v___x_842_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_826_, v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg___boxed(lean_object* v_m_843_, lean_object* v_a_844_){
_start:
{
uint8_t v_res_845_; lean_object* v_r_846_; 
v_res_845_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_843_, v_a_844_);
lean_dec_ref(v_a_844_);
lean_dec_ref(v_m_843_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(lean_object* v_a_847_, lean_object* v_fallback_848_, lean_object* v_x_849_){
_start:
{
if (lean_obj_tag(v_x_849_) == 0)
{
lean_inc(v_fallback_848_);
return v_fallback_848_;
}
else
{
lean_object* v_key_850_; lean_object* v_value_851_; lean_object* v_tail_852_; uint8_t v___x_853_; 
v_key_850_ = lean_ctor_get(v_x_849_, 0);
v_value_851_ = lean_ctor_get(v_x_849_, 1);
v_tail_852_ = lean_ctor_get(v_x_849_, 2);
v___x_853_ = lean_string_dec_eq(v_key_850_, v_a_847_);
if (v___x_853_ == 0)
{
v_x_849_ = v_tail_852_;
goto _start;
}
else
{
lean_inc(v_value_851_);
return v_value_851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg___boxed(lean_object* v_a_855_, lean_object* v_fallback_856_, lean_object* v_x_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_855_, v_fallback_856_, v_x_857_);
lean_dec(v_x_857_);
lean_dec(v_fallback_856_);
lean_dec_ref(v_a_855_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(lean_object* v_m_859_, lean_object* v_a_860_, lean_object* v_fallback_861_){
_start:
{
lean_object* v_buckets_862_; lean_object* v___x_863_; uint64_t v___x_864_; uint64_t v___x_865_; uint64_t v___x_866_; uint64_t v_fold_867_; uint64_t v___x_868_; uint64_t v___x_869_; uint64_t v___x_870_; size_t v___x_871_; size_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_buckets_862_ = lean_ctor_get(v_m_859_, 1);
v___x_863_ = lean_array_get_size(v_buckets_862_);
v___x_864_ = lean_string_hash(v_a_860_);
v___x_865_ = 32ULL;
v___x_866_ = lean_uint64_shift_right(v___x_864_, v___x_865_);
v_fold_867_ = lean_uint64_xor(v___x_864_, v___x_866_);
v___x_868_ = 16ULL;
v___x_869_ = lean_uint64_shift_right(v_fold_867_, v___x_868_);
v___x_870_ = lean_uint64_xor(v_fold_867_, v___x_869_);
v___x_871_ = lean_uint64_to_usize(v___x_870_);
v___x_872_ = lean_usize_of_nat(v___x_863_);
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_sub(v___x_872_, v___x_873_);
v___x_875_ = lean_usize_land(v___x_871_, v___x_874_);
v___x_876_ = lean_array_uget_borrowed(v_buckets_862_, v___x_875_);
v___x_877_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_860_, v_fallback_861_, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg___boxed(lean_object* v_m_878_, lean_object* v_a_879_, lean_object* v_fallback_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_878_, v_a_879_, v_fallback_880_);
lean_dec(v_fallback_880_);
lean_dec_ref(v_a_879_);
lean_dec_ref(v_m_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2(lean_object* v_filePath_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_lean_x3f_884_; lean_object* v_olean_x3f_885_; lean_object* v_oleanServer_x3f_886_; lean_object* v_ilean_x3f_887_; lean_object* v_ir_x3f_888_; lean_object* v_c_x3f_889_; lean_object* v_bc_x3f_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_898_; 
v_lean_x3f_884_ = lean_ctor_get(v_a_883_, 0);
v_olean_x3f_885_ = lean_ctor_get(v_a_883_, 1);
v_oleanServer_x3f_886_ = lean_ctor_get(v_a_883_, 2);
v_ilean_x3f_887_ = lean_ctor_get(v_a_883_, 4);
v_ir_x3f_888_ = lean_ctor_get(v_a_883_, 5);
v_c_x3f_889_ = lean_ctor_get(v_a_883_, 6);
v_bc_x3f_890_ = lean_ctor_get(v_a_883_, 7);
v_isSharedCheck_898_ = !lean_is_exclusive(v_a_883_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_a_883_, 3);
lean_dec(v_unused_899_);
v___x_892_ = v_a_883_;
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_bc_x3f_890_);
lean_inc(v_c_x3f_889_);
lean_inc(v_ir_x3f_888_);
lean_inc(v_ilean_x3f_887_);
lean_inc(v_oleanServer_x3f_886_);
lean_inc(v_olean_x3f_885_);
lean_inc(v_lean_x3f_884_);
lean_dec(v_a_883_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_894_, 0, v_filePath_882_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 3, v___x_894_);
v___x_896_ = v___x_892_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_lean_x3f_884_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_olean_x3f_885_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_oleanServer_x3f_886_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_897_, 4, v_ilean_x3f_887_);
lean_ctor_set(v_reuseFailAlloc_897_, 5, v_ir_x3f_888_);
lean_ctor_set(v_reuseFailAlloc_897_, 6, v_c_x3f_889_);
lean_ctor_set(v_reuseFailAlloc_897_, 7, v_bc_x3f_890_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0(lean_object* v_filePath_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_lean_x3f_902_; lean_object* v_oleanServer_x3f_903_; lean_object* v_oleanPrivate_x3f_904_; lean_object* v_ilean_x3f_905_; lean_object* v_ir_x3f_906_; lean_object* v_c_x3f_907_; lean_object* v_bc_x3f_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_916_; 
v_lean_x3f_902_ = lean_ctor_get(v_a_901_, 0);
v_oleanServer_x3f_903_ = lean_ctor_get(v_a_901_, 2);
v_oleanPrivate_x3f_904_ = lean_ctor_get(v_a_901_, 3);
v_ilean_x3f_905_ = lean_ctor_get(v_a_901_, 4);
v_ir_x3f_906_ = lean_ctor_get(v_a_901_, 5);
v_c_x3f_907_ = lean_ctor_get(v_a_901_, 6);
v_bc_x3f_908_ = lean_ctor_get(v_a_901_, 7);
v_isSharedCheck_916_ = !lean_is_exclusive(v_a_901_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v_a_901_, 1);
lean_dec(v_unused_917_);
v___x_910_ = v_a_901_;
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_bc_x3f_908_);
lean_inc(v_c_x3f_907_);
lean_inc(v_ir_x3f_906_);
lean_inc(v_ilean_x3f_905_);
lean_inc(v_oleanPrivate_x3f_904_);
lean_inc(v_oleanServer_x3f_903_);
lean_inc(v_lean_x3f_902_);
lean_dec(v_a_901_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v_filePath_900_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v___x_912_);
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_lean_x3f_902_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_oleanServer_x3f_903_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_oleanPrivate_x3f_904_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v_ilean_x3f_905_);
lean_ctor_set(v_reuseFailAlloc_915_, 5, v_ir_x3f_906_);
lean_ctor_set(v_reuseFailAlloc_915_, 6, v_c_x3f_907_);
lean_ctor_set(v_reuseFailAlloc_915_, 7, v_bc_x3f_908_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(lean_object* v_a_918_, lean_object* v_b_919_, lean_object* v_x_920_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
lean_dec(v_b_919_);
lean_dec_ref(v_a_918_);
return v_x_920_;
}
else
{
lean_object* v_key_921_; lean_object* v_value_922_; lean_object* v_tail_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_935_; 
v_key_921_ = lean_ctor_get(v_x_920_, 0);
v_value_922_ = lean_ctor_get(v_x_920_, 1);
v_tail_923_ = lean_ctor_get(v_x_920_, 2);
v_isSharedCheck_935_ = !lean_is_exclusive(v_x_920_);
if (v_isSharedCheck_935_ == 0)
{
v___x_925_ = v_x_920_;
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_tail_923_);
lean_inc(v_value_922_);
lean_inc(v_key_921_);
lean_dec(v_x_920_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
uint8_t v___x_927_; 
v___x_927_ = lean_string_dec_eq(v_key_921_, v_a_918_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_918_, v_b_919_, v_tail_923_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 2, v___x_928_);
v___x_930_ = v___x_925_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_key_921_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_value_922_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
else
{
lean_object* v___x_933_; 
lean_dec(v_value_922_);
lean_dec(v_key_921_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v_b_919_);
lean_ctor_set(v___x_925_, 0, v_a_918_);
v___x_933_ = v___x_925_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_918_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_b_919_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_tail_923_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
if (lean_obj_tag(v_x_937_) == 0)
{
return v_x_936_;
}
else
{
lean_object* v_key_938_; lean_object* v_value_939_; lean_object* v_tail_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_963_; 
v_key_938_ = lean_ctor_get(v_x_937_, 0);
v_value_939_ = lean_ctor_get(v_x_937_, 1);
v_tail_940_ = lean_ctor_get(v_x_937_, 2);
v_isSharedCheck_963_ = !lean_is_exclusive(v_x_937_);
if (v_isSharedCheck_963_ == 0)
{
v___x_942_ = v_x_937_;
v_isShared_943_ = v_isSharedCheck_963_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_tail_940_);
lean_inc(v_value_939_);
lean_inc(v_key_938_);
lean_dec(v_x_937_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_963_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; uint64_t v___x_945_; uint64_t v___x_946_; uint64_t v___x_947_; uint64_t v_fold_948_; uint64_t v___x_949_; uint64_t v___x_950_; uint64_t v___x_951_; size_t v___x_952_; size_t v___x_953_; size_t v___x_954_; size_t v___x_955_; size_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_944_ = lean_array_get_size(v_x_936_);
v___x_945_ = lean_string_hash(v_key_938_);
v___x_946_ = 32ULL;
v___x_947_ = lean_uint64_shift_right(v___x_945_, v___x_946_);
v_fold_948_ = lean_uint64_xor(v___x_945_, v___x_947_);
v___x_949_ = 16ULL;
v___x_950_ = lean_uint64_shift_right(v_fold_948_, v___x_949_);
v___x_951_ = lean_uint64_xor(v_fold_948_, v___x_950_);
v___x_952_ = lean_uint64_to_usize(v___x_951_);
v___x_953_ = lean_usize_of_nat(v___x_944_);
v___x_954_ = ((size_t)1ULL);
v___x_955_ = lean_usize_sub(v___x_953_, v___x_954_);
v___x_956_ = lean_usize_land(v___x_952_, v___x_955_);
v___x_957_ = lean_array_uget_borrowed(v_x_936_, v___x_956_);
lean_inc(v___x_957_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 2, v___x_957_);
v___x_959_ = v___x_942_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_key_938_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_value_939_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v___x_957_);
v___x_959_ = v_reuseFailAlloc_962_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; 
v___x_960_ = lean_array_uset(v_x_936_, v___x_956_, v___x_959_);
v_x_936_ = v___x_960_;
v_x_937_ = v_tail_940_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(lean_object* v_i_964_, lean_object* v_source_965_, lean_object* v_target_966_){
_start:
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = lean_array_get_size(v_source_965_);
v___x_968_ = lean_nat_dec_lt(v_i_964_, v___x_967_);
if (v___x_968_ == 0)
{
lean_dec_ref(v_source_965_);
lean_dec(v_i_964_);
return v_target_966_;
}
else
{
lean_object* v_es_969_; lean_object* v___x_970_; lean_object* v_source_971_; lean_object* v_target_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_es_969_ = lean_array_fget(v_source_965_, v_i_964_);
v___x_970_ = lean_box(0);
v_source_971_ = lean_array_fset(v_source_965_, v_i_964_, v___x_970_);
v_target_972_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_target_966_, v_es_969_);
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = lean_nat_add(v_i_964_, v___x_973_);
lean_dec(v_i_964_);
v_i_964_ = v___x_974_;
v_source_965_ = v_source_971_;
v_target_966_ = v_target_972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(lean_object* v_data_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v_nbuckets_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_977_ = lean_array_get_size(v_data_976_);
v___x_978_ = lean_unsigned_to_nat(2u);
v_nbuckets_979_ = lean_nat_mul(v___x_977_, v___x_978_);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_box(0);
v___x_982_ = lean_mk_array(v_nbuckets_979_, v___x_981_);
v___x_983_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v___x_980_, v_data_976_, v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object* v_m_984_, lean_object* v_a_985_, lean_object* v_b_986_){
_start:
{
lean_object* v_size_987_; lean_object* v_buckets_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1031_; 
v_size_987_ = lean_ctor_get(v_m_984_, 0);
v_buckets_988_ = lean_ctor_get(v_m_984_, 1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_m_984_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_990_ = v_m_984_;
v_isShared_991_ = v_isSharedCheck_1031_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_buckets_988_);
lean_inc(v_size_987_);
lean_dec(v_m_984_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1031_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; uint64_t v___x_993_; uint64_t v___x_994_; uint64_t v___x_995_; uint64_t v_fold_996_; uint64_t v___x_997_; uint64_t v___x_998_; uint64_t v___x_999_; size_t v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; lean_object* v_bkt_1005_; uint8_t v___x_1006_; 
v___x_992_ = lean_array_get_size(v_buckets_988_);
v___x_993_ = lean_string_hash(v_a_985_);
v___x_994_ = 32ULL;
v___x_995_ = lean_uint64_shift_right(v___x_993_, v___x_994_);
v_fold_996_ = lean_uint64_xor(v___x_993_, v___x_995_);
v___x_997_ = 16ULL;
v___x_998_ = lean_uint64_shift_right(v_fold_996_, v___x_997_);
v___x_999_ = lean_uint64_xor(v_fold_996_, v___x_998_);
v___x_1000_ = lean_uint64_to_usize(v___x_999_);
v___x_1001_ = lean_usize_of_nat(v___x_992_);
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_sub(v___x_1001_, v___x_1002_);
v___x_1004_ = lean_usize_land(v___x_1000_, v___x_1003_);
v_bkt_1005_ = lean_array_uget_borrowed(v_buckets_988_, v___x_1004_);
v___x_1006_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_985_, v_bkt_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v_size_x27_1008_; lean_object* v___x_1009_; lean_object* v_buckets_x27_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1007_ = lean_unsigned_to_nat(1u);
v_size_x27_1008_ = lean_nat_add(v_size_987_, v___x_1007_);
lean_dec(v_size_987_);
lean_inc(v_bkt_1005_);
v___x_1009_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1009_, 0, v_a_985_);
lean_ctor_set(v___x_1009_, 1, v_b_986_);
lean_ctor_set(v___x_1009_, 2, v_bkt_1005_);
v_buckets_x27_1010_ = lean_array_uset(v_buckets_988_, v___x_1004_, v___x_1009_);
v___x_1011_ = lean_unsigned_to_nat(4u);
v___x_1012_ = lean_nat_mul(v_size_x27_1008_, v___x_1011_);
v___x_1013_ = lean_unsigned_to_nat(3u);
v___x_1014_ = lean_nat_div(v___x_1012_, v___x_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_array_get_size(v_buckets_x27_1010_);
v___x_1016_ = lean_nat_dec_le(v___x_1014_, v___x_1015_);
lean_dec(v___x_1014_);
if (v___x_1016_ == 0)
{
lean_object* v_val_1017_; lean_object* v___x_1019_; 
v_val_1017_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_buckets_x27_1010_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v_val_1017_);
lean_ctor_set(v___x_990_, 0, v_size_x27_1008_);
v___x_1019_ = v___x_990_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_size_x27_1008_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_val_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
else
{
lean_object* v___x_1022_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v_buckets_x27_1010_);
lean_ctor_set(v___x_990_, 0, v_size_x27_1008_);
v___x_1022_ = v___x_990_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_size_x27_1008_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_buckets_x27_1010_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
else
{
lean_object* v___x_1024_; lean_object* v_buckets_x27_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
lean_inc(v_bkt_1005_);
v___x_1024_ = lean_box(0);
v_buckets_x27_1025_ = lean_array_uset(v_buckets_988_, v___x_1004_, v___x_1024_);
v___x_1026_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_985_, v_b_986_, v_bkt_1005_);
v___x_1027_ = lean_array_uset(v_buckets_x27_1025_, v___x_1004_, v___x_1026_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v___x_1027_);
v___x_1029_ = v___x_990_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_size_987_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object* v_as_1039_, size_t v_sz_1040_, size_t v_i_1041_, lean_object* v_b_1042_){
_start:
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_usize_dec_lt(v_i_1041_, v_sz_1040_);
if (v___x_1043_ == 0)
{
return v_b_1042_;
}
else
{
lean_object* v_fst_1044_; lean_object* v_snd_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1088_; 
v_fst_1044_ = lean_ctor_get(v_b_1042_, 0);
v_snd_1045_ = lean_ctor_get(v_b_1042_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_b_1042_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1047_ = v_b_1042_;
v_isShared_1048_ = v_isSharedCheck_1088_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_snd_1045_);
lean_inc(v_fst_1044_);
lean_dec(v_b_1042_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1088_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v_order_1052_; lean_object* v_fst_1064_; lean_object* v_snd_1065_; lean_object* v_a_1068_; lean_object* v_filePath_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; 
v_a_1068_ = lean_array_uget_borrowed(v_as_1039_, v_i_1041_);
v_filePath_1069_ = lean_ctor_get(v_a_1068_, 0);
lean_inc_ref_n(v_filePath_1069_, 2);
v___f_1070_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1070_, 0, v_filePath_1069_);
v___x_1071_ = l_System_FilePath_extension(v_filePath_1069_);
if (lean_obj_tag(v___x_1071_) == 1)
{
lean_object* v_val_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_val_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_val_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1));
v___x_1074_ = lean_string_dec_eq(v_val_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2));
v___x_1076_ = lean_string_dec_eq(v_val_1072_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3));
v___x_1078_ = lean_string_dec_eq(v_val_1072_, v___x_1077_);
lean_dec(v_val_1072_);
if (v___x_1078_ == 0)
{
lean_inc_ref(v_filePath_1069_);
v_fst_1064_ = v_filePath_1069_;
v_snd_1065_ = v___f_1070_;
goto v___jp_1063_;
}
else
{
lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref(v___f_1070_);
lean_inc_ref_n(v_filePath_1069_, 2);
v___f_1079_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1), 2, 1);
lean_closure_set(v___f_1079_, 0, v_filePath_1069_);
v___x_1080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4));
v___x_1081_ = l_System_FilePath_withExtension(v_filePath_1069_, v___x_1080_);
v_fst_1064_ = v___x_1081_;
v_snd_1065_ = v___f_1079_;
goto v___jp_1063_;
}
}
else
{
lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v_val_1072_);
lean_dec_ref(v___f_1070_);
lean_inc_ref_n(v_filePath_1069_, 2);
v___f_1082_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2), 2, 1);
lean_closure_set(v___f_1082_, 0, v_filePath_1069_);
v___x_1083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1084_ = l_System_FilePath_withExtension(v_filePath_1069_, v___x_1083_);
v_fst_1064_ = v___x_1084_;
v_snd_1065_ = v___f_1082_;
goto v___jp_1063_;
}
}
else
{
lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec(v_val_1072_);
lean_dec_ref(v___f_1070_);
lean_inc_ref_n(v_filePath_1069_, 2);
v___f_1085_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3), 2, 1);
lean_closure_set(v___f_1085_, 0, v_filePath_1069_);
v___x_1086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1087_ = l_System_FilePath_withExtension(v_filePath_1069_, v___x_1086_);
v_fst_1064_ = v___x_1087_;
v_snd_1065_ = v___f_1085_;
goto v___jp_1063_;
}
}
else
{
lean_dec(v___x_1071_);
lean_inc_ref(v_filePath_1069_);
v_fst_1064_ = v_filePath_1069_;
v_snd_1065_ = v___f_1070_;
goto v___jp_1063_;
}
v___jp_1049_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1053_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0));
v___x_1054_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_snd_1045_, v___y_1051_, v___x_1053_);
v___x_1055_ = lean_apply_1(v___y_1050_, v___x_1054_);
v___x_1056_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_snd_1045_, v___y_1051_, v___x_1055_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v___x_1056_);
lean_ctor_set(v___x_1047_, 0, v_order_1052_);
v___x_1058_ = v___x_1047_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_order_1052_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
size_t v___x_1059_; size_t v___x_1060_; 
v___x_1059_ = ((size_t)1ULL);
v___x_1060_ = lean_usize_add(v_i_1041_, v___x_1059_);
v_i_1041_ = v___x_1060_;
v_b_1042_ = v___x_1058_;
goto _start;
}
}
v___jp_1063_:
{
uint8_t v___x_1066_; 
v___x_1066_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1045_, v_fst_1064_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
lean_inc_ref(v_fst_1064_);
v___x_1067_ = lean_array_push(v_fst_1044_, v_fst_1064_);
v___y_1050_ = v_snd_1065_;
v___y_1051_ = v_fst_1064_;
v_order_1052_ = v___x_1067_;
goto v___jp_1049_;
}
else
{
v___y_1050_ = v_snd_1065_;
v___y_1051_ = v_fst_1064_;
v_order_1052_ = v_fst_1044_;
goto v___jp_1049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object* v_as_1089_, lean_object* v_sz_1090_, lean_object* v_i_1091_, lean_object* v_b_1092_){
_start:
{
size_t v_sz_boxed_1093_; size_t v_i_boxed_1094_; lean_object* v_res_1095_; 
v_sz_boxed_1093_ = lean_unbox_usize(v_sz_1090_);
lean_dec(v_sz_1090_);
v_i_boxed_1094_ = lean_unbox_usize(v_i_1091_);
lean_dec(v_i_1091_);
v_res_1095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_as_1089_, v_sz_boxed_1093_, v_i_boxed_1094_, v_b_1092_);
lean_dec_ref(v_as_1089_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(lean_object* v_msg_1096_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1098_ = lean_panic_fn_borrowed(v___x_1097_, v_msg_1096_);
return v___x_1098_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1102_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2));
v___x_1103_ = lean_unsigned_to_nat(11u);
v___x_1104_ = lean_unsigned_to_nat(163u);
v___x_1105_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1));
v___x_1106_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0));
v___x_1107_ = l_mkPanicMessageWithDecl(v___x_1106_, v___x_1105_, v___x_1104_, v___x_1103_, v___x_1102_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(lean_object* v_a_1108_, lean_object* v_x_1109_){
_start:
{
if (lean_obj_tag(v_x_1109_) == 0)
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3);
v___x_1111_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(v___x_1110_);
return v___x_1111_;
}
else
{
lean_object* v_key_1112_; lean_object* v_value_1113_; lean_object* v_tail_1114_; uint8_t v___x_1115_; 
v_key_1112_ = lean_ctor_get(v_x_1109_, 0);
v_value_1113_ = lean_ctor_get(v_x_1109_, 1);
v_tail_1114_ = lean_ctor_get(v_x_1109_, 2);
v___x_1115_ = lean_string_dec_eq(v_key_1112_, v_a_1108_);
if (v___x_1115_ == 0)
{
v_x_1109_ = v_tail_1114_;
goto _start;
}
else
{
lean_inc(v_value_1113_);
return v_value_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___boxed(lean_object* v_a_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1117_, v_x_1118_);
lean_dec(v_x_1118_);
lean_dec_ref(v_a_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object* v_m_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_buckets_1122_; lean_object* v___x_1123_; uint64_t v___x_1124_; uint64_t v___x_1125_; uint64_t v___x_1126_; uint64_t v_fold_1127_; uint64_t v___x_1128_; uint64_t v___x_1129_; uint64_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; size_t v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_buckets_1122_ = lean_ctor_get(v_m_1120_, 1);
v___x_1123_ = lean_array_get_size(v_buckets_1122_);
v___x_1124_ = lean_string_hash(v_a_1121_);
v___x_1125_ = 32ULL;
v___x_1126_ = lean_uint64_shift_right(v___x_1124_, v___x_1125_);
v_fold_1127_ = lean_uint64_xor(v___x_1124_, v___x_1126_);
v___x_1128_ = 16ULL;
v___x_1129_ = lean_uint64_shift_right(v_fold_1127_, v___x_1128_);
v___x_1130_ = lean_uint64_xor(v_fold_1127_, v___x_1129_);
v___x_1131_ = lean_uint64_to_usize(v___x_1130_);
v___x_1132_ = lean_usize_of_nat(v___x_1123_);
v___x_1133_ = ((size_t)1ULL);
v___x_1134_ = lean_usize_sub(v___x_1132_, v___x_1133_);
v___x_1135_ = lean_usize_land(v___x_1131_, v___x_1134_);
v___x_1136_ = lean_array_uget_borrowed(v_buckets_1122_, v___x_1135_);
v___x_1137_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1121_, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object* v_m_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v_m_1138_, v_a_1139_);
lean_dec_ref(v_a_1139_);
lean_dec_ref(v_m_1138_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object* v___x_1141_, size_t v_sz_1142_, size_t v_i_1143_, lean_object* v_bs_1144_){
_start:
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_usize_dec_lt(v_i_1143_, v_sz_1142_);
if (v___x_1145_ == 0)
{
return v_bs_1144_;
}
else
{
lean_object* v_v_1146_; lean_object* v___x_1147_; lean_object* v_bs_x27_1148_; lean_object* v___x_1149_; size_t v___x_1150_; size_t v___x_1151_; lean_object* v___x_1152_; 
v_v_1146_ = lean_array_uget(v_bs_1144_, v_i_1143_);
v___x_1147_ = lean_unsigned_to_nat(0u);
v_bs_x27_1148_ = lean_array_uset(v_bs_1144_, v_i_1143_, v___x_1147_);
v___x_1149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v___x_1141_, v_v_1146_);
lean_dec(v_v_1146_);
v___x_1150_ = ((size_t)1ULL);
v___x_1151_ = lean_usize_add(v_i_1143_, v___x_1150_);
v___x_1152_ = lean_array_uset(v_bs_x27_1148_, v_i_1143_, v___x_1149_);
v_i_1143_ = v___x_1151_;
v_bs_1144_ = v___x_1152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object* v___x_1154_, lean_object* v_sz_1155_, lean_object* v_i_1156_, lean_object* v_bs_1157_){
_start:
{
size_t v_sz_boxed_1158_; size_t v_i_boxed_1159_; lean_object* v_res_1160_; 
v_sz_boxed_1158_ = lean_unbox_usize(v_sz_1155_);
lean_dec(v_sz_1155_);
v_i_boxed_1159_ = lean_unbox_usize(v_i_1156_);
lean_dec(v_i_1156_);
v_res_1160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v___x_1154_, v_sz_boxed_1158_, v_i_boxed_1159_, v_bs_1157_);
lean_dec_ref(v___x_1154_);
return v_res_1160_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_box(0);
v___x_1164_ = lean_unsigned_to_nat(16u);
v___x_1165_ = lean_mk_array(v___x_1164_, v___x_1163_);
return v___x_1165_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v_byBase_1168_; 
v___x_1166_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1);
v___x_1167_ = lean_unsigned_to_nat(0u);
v_byBase_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byBase_1168_, 0, v___x_1167_);
lean_ctor_set(v_byBase_1168_, 1, v___x_1166_);
return v_byBase_1168_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3(void){
_start:
{
lean_object* v_byBase_1169_; lean_object* v_order_1170_; lean_object* v___x_1171_; 
v_byBase_1169_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2);
v_order_1170_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0));
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_order_1170_);
lean_ctor_set(v___x_1171_, 1, v_byBase_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object* v_regions_1172_){
_start:
{
lean_object* v___x_1173_; size_t v_sz_1174_; size_t v___x_1175_; lean_object* v___x_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; size_t v_sz_1179_; lean_object* v___x_1180_; 
v___x_1173_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3);
v_sz_1174_ = lean_array_size(v_regions_1172_);
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_regions_1172_, v_sz_1174_, v___x_1175_, v___x_1173_);
v_fst_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_fst_1177_);
v_snd_1178_ = lean_ctor_get(v___x_1176_, 1);
lean_inc(v_snd_1178_);
lean_dec_ref(v___x_1176_);
v_sz_1179_ = lean_array_size(v_fst_1177_);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v_snd_1178_, v_sz_1179_, v___x_1175_, v_fst_1177_);
lean_dec(v_snd_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object* v_regions_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1181_);
lean_dec_ref(v_regions_1181_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object* v_00_u03b2_1183_, lean_object* v_m_1184_, lean_object* v_a_1185_, lean_object* v_fallback_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_1184_, v_a_1185_, v_fallback_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object* v_00_u03b2_1188_, lean_object* v_m_1189_, lean_object* v_a_1190_, lean_object* v_fallback_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(v_00_u03b2_1188_, v_m_1189_, v_a_1190_, v_fallback_1191_);
lean_dec(v_fallback_1191_);
lean_dec_ref(v_a_1190_);
lean_dec_ref(v_m_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object* v_00_u03b2_1193_, lean_object* v_m_1194_, lean_object* v_a_1195_, lean_object* v_b_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_1194_, v_a_1195_, v_b_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object* v_00_u03b2_1198_, lean_object* v_m_1199_, lean_object* v_a_1200_){
_start:
{
uint8_t v___x_1201_; 
v___x_1201_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_1199_, v_a_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object* v_00_u03b2_1202_, lean_object* v_m_1203_, lean_object* v_a_1204_){
_start:
{
uint8_t v_res_1205_; lean_object* v_r_1206_; 
v_res_1205_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(v_00_u03b2_1202_, v_m_1203_, v_a_1204_);
lean_dec_ref(v_a_1204_);
lean_dec_ref(v_m_1203_);
v_r_1206_ = lean_box(v_res_1205_);
return v_r_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object* v_00_u03b2_1207_, lean_object* v_a_1208_, lean_object* v_fallback_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_1208_, v_fallback_1209_, v_x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1212_, lean_object* v_a_1213_, lean_object* v_fallback_1214_, lean_object* v_x_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(v_00_u03b2_1212_, v_a_1213_, v_fallback_1214_, v_x_1215_);
lean_dec(v_x_1215_);
lean_dec(v_fallback_1214_);
lean_dec_ref(v_a_1213_);
return v_res_1216_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object* v_00_u03b2_1217_, lean_object* v_a_1218_, lean_object* v_x_1219_){
_start:
{
uint8_t v___x_1220_; 
v___x_1220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1218_, v_x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1221_, lean_object* v_a_1222_, lean_object* v_x_1223_){
_start:
{
uint8_t v_res_1224_; lean_object* v_r_1225_; 
v_res_1224_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(v_00_u03b2_1221_, v_a_1222_, v_x_1223_);
lean_dec(v_x_1223_);
lean_dec_ref(v_a_1222_);
v_r_1225_ = lean_box(v_res_1224_);
return v_r_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3(lean_object* v_00_u03b2_1226_, lean_object* v_data_1227_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_data_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4(lean_object* v_00_u03b2_1229_, lean_object* v_a_1230_, lean_object* v_b_1231_, lean_object* v_x_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1230_, v_b_1231_, v_x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1234_, lean_object* v_i_1235_, lean_object* v_source_1236_, lean_object* v_target_1237_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v_i_1235_, v_source_1236_, v_target_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1239_, lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_x_1240_, v_x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(lean_object* v_as_1243_, size_t v_sz_1244_, size_t v_i_1245_, lean_object* v_b_1246_){
_start:
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_usize_dec_lt(v_i_1245_, v_sz_1244_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_b_1246_);
return v___x_1249_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1251_; 
v_a_1250_ = lean_array_uget_borrowed(v_as_1243_, v_i_1245_);
v___x_1251_ = lean_compacted_region_read(v_a_1250_, v_b_1246_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v_snd_1253_; lean_object* v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v_snd_1253_ = lean_ctor_get(v_a_1252_, 1);
lean_inc(v_snd_1253_);
lean_dec(v_a_1252_);
v___x_1254_ = lean_array_push(v_b_1246_, v_snd_1253_);
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_add(v_i_1245_, v___x_1255_);
v_i_1245_ = v___x_1256_;
v_b_1246_ = v___x_1254_;
goto _start;
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref(v_b_1246_);
v_a_1258_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1251_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1251_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0___boxed(lean_object* v_as_1266_, lean_object* v_sz_1267_, lean_object* v_i_1268_, lean_object* v_b_1269_, lean_object* v___y_1270_){
_start:
{
size_t v_sz_boxed_1271_; size_t v_i_boxed_1272_; lean_object* v_res_1273_; 
v_sz_boxed_1271_ = lean_unbox_usize(v_sz_1267_);
lean_dec(v_sz_1267_);
v_i_boxed_1272_ = lean_unbox_usize(v_i_1268_);
lean_dec(v_i_1268_);
v_res_1273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v_as_1266_, v_sz_boxed_1271_, v_i_boxed_1272_, v_b_1269_);
lean_dec_ref(v_as_1266_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(lean_object* v_arts_1276_){
_start:
{
lean_object* v_chainDeps_1278_; lean_object* v___x_1279_; size_t v_sz_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v_chainDeps_1278_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc_ref(v_arts_1276_);
v___x_1279_ = l_Lean_ModuleArtifacts_oleanParts(v_arts_1276_);
v_sz_1280_ = lean_array_size(v___x_1279_);
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1279_, v_sz_1280_, v___x_1281_, v_chainDeps_1278_);
lean_dec_ref(v___x_1279_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_ir_x3f_1283_; 
v_ir_x3f_1283_ = lean_ctor_get(v_arts_1276_, 5);
lean_inc(v_ir_x3f_1283_);
lean_dec_ref(v_arts_1276_);
if (lean_obj_tag(v_ir_x3f_1283_) == 1)
{
lean_object* v_a_1284_; lean_object* v_val_1285_; lean_object* v___x_1286_; 
v_a_1284_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1282_, 1);
v_val_1285_ = lean_ctor_get(v_ir_x3f_1283_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v_ir_x3f_1283_, 1);
v___x_1286_ = lean_compacted_region_read(v_val_1285_, v_chainDeps_1278_);
lean_dec(v_val_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1296_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1296_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1296_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v_snd_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v_snd_1291_ = lean_ctor_get(v_a_1287_, 1);
lean_inc(v_snd_1291_);
lean_dec(v_a_1287_);
v___x_1292_ = lean_array_push(v_a_1284_, v_snd_1291_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1292_);
v___x_1294_ = v___x_1289_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v_a_1284_);
v_a_1297_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1286_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1286_);
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
else
{
lean_dec(v_ir_x3f_1283_);
return v___x_1282_;
}
}
else
{
lean_dec_ref(v_arts_1276_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___boxed(lean_object* v_arts_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v_arts_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(lean_object* v_e_1308_){
_start:
{
if (lean_obj_tag(v_e_1308_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1319_; 
v_a_1310_ = lean_ctor_get(v_e_1308_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_e_1308_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1312_ = v_e_1308_;
v_isShared_1313_ = v_isSharedCheck_1319_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v_e_1308_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1319_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1314_ = lean_io_error_to_string(v_a_1310_);
v___x_1315_ = lean_mk_io_user_error(v___x_1314_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set_tag(v___x_1312_, 1);
lean_ctor_set(v___x_1312_, 0, v___x_1315_);
v___x_1317_ = v___x_1312_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
v_a_1320_ = lean_ctor_get(v_e_1308_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_e_1308_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v_e_1308_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v_e_1308_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
lean_ctor_set_tag(v___x_1322_, 0);
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg___boxed(lean_object* v_e_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1328_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_object* v_00_u03b1_1331_, lean_object* v_e_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___boxed(lean_object* v_00_u03b1_1335_, lean_object* v_e_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(v_00_u03b1_1335_, v_e_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object* v_a_1339_, lean_object* v___y_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_fst_1343_; lean_object* v_snd_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1372_; 
v_fst_1343_ = lean_ctor_get(v_a_1341_, 0);
v_snd_1344_ = lean_ctor_get(v_a_1341_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_a_1341_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1346_ = v_a_1341_;
v_isShared_1347_ = v_isSharedCheck_1372_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_snd_1344_);
lean_inc(v_fst_1343_);
lean_dec(v_a_1341_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1372_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = lean_array_get_size(v_a_1339_);
v___x_1349_ = lean_nat_dec_lt(v_snd_1344_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1351_; 
if (v_isShared_1347_ == 0)
{
v___x_1351_ = v___x_1346_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_fst_1343_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_snd_1344_);
v___x_1351_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
return v___x_1352_;
}
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1355_ = lean_array_get_borrowed(v___x_1354_, v_a_1339_, v_snd_1344_);
lean_inc(v___x_1355_);
v___x_1356_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v___x_1355_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v___x_1358_ = l_Array_append___redArg(v_fst_1343_, v_a_1357_);
lean_dec(v_a_1357_);
v___x_1359_ = lean_nat_add(v_snd_1344_, v___y_1340_);
lean_dec(v_snd_1344_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1359_);
lean_ctor_set(v___x_1346_, 0, v___x_1358_);
v___x_1361_ = v___x_1346_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
v_a_1341_ = v___x_1361_;
goto _start;
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
v_a_1364_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1356_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1356_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object* v_a_1373_, lean_object* v___y_1374_, lean_object* v_a_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1373_, v___y_1374_, v_a_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v_a_1373_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(lean_object* v_a_1378_, lean_object* v___y_1379_, lean_object* v___x_1380_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1378_, v___y_1379_, v___x_1380_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1391_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1391_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v_fst_1387_; lean_object* v___x_1389_; 
v_fst_1387_ = lean_ctor_get(v_a_1383_, 0);
lean_inc(v_fst_1387_);
lean_dec(v_a_1383_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set_tag(v___x_1385_, 1);
lean_ctor_set(v___x_1385_, 0, v_fst_1387_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_fst_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
v_a_1392_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1382_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1382_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 0);
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed(lean_object* v_a_1400_, lean_object* v___y_1401_, lean_object* v___x_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(v_a_1400_, v___y_1401_, v___x_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v_a_1400_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(lean_object* v_upperBound_1405_, lean_object* v_a_1406_, lean_object* v___y_1407_, lean_object* v_a_1408_, lean_object* v_b_1409_){
_start:
{
uint8_t v___x_1411_; 
v___x_1411_ = lean_nat_dec_lt(v_a_1408_, v_upperBound_1405_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; 
lean_dec(v_a_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v_a_1406_);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v_b_1409_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___f_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc(v_a_1408_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
lean_ctor_set(v___x_1415_, 1, v_a_1408_);
lean_inc(v___y_1407_);
lean_inc_ref(v_a_1406_);
v___f_1416_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1416_, 0, v_a_1406_);
lean_closure_set(v___f_1416_, 1, v___y_1407_);
lean_closure_set(v___f_1416_, 2, v___x_1415_);
v___x_1417_ = lean_io_as_task(v___f_1416_, v___x_1413_);
v___x_1418_ = lean_array_push(v_b_1409_, v___x_1417_);
v___x_1419_ = lean_unsigned_to_nat(1u);
v___x_1420_ = lean_nat_add(v_a_1408_, v___x_1419_);
lean_dec(v_a_1408_);
v_a_1408_ = v___x_1420_;
v_b_1409_ = v___x_1418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___boxed(lean_object* v_upperBound_1422_, lean_object* v_a_1423_, lean_object* v___y_1424_, lean_object* v_a_1425_, lean_object* v_b_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1422_, v_a_1423_, v___y_1424_, v_a_1425_, v_b_1426_);
lean_dec(v_upperBound_1422_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(lean_object* v_as_1429_, size_t v_sz_1430_, size_t v_i_1431_, lean_object* v_b_1432_){
_start:
{
uint8_t v___x_1434_; 
v___x_1434_ = lean_usize_dec_lt(v_i_1431_, v_sz_1430_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v_b_1432_);
return v___x_1435_;
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_a_1436_ = lean_array_uget_borrowed(v_as_1429_, v_i_1431_);
lean_inc(v_a_1436_);
v___x_1437_ = lean_task_get_own(v_a_1436_);
v___x_1438_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v___x_1437_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1440_; size_t v___x_1441_; size_t v___x_1442_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1438_, 1);
v___x_1440_ = l_Array_append___redArg(v_b_1432_, v_a_1439_);
lean_dec(v_a_1439_);
v___x_1441_ = ((size_t)1ULL);
v___x_1442_ = lean_usize_add(v_i_1431_, v___x_1441_);
v_i_1431_ = v___x_1442_;
v_b_1432_ = v___x_1440_;
goto _start;
}
else
{
lean_dec_ref(v_b_1432_);
return v___x_1438_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2___boxed(lean_object* v_as_1444_, lean_object* v_sz_1445_, lean_object* v_i_1446_, lean_object* v_b_1447_, lean_object* v___y_1448_){
_start:
{
size_t v_sz_boxed_1449_; size_t v_i_boxed_1450_; lean_object* v_res_1451_; 
v_sz_boxed_1449_ = lean_unbox_usize(v_sz_1445_);
lean_dec(v_sz_1445_);
v_i_boxed_1450_ = lean_unbox_usize(v_i_1446_);
lean_dec(v_i_1446_);
v_res_1451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_as_1444_, v_sz_boxed_1449_, v_i_boxed_1450_, v_b_1447_);
lean_dec_ref(v_as_1444_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t v_sz_1452_, size_t v_i_1453_, lean_object* v_bs_1454_){
_start:
{
uint8_t v___x_1455_; 
v___x_1455_ = lean_usize_dec_lt(v_i_1453_, v_sz_1452_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_bs_1454_);
return v___x_1456_;
}
else
{
lean_object* v_v_1457_; lean_object* v___x_1458_; 
v_v_1457_ = lean_array_uget_borrowed(v_bs_1454_, v_i_1453_);
lean_inc(v_v_1457_);
v___x_1458_ = l_Lean_instFromJsonModuleArtifacts_fromJson(v_v_1457_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec_ref(v_bs_1454_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1468_; lean_object* v_bs_x27_1469_; size_t v___x_1470_; size_t v___x_1471_; lean_object* v___x_1472_; 
v_a_1467_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1458_, 1);
v___x_1468_ = lean_unsigned_to_nat(0u);
v_bs_x27_1469_ = lean_array_uset(v_bs_1454_, v_i_1453_, v___x_1468_);
v___x_1470_ = ((size_t)1ULL);
v___x_1471_ = lean_usize_add(v_i_1453_, v___x_1470_);
v___x_1472_ = lean_array_uset(v_bs_x27_1469_, v_i_1453_, v_a_1467_);
v_i_1453_ = v___x_1471_;
v_bs_1454_ = v___x_1472_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object* v_sz_1474_, lean_object* v_i_1475_, lean_object* v_bs_1476_){
_start:
{
size_t v_sz_boxed_1477_; size_t v_i_boxed_1478_; lean_object* v_res_1479_; 
v_sz_boxed_1477_ = lean_unbox_usize(v_sz_1474_);
lean_dec(v_sz_1474_);
v_i_boxed_1478_ = lean_unbox_usize(v_i_1475_);
lean_dec(v_i_1475_);
v_res_1479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_boxed_1477_, v_i_boxed_1478_, v_bs_1476_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object* v_x_1482_){
_start:
{
if (lean_obj_tag(v_x_1482_) == 4)
{
lean_object* v_elems_1483_; size_t v_sz_1484_; size_t v___x_1485_; lean_object* v___x_1486_; 
v_elems_1483_ = lean_ctor_get(v_x_1482_, 0);
lean_inc_ref(v_elems_1483_);
lean_dec_ref_known(v_x_1482_, 1);
v_sz_1484_ = lean_array_size(v_elems_1483_);
v___x_1485_ = ((size_t)0ULL);
v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_1484_, v___x_1485_, v_elems_1483_);
return v___x_1486_;
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1487_ = ((lean_object*)(l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0));
v___x_1488_ = lean_unsigned_to_nat(80u);
v___x_1489_ = l_Lean_Json_pretty(v_x_1482_, v___x_1488_);
v___x_1490_ = lean_string_append(v___x_1487_, v___x_1489_);
lean_dec_ref(v___x_1489_);
v___x_1491_ = ((lean_object*)(l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1));
v___x_1492_ = lean_string_append(v___x_1490_, v___x_1491_);
v___x_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1492_);
return v___x_1493_;
}
}
}
static uint32_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3(void){
_start:
{
lean_object* v___x_1497_; uint32_t v___x_1498_; 
v___x_1497_ = lean_box(0);
v___x_1498_ = lean_internal_get_hardware_concurrency(v___x_1497_);
return v___x_1498_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4(void){
_start:
{
uint32_t v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_uint32_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3);
v___x_1500_ = lean_uint32_to_nat(v___x_1499_);
return v___x_1500_;
}
}
static uint8_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1502_ = lean_unsigned_to_nat(4u);
v___x_1503_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1504_ = lean_nat_dec_le(v___x_1503_, v___x_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(lean_object* v_fname_1505_){
_start:
{
lean_object* v___x_1507_; lean_object* v_depsFile_1508_; lean_object* v___x_1509_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
lean_inc_ref(v_fname_1505_);
v_depsFile_1508_ = l_System_FilePath_addExtension(v_fname_1505_, v___x_1507_);
v___x_1509_ = l_IO_FS_readFile(v_depsFile_1508_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1596_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1596_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1596_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v_a_1515_; lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_Json_parse(v_a_1510_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; 
lean_dec_ref(v_fname_1505_);
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref_known(v___x_1525_, 1);
v_a_1515_ = v_a_1526_;
goto v___jp_1514_;
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1525_, 1);
v___x_1528_ = l_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(v_a_1527_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; 
lean_dec_ref(v_fname_1505_);
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v_a_1515_ = v_a_1529_;
goto v___jp_1514_;
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___y_1534_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1585_; uint8_t v___x_1595_; 
lean_del_object(v___x_1512_);
lean_dec_ref(v_depsFile_1508_);
v_a_1530_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1531_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1532_ = lean_unsigned_to_nat(4u);
v___x_1595_ = lean_uint8_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6);
if (v___x_1595_ == 0)
{
v___y_1585_ = v___x_1532_;
goto v___jp_1584_;
}
else
{
v___y_1585_ = v___x_1531_;
goto v___jp_1584_;
}
v___jp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = lean_mk_empty_array_with_capacity(v___y_1534_);
v___x_1536_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_1530_);
lean_inc(v___y_1534_);
v___x_1537_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v___y_1534_, v_a_1530_, v___y_1534_, v___x_1536_, v___x_1535_);
lean_dec(v___y_1534_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; size_t v_sz_1542_; size_t v___x_1543_; lean_object* v___x_1544_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
v___x_1539_ = lean_array_get_size(v_a_1530_);
lean_dec(v_a_1530_);
v___x_1540_ = lean_nat_mul(v___x_1539_, v___x_1532_);
v___x_1541_ = lean_mk_empty_array_with_capacity(v___x_1540_);
lean_dec(v___x_1540_);
v_sz_1542_ = lean_array_size(v_a_1538_);
v___x_1543_ = ((size_t)0ULL);
v___x_1544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_a_1538_, v_sz_1542_, v___x_1543_, v___x_1541_);
lean_dec(v_a_1538_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1546_ = lean_compacted_region_read(v_fname_1505_, v_a_1545_);
lean_dec(v_a_1545_);
lean_dec_ref(v_fname_1505_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1555_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_fst_1551_; lean_object* v___x_1553_; 
v_fst_1551_ = lean_ctor_get(v_a_1547_, 0);
lean_inc(v_fst_1551_);
lean_dec(v_a_1547_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v_fst_1551_);
v___x_1553_ = v___x_1549_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_fst_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
v_a_1556_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1546_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1546_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v_fname_1505_);
v_a_1564_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1544_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1544_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v_a_1530_);
lean_dec_ref(v_fname_1505_);
v_a_1572_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1537_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1537_);
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
v___jp_1580_:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_nat_dec_le(v___y_1581_, v___y_1582_);
if (v___x_1583_ == 0)
{
lean_dec(v___y_1582_);
v___y_1534_ = v___y_1581_;
goto v___jp_1533_;
}
else
{
lean_dec(v___y_1581_);
v___y_1534_ = v___y_1582_;
goto v___jp_1533_;
}
}
v___jp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5));
v___x_1587_ = lean_io_getenv(v___x_1586_);
v___x_1588_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v___x_1587_) == 0)
{
v___y_1581_ = v___x_1588_;
v___y_1582_ = v___y_1585_;
goto v___jp_1580_;
}
else
{
lean_object* v_val_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_val_1589_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_val_1589_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1590_ = lean_unsigned_to_nat(0u);
v___x_1591_ = lean_string_utf8_byte_size(v_val_1589_);
v___x_1592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1592_, 0, v_val_1589_);
lean_ctor_set(v___x_1592_, 1, v___x_1590_);
lean_ctor_set(v___x_1592_, 2, v___x_1591_);
v___x_1593_ = l_String_Slice_toNat_x3f(v___x_1592_);
lean_dec_ref_known(v___x_1592_, 3);
if (lean_obj_tag(v___x_1593_) == 0)
{
v___y_1581_ = v___x_1588_;
v___y_1582_ = v___y_1585_;
goto v___jp_1580_;
}
else
{
lean_object* v_val_1594_; 
lean_dec(v___y_1585_);
v_val_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v___y_1581_ = v___x_1588_;
v___y_1582_ = v_val_1594_;
goto v___jp_1580_;
}
}
}
}
}
v___jp_1514_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1516_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1));
v___x_1517_ = lean_string_append(v___x_1516_, v_depsFile_1508_);
lean_dec_ref(v_depsFile_1508_);
v___x_1518_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2));
v___x_1519_ = lean_string_append(v___x_1517_, v___x_1518_);
v___x_1520_ = lean_string_append(v___x_1519_, v_a_1515_);
lean_dec_ref(v_a_1515_);
v___x_1521_ = lean_mk_io_user_error(v___x_1520_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set_tag(v___x_1512_, 1);
lean_ctor_set(v___x_1512_, 0, v___x_1521_);
v___x_1523_ = v___x_1512_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec_ref(v_depsFile_1508_);
lean_dec_ref(v_fname_1505_);
v_a_1597_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1509_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1509_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___boxed(lean_object* v_fname_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_fname_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object* v_a_1608_, lean_object* v___y_1609_, lean_object* v_inst_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1608_, v___y_1609_, v_a_1611_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object* v_a_1614_, lean_object* v___y_1615_, lean_object* v_inst_1616_, lean_object* v_a_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(v_a_1614_, v___y_1615_, v_inst_1616_, v_a_1617_);
lean_dec(v___y_1615_);
lean_dec_ref(v_a_1614_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object* v_upperBound_1620_, lean_object* v_a_1621_, lean_object* v___y_1622_, lean_object* v_inst_1623_, lean_object* v_R_1624_, lean_object* v_a_1625_, lean_object* v_b_1626_, lean_object* v_c_1627_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1620_, v_a_1621_, v___y_1622_, v_a_1625_, v_b_1626_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object* v_upperBound_1630_, lean_object* v_a_1631_, lean_object* v___y_1632_, lean_object* v_inst_1633_, lean_object* v_R_1634_, lean_object* v_a_1635_, lean_object* v_b_1636_, lean_object* v_c_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(v_upperBound_1630_, v_a_1631_, v___y_1632_, v_inst_1633_, v_R_1634_, v_a_1635_, v_b_1636_, v_c_1637_);
lean_dec(v_upperBound_1630_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object* v_as_1640_, size_t v_sz_1641_, size_t v_i_1642_, lean_object* v_b_1643_){
_start:
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_usize_dec_lt(v_i_1642_, v_sz_1641_);
if (v___x_1645_ == 0)
{
return v_b_1643_;
}
else
{
lean_object* v_a_1646_; lean_object* v_cancelTk_x3f_1647_; lean_object* v___x_1648_; 
v_a_1646_ = lean_array_uget_borrowed(v_as_1640_, v_i_1642_);
v_cancelTk_x3f_1647_ = lean_ctor_get(v_a_1646_, 2);
v___x_1648_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_1647_) == 1)
{
lean_object* v_val_1655_; lean_object* v___x_1656_; 
v_val_1655_ = lean_ctor_get(v_cancelTk_x3f_1647_, 0);
v___x_1656_ = l_IO_CancelToken_set(v_val_1655_);
goto v___jp_1649_;
}
else
{
goto v___jp_1649_;
}
v___jp_1649_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; size_t v___x_1652_; size_t v___x_1653_; 
lean_inc(v_a_1646_);
v___x_1650_ = l_Lean_Language_SnapshotTask_get___redArg(v_a_1646_);
v___x_1651_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___x_1650_);
lean_dec(v___x_1650_);
v___x_1652_ = ((size_t)1ULL);
v___x_1653_ = lean_usize_add(v_i_1642_, v___x_1652_);
v_i_1642_ = v___x_1653_;
v_b_1643_ = v___x_1648_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object* v_s_1657_){
_start:
{
lean_object* v_children_1659_; lean_object* v___x_1660_; size_t v_sz_1661_; size_t v___x_1662_; lean_object* v___x_1663_; 
v_children_1659_ = lean_ctor_get(v_s_1657_, 1);
v___x_1660_ = lean_box(0);
v_sz_1661_ = lean_array_size(v_children_1659_);
v___x_1662_ = ((size_t)0ULL);
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_children_1659_, v_sz_1661_, v___x_1662_, v___x_1660_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object* v_s_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v_s_1664_);
lean_dec_ref(v_s_1664_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object* v_as_1667_, lean_object* v_sz_1668_, lean_object* v_i_1669_, lean_object* v_b_1670_, lean_object* v___y_1671_){
_start:
{
size_t v_sz_boxed_1672_; size_t v_i_boxed_1673_; lean_object* v_res_1674_; 
v_sz_boxed_1672_ = lean_unbox_usize(v_sz_1668_);
lean_dec(v_sz_1668_);
v_i_boxed_1673_ = lean_unbox_usize(v_i_1669_);
lean_dec(v_i_1669_);
v_res_1674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_as_1667_, v_sz_boxed_1672_, v_i_boxed_1673_, v_b_1670_);
lean_dec_ref(v_as_1667_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object* v_incrFile_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_incrFile_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object* v_incrFile_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(v_incrFile_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object* v_opts_1681_, lean_object* v_incr_1682_, lean_object* v_res_1683_){
_start:
{
lean_object* v_cmdState_1685_; lean_object* v_env_1686_; lean_object* v_initModIdxs_1687_; lean_object* v___x_1688_; 
v_cmdState_1685_ = lean_ctor_get(v_res_1683_, 0);
lean_inc_ref(v_cmdState_1685_);
lean_dec_ref(v_res_1683_);
v_env_1686_ = lean_ctor_get(v_cmdState_1685_, 0);
lean_inc_ref(v_env_1686_);
lean_dec_ref(v_cmdState_1685_);
v_initModIdxs_1687_ = lean_ctor_get(v_incr_1682_, 1);
v___x_1688_ = l_Lean_runInitAttrsForModules(v_env_1686_, v_initModIdxs_1687_, v_opts_1681_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object* v_opts_1689_, lean_object* v_incr_1690_, lean_object* v_res_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(v_opts_1689_, v_incr_1690_, v_res_1691_);
lean_dec_ref(v_incr_1690_);
lean_dec_ref(v_opts_1689_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7(){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_enable_initializer_execution();
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14(lean_object* v_env_1701_, lean_object* v_incrFile_1702_, lean_object* v_toSave_1703_){
_start:
{
lean_object* v___x_1705_; lean_object* v_regions_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; lean_object* v___x_1710_; 
v___x_1705_ = l_Lean_Environment_header(v_env_1701_);
v_regions_1706_ = lean_ctor_get(v___x_1705_, 2);
lean_inc_ref(v_regions_1706_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14___closed__1));
v___x_1708_ = lean_box(0);
v___x_1709_ = 1;
v___x_1710_ = lean_compacted_region_save(v_incrFile_1702_, v___x_1707_, v_toSave_1703_, v_regions_1706_, v___x_1708_, v___x_1709_);
lean_dec_ref(v_regions_1706_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14___boxed(lean_object* v_env_1711_, lean_object* v_incrFile_1712_, lean_object* v_toSave_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14(v_env_1711_, v_incrFile_1712_, v_toSave_1713_);
lean_dec_ref(v_toSave_1713_);
lean_dec_ref(v_incrFile_1712_);
lean_dec_ref(v_env_1711_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__3(lean_object* v_opts_1716_, lean_object* v_opt_1717_){
_start:
{
lean_object* v_name_1718_; lean_object* v_map_1719_; lean_object* v___x_1720_; 
v_name_1718_ = lean_ctor_get(v_opt_1717_, 0);
v_map_1719_ = lean_ctor_get(v_opts_1716_, 0);
v___x_1720_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1719_, v_name_1718_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_box(0);
return v___x_1721_;
}
else
{
lean_object* v_val_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1731_; 
v_val_1722_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1724_ = v___x_1720_;
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_val_1722_);
lean_dec(v___x_1720_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
if (lean_obj_tag(v_val_1722_) == 0)
{
lean_object* v_v_1726_; lean_object* v___x_1728_; 
v_v_1726_ = lean_ctor_get(v_val_1722_, 0);
lean_inc_ref(v_v_1726_);
lean_dec_ref_known(v_val_1722_, 1);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v_v_1726_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_v_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
else
{
lean_object* v___x_1730_; 
lean_del_object(v___x_1724_);
lean_dec(v_val_1722_);
v___x_1730_ = lean_box(0);
return v___x_1730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object* v_opts_1732_, lean_object* v_opt_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__3(v_opts_1732_, v_opt_1733_);
lean_dec_ref(v_opt_1733_);
lean_dec_ref(v_opts_1732_);
return v_res_1734_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(lean_object* v_opts_1735_, lean_object* v_opt_1736_){
_start:
{
lean_object* v_name_1737_; lean_object* v_defValue_1738_; lean_object* v_map_1739_; lean_object* v___x_1740_; 
v_name_1737_ = lean_ctor_get(v_opt_1736_, 0);
v_defValue_1738_ = lean_ctor_get(v_opt_1736_, 1);
v_map_1739_ = lean_ctor_get(v_opts_1735_, 0);
v___x_1740_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1739_, v_name_1737_);
if (lean_obj_tag(v___x_1740_) == 0)
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_unbox(v_defValue_1738_);
return v___x_1741_;
}
else
{
lean_object* v_val_1742_; 
v_val_1742_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_val_1742_);
lean_dec_ref_known(v___x_1740_, 1);
if (lean_obj_tag(v_val_1742_) == 1)
{
uint8_t v_v_1743_; 
v_v_1743_ = lean_ctor_get_uint8(v_val_1742_, 0);
lean_dec_ref_known(v_val_1742_, 0);
return v_v_1743_;
}
else
{
uint8_t v___x_1744_; 
lean_dec(v_val_1742_);
v___x_1744_ = lean_unbox(v_defValue_1738_);
return v___x_1744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_opts_1745_, lean_object* v_opt_1746_){
_start:
{
uint8_t v_res_1747_; lean_object* v_r_1748_; 
v_res_1747_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(v_opts_1745_, v_opt_1746_);
lean_dec_ref(v_opt_1746_);
lean_dec_ref(v_opts_1745_);
v_r_1748_ = lean_box(v_res_1747_);
return v_r_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_1749_, lean_object* v_x_1750_, lean_object* v_hOpt_1751_){
_start:
{
lean_inc_ref(v_hOpt_1751_);
return v_hOpt_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_1752_, lean_object* v_x_1753_, lean_object* v_hOpt_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Elab_runFrontend___lam__0(v_x_1752_, v_x_1753_, v_hOpt_1754_);
lean_dec_ref(v_hOpt_1754_);
lean_dec_ref(v_x_1753_);
lean_dec(v_x_1752_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_s_1758_){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = ((lean_object*)(l_Lean_Elab_runFrontend___lam__1___closed__0));
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v_s_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v___f_1762_, lean_object* v_s_1763_){
_start:
{
lean_object* v_toSnapshot_1764_; lean_object* v_metaSnap_1765_; lean_object* v_result_x3f_1766_; lean_object* v___y_1768_; 
v_toSnapshot_1764_ = lean_ctor_get(v_s_1763_, 0);
lean_inc_ref(v_toSnapshot_1764_);
v_metaSnap_1765_ = lean_ctor_get(v_s_1763_, 1);
lean_inc_ref(v_metaSnap_1765_);
v_result_x3f_1766_ = lean_ctor_get(v_s_1763_, 2);
lean_inc(v_result_x3f_1766_);
lean_dec_ref(v_s_1763_);
if (lean_obj_tag(v_result_x3f_1766_) == 0)
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_box(0);
v___y_1768_ = v___x_1778_;
goto v___jp_1767_;
}
else
{
lean_object* v_val_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1792_; 
v_val_1779_ = lean_ctor_get(v_result_x3f_1766_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_result_x3f_1766_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1781_ = v_result_x3f_1766_;
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_val_1779_);
lean_dec(v_result_x3f_1766_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1792_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v_firstCmdSnap_1783_; lean_object* v_stx_x3f_1784_; lean_object* v_reportingRange_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1790_; 
v_firstCmdSnap_1783_ = lean_ctor_get(v_val_1779_, 1);
lean_inc_ref(v_firstCmdSnap_1783_);
lean_dec(v_val_1779_);
v_stx_x3f_1784_ = lean_ctor_get(v_firstCmdSnap_1783_, 0);
lean_inc(v_stx_x3f_1784_);
v_reportingRange_1785_ = lean_ctor_get(v_firstCmdSnap_1783_, 1);
lean_inc(v_reportingRange_1785_);
v___x_1786_ = ((lean_object*)(l_Lean_Elab_runFrontend___lam__2___closed__0));
v___x_1787_ = 1;
v___x_1788_ = l_Lean_Language_SnapshotTask_map___redArg(v_firstCmdSnap_1783_, v___x_1786_, v_stx_x3f_1784_, v_reportingRange_1785_, v___x_1787_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1788_);
v___x_1790_ = v___x_1781_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
v___y_1768_ = v___x_1790_;
goto v___jp_1767_;
}
}
}
v___jp_1767_:
{
lean_object* v_stx_x3f_1769_; lean_object* v_reportingRange_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_stx_x3f_1769_ = lean_ctor_get(v_metaSnap_1765_, 0);
lean_inc(v_stx_x3f_1769_);
v_reportingRange_1770_ = lean_ctor_get(v_metaSnap_1765_, 1);
lean_inc(v_reportingRange_1770_);
v___x_1771_ = 1;
v___x_1772_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_1765_, v___f_1762_, v_stx_x3f_1769_, v_reportingRange_1770_, v___x_1771_);
v___x_1773_ = lean_unsigned_to_nat(1u);
v___x_1774_ = lean_mk_empty_array_with_capacity(v___x_1773_);
v___x_1775_ = lean_array_push(v___x_1774_, v___x_1772_);
v___x_1776_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_1768_, v___x_1775_);
v___x_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1777_, 0, v_toSnapshot_1764_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Elab_runFrontend_spec__2_spec__3(size_t v_sz_1793_, size_t v_i_1794_, lean_object* v_bs_1795_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_usize_dec_lt(v_i_1794_, v_sz_1793_);
if (v___x_1796_ == 0)
{
return v_bs_1795_;
}
else
{
lean_object* v_v_1797_; lean_object* v___x_1798_; lean_object* v_bs_x27_1799_; lean_object* v___x_1800_; size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v_v_1797_ = lean_array_uget(v_bs_1795_, v_i_1794_);
v___x_1798_ = lean_unsigned_to_nat(0u);
v_bs_x27_1799_ = lean_array_uset(v_bs_1795_, v_i_1794_, v___x_1798_);
v___x_1800_ = l_Lean_instToJsonModuleArtifacts_toJson(v_v_1797_);
v___x_1801_ = ((size_t)1ULL);
v___x_1802_ = lean_usize_add(v_i_1794_, v___x_1801_);
v___x_1803_ = lean_array_uset(v_bs_x27_1799_, v_i_1794_, v___x_1800_);
v_i_1794_ = v___x_1802_;
v_bs_1795_ = v___x_1803_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object* v_sz_1805_, lean_object* v_i_1806_, lean_object* v_bs_1807_){
_start:
{
size_t v_sz_boxed_1808_; size_t v_i_boxed_1809_; lean_object* v_res_1810_; 
v_sz_boxed_1808_ = lean_unbox_usize(v_sz_1805_);
lean_dec(v_sz_1805_);
v_i_boxed_1809_ = lean_unbox_usize(v_i_1806_);
lean_dec(v_i_1806_);
v_res_1810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_sz_boxed_1808_, v_i_boxed_1809_, v_bs_1807_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_a_1811_){
_start:
{
size_t v_sz_1812_; size_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v_sz_1812_ = lean_array_size(v_a_1811_);
v___x_1813_ = ((size_t)0ULL);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_sz_1812_, v___x_1813_, v_a_1811_);
v___x_1815_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* v_env_1816_, lean_object* v_incrFile_1817_, lean_object* v_snapToSave_1818_){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = l_Lean_getRegularInitAttrModIdxs(v_env_1816_);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v_snapToSave_1818_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__14(v_env_1816_, v_incrFile_1817_, v___x_1821_);
lean_dec_ref_known(v___x_1821_, 2);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1824_; lean_object* v_regions_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v___x_1824_ = l_Lean_Environment_header(v_env_1816_);
v_regions_1825_ = lean_ctor_get(v___x_1824_, 2);
lean_inc_ref(v_regions_1825_);
lean_dec_ref(v___x_1824_);
v___x_1826_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1825_);
lean_dec_ref(v_regions_1825_);
v___x_1827_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
v___x_1828_ = l_System_FilePath_addExtension(v_incrFile_1817_, v___x_1827_);
v___x_1829_ = l_Array_toJson___at___00Lean_Elab_runFrontend_spec__2(v___x_1826_);
v___x_1830_ = l_Lean_Json_compress(v___x_1829_);
v___x_1831_ = l_IO_FS_writeFile(v___x_1828_, v___x_1830_);
lean_dec_ref(v___x_1830_);
lean_dec_ref(v___x_1828_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1839_; 
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1839_ == 0)
{
lean_object* v_unused_1840_; 
v_unused_1840_ = lean_ctor_get(v___x_1831_, 0);
lean_dec(v_unused_1840_);
v___x_1833_ = v___x_1831_;
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
else
{
lean_dec(v___x_1831_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1839_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1835_ = lean_runtime_forget(v_a_1823_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1835_);
v___x_1837_ = v___x_1833_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
lean_dec(v_a_1823_);
return v___x_1831_;
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec_ref(v_incrFile_1817_);
v_a_1841_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1822_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1822_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object* v_env_1849_, lean_object* v_incrFile_1850_, lean_object* v_snapToSave_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Elab_runFrontend___lam__4(v_env_1849_, v_incrFile_1850_, v_snapToSave_1851_);
lean_dec_ref(v_env_1849_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_fileMap_1854_, lean_object* v_env_1855_, lean_object* v___x_1856_, lean_object* v_opts_1857_, lean_object* v_val_1858_, uint8_t v___x_1859_, uint8_t v_a_1860_){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1862_ = l_Lean_Linter_recordLints(v_fileMap_1854_, v_env_1855_, v___x_1856_);
v___x_1863_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1864_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(v_opts_1857_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_writeModule(v___x_1862_, v_val_1858_, v___x_1859_);
return v___x_1865_;
}
else
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_writeModule(v___x_1862_, v_val_1858_, v_a_1860_);
return v___x_1866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_fileMap_1867_, lean_object* v_env_1868_, lean_object* v___x_1869_, lean_object* v_opts_1870_, lean_object* v_val_1871_, lean_object* v___x_1872_, lean_object* v_a_1873_, lean_object* v___y_1874_){
_start:
{
uint8_t v___x_6640__boxed_1875_; uint8_t v_a_6641__boxed_1876_; lean_object* v_res_1877_; 
v___x_6640__boxed_1875_ = lean_unbox(v___x_1872_);
v_a_6641__boxed_1876_ = lean_unbox(v_a_1873_);
v_res_1877_ = l_Lean_Elab_runFrontend___lam__3(v_fileMap_1867_, v_env_1868_, v___x_1869_, v_opts_1870_, v_val_1871_, v___x_6640__boxed_1875_, v_a_6641__boxed_1876_);
lean_dec_ref(v_opts_1870_);
lean_dec_ref(v___x_1869_);
lean_dec_ref(v_fileMap_1867_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_1878_, size_t v_i_1879_, size_t v_stop_1880_, lean_object* v_b_1881_){
_start:
{
uint8_t v___x_1883_; 
v___x_1883_ = lean_usize_dec_eq(v_i_1879_, v_stop_1880_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_array_uget_borrowed(v_as_1878_, v_i_1879_);
lean_inc(v___x_1884_);
v___x_1885_ = lean_load_dynlib(v___x_1884_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; size_t v___x_1887_; size_t v___x_1888_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_add(v_i_1879_, v___x_1887_);
v_i_1879_ = v___x_1888_;
v_b_1881_ = v_a_1886_;
goto _start;
}
else
{
return v___x_1885_;
}
}
else
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v_b_1881_);
return v___x_1890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_1891_, lean_object* v_i_1892_, lean_object* v_stop_1893_, lean_object* v_b_1894_, lean_object* v___y_1895_){
_start:
{
size_t v_i_boxed_1896_; size_t v_stop_boxed_1897_; lean_object* v_res_1898_; 
v_i_boxed_1896_ = lean_unbox_usize(v_i_1892_);
lean_dec(v_i_1892_);
v_stop_boxed_1897_ = lean_unbox_usize(v_stop_1893_);
lean_dec(v_stop_1893_);
v_res_1898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_1891_, v_i_boxed_1896_, v_stop_boxed_1897_, v_b_1894_);
lean_dec_ref(v_as_1891_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object* v_setup_x3f_1899_, lean_object* v___f_1900_, lean_object* v___x_1901_, lean_object* v_plugins_1902_, uint32_t v_trustLevel_1903_, uint8_t v___x_1904_, lean_object* v_mainModuleName_1905_, lean_object* v_stx_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___y_1910_; lean_object* v___y_1911_; uint8_t v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; 
if (lean_obj_tag(v_setup_x3f_1899_) == 1)
{
lean_object* v_val_1923_; lean_object* v_name_1924_; lean_object* v_package_x3f_1925_; uint8_t v_isModule_1926_; lean_object* v_imports_x3f_1927_; lean_object* v_importArts_1928_; lean_object* v_dynlibs_1929_; lean_object* v_plugins_1930_; lean_object* v_options_1931_; lean_object* v___y_1938_; lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
lean_dec(v_mainModuleName_1905_);
v_val_1923_ = lean_ctor_get(v_setup_x3f_1899_, 0);
lean_inc(v_val_1923_);
lean_dec_ref_known(v_setup_x3f_1899_, 1);
v_name_1924_ = lean_ctor_get(v_val_1923_, 0);
lean_inc(v_name_1924_);
v_package_x3f_1925_ = lean_ctor_get(v_val_1923_, 1);
lean_inc(v_package_x3f_1925_);
v_isModule_1926_ = lean_ctor_get_uint8(v_val_1923_, sizeof(void*)*7);
v_imports_x3f_1927_ = lean_ctor_get(v_val_1923_, 2);
lean_inc(v_imports_x3f_1927_);
v_importArts_1928_ = lean_ctor_get(v_val_1923_, 3);
lean_inc(v_importArts_1928_);
v_dynlibs_1929_ = lean_ctor_get(v_val_1923_, 4);
lean_inc_ref(v_dynlibs_1929_);
v_plugins_1930_ = lean_ctor_get(v_val_1923_, 5);
lean_inc_ref(v_plugins_1930_);
v_options_1931_ = lean_ctor_get(v_val_1923_, 6);
lean_inc(v_options_1931_);
lean_dec(v_val_1923_);
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = lean_array_get_size(v_dynlibs_1929_);
v___x_1949_ = lean_nat_dec_lt(v___x_1947_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_dec_ref(v_dynlibs_1929_);
goto v___jp_1932_;
}
else
{
lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = lean_box(0);
v___x_1951_ = lean_nat_dec_le(v___x_1948_, v___x_1948_);
if (v___x_1951_ == 0)
{
if (v___x_1949_ == 0)
{
lean_dec_ref(v_dynlibs_1929_);
goto v___jp_1932_;
}
else
{
size_t v___x_1952_; size_t v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = ((size_t)0ULL);
v___x_1953_ = lean_usize_of_nat(v___x_1948_);
v___x_1954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_1929_, v___x_1952_, v___x_1953_, v___x_1950_);
lean_dec_ref(v_dynlibs_1929_);
v___y_1938_ = v___x_1954_;
goto v___jp_1937_;
}
}
else
{
size_t v___x_1955_; size_t v___x_1956_; lean_object* v___x_1957_; 
v___x_1955_ = ((size_t)0ULL);
v___x_1956_ = lean_usize_of_nat(v___x_1948_);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_1929_, v___x_1955_, v___x_1956_, v___x_1950_);
lean_dec_ref(v_dynlibs_1929_);
v___y_1938_ = v___x_1957_;
goto v___jp_1937_;
}
}
v___jp_1932_:
{
uint8_t v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_1906_);
v___x_1934_ = lean_strict_or(v_isModule_1926_, v___x_1933_);
if (lean_obj_tag(v_imports_x3f_1927_) == 0)
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_1906_, v___x_1904_);
v___y_1910_ = v_package_x3f_1925_;
v___y_1911_ = v_plugins_1930_;
v___y_1912_ = v___x_1934_;
v___y_1913_ = v_importArts_1928_;
v___y_1914_ = v_name_1924_;
v___y_1915_ = v_options_1931_;
v___y_1916_ = v___x_1935_;
goto v___jp_1909_;
}
else
{
lean_object* v_val_1936_; 
lean_dec(v_stx_1906_);
v_val_1936_ = lean_ctor_get(v_imports_x3f_1927_, 0);
lean_inc(v_val_1936_);
lean_dec_ref_known(v_imports_x3f_1927_, 1);
v___y_1910_ = v_package_x3f_1925_;
v___y_1911_ = v_plugins_1930_;
v___y_1912_ = v___x_1934_;
v___y_1913_ = v_importArts_1928_;
v___y_1914_ = v_name_1924_;
v___y_1915_ = v_options_1931_;
v___y_1916_ = v_val_1936_;
goto v___jp_1909_;
}
}
v___jp_1937_:
{
if (lean_obj_tag(v___y_1938_) == 0)
{
lean_dec_ref_known(v___y_1938_, 1);
goto v___jp_1932_;
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_options_1931_);
lean_dec_ref(v_plugins_1930_);
lean_dec(v_importArts_1928_);
lean_dec(v_imports_x3f_1927_);
lean_dec(v_package_x3f_1925_);
lean_dec(v_name_1924_);
lean_dec(v_stx_1906_);
lean_dec_ref(v_plugins_1902_);
lean_dec_ref(v___x_1901_);
lean_dec_ref(v___f_1900_);
v_a_1939_ = lean_ctor_get(v___y_1938_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___y_1938_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___y_1938_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___y_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
else
{
lean_object* v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
lean_dec_ref(v___f_1900_);
lean_dec(v_setup_x3f_1899_);
v___x_1958_ = lean_box(0);
v___x_1959_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_1906_);
v___x_1960_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_1906_, v___x_1904_);
v___x_1961_ = lean_box(1);
v___x_1962_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_1962_, 0, v_mainModuleName_1905_);
lean_ctor_set(v___x_1962_, 1, v___x_1958_);
lean_ctor_set(v___x_1962_, 2, v___x_1960_);
lean_ctor_set(v___x_1962_, 3, v___x_1901_);
lean_ctor_set(v___x_1962_, 4, v___x_1961_);
lean_ctor_set(v___x_1962_, 5, v_plugins_1902_);
lean_ctor_set_uint8(v___x_1962_, sizeof(void*)*6 + 4, v___x_1959_);
lean_ctor_set_uint32(v___x_1962_, sizeof(void*)*6, v_trustLevel_1903_);
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
return v___x_1964_;
}
v___jp_1909_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1917_ = l_Lean_LeanOptions_toOptions(v___y_1915_);
v___x_1918_ = l_Lean_Options_mergeBy(v___f_1900_, v___x_1901_, v___x_1917_);
v___x_1919_ = l_Array_append___redArg(v_plugins_1902_, v___y_1911_);
lean_dec_ref(v___y_1911_);
v___x_1920_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_1920_, 0, v___y_1914_);
lean_ctor_set(v___x_1920_, 1, v___y_1910_);
lean_ctor_set(v___x_1920_, 2, v___y_1916_);
lean_ctor_set(v___x_1920_, 3, v___x_1918_);
lean_ctor_set(v___x_1920_, 4, v___y_1913_);
lean_ctor_set(v___x_1920_, 5, v___x_1919_);
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*6 + 4, v___y_1912_);
lean_ctor_set_uint32(v___x_1920_, sizeof(void*)*6, v_trustLevel_1903_);
v___x_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5___boxed(lean_object* v_setup_x3f_1965_, lean_object* v___f_1966_, lean_object* v___x_1967_, lean_object* v_plugins_1968_, lean_object* v_trustLevel_1969_, lean_object* v___x_1970_, lean_object* v_mainModuleName_1971_, lean_object* v_stx_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
uint32_t v_trustLevel_boxed_1975_; uint8_t v___x_6685__boxed_1976_; lean_object* v_res_1977_; 
v_trustLevel_boxed_1975_ = lean_unbox_uint32(v_trustLevel_1969_);
lean_dec(v_trustLevel_1969_);
v___x_6685__boxed_1976_ = lean_unbox(v___x_1970_);
v_res_1977_ = l_Lean_Elab_runFrontend___lam__5(v_setup_x3f_1965_, v___f_1966_, v___x_1967_, v_plugins_1968_, v_trustLevel_boxed_1975_, v___x_6685__boxed_1976_, v_mainModuleName_1971_, v_stx_1972_, v___y_1973_);
lean_dec_ref(v___y_1973_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_1981_, lean_object* v_k_1982_, uint8_t v_v_1983_){
_start:
{
lean_object* v_map_1984_; uint8_t v_hasTrace_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1999_; 
v_map_1984_ = lean_ctor_get(v_o_1981_, 0);
v_hasTrace_1985_ = lean_ctor_get_uint8(v_o_1981_, sizeof(void*)*1);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_o_1981_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1987_ = v_o_1981_;
v_isShared_1988_ = v_isSharedCheck_1999_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_map_1984_);
lean_dec(v_o_1981_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1999_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1989_, 0, v_v_1983_);
lean_inc(v_k_1982_);
v___x_1990_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1982_, v___x_1989_, v_map_1984_);
if (v_hasTrace_1985_ == 0)
{
lean_object* v___x_1991_; uint8_t v___x_1992_; lean_object* v___x_1994_; 
v___x_1991_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_1992_ = l_Lean_Name_isPrefixOf(v___x_1991_, v_k_1982_);
lean_dec(v_k_1982_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_1990_);
v___x_1994_ = v___x_1987_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1990_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_ctor_set_uint8(v___x_1994_, sizeof(void*)*1, v___x_1992_);
return v___x_1994_;
}
}
else
{
lean_object* v___x_1997_; 
lean_dec(v_k_1982_);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_1990_);
v___x_1997_ = v___x_1987_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_1998_, sizeof(void*)*1, v_hasTrace_1985_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_2000_, lean_object* v_k_2001_, lean_object* v_v_2002_){
_start:
{
uint8_t v_v_boxed_2003_; lean_object* v_res_2004_; 
v_v_boxed_2003_ = lean_unbox(v_v_2002_);
v_res_2004_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2000_, v_k_2001_, v_v_boxed_2003_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_2005_, lean_object* v_opt_2006_, uint8_t v_val_2007_){
_start:
{
lean_object* v_name_2008_; lean_object* v___x_2009_; 
v_name_2008_ = lean_ctor_get(v_opt_2006_, 0);
lean_inc(v_name_2008_);
lean_dec_ref(v_opt_2006_);
v___x_2009_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_2005_, v_name_2008_, v_val_2007_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_2010_, lean_object* v_opt_2011_, lean_object* v_val_2012_){
_start:
{
uint8_t v_val_boxed_2013_; lean_object* v_res_2014_; 
v_val_boxed_2013_ = lean_unbox(v_val_2012_);
v_res_2014_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2010_, v_opt_2011_, v_val_boxed_2013_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_2015_, lean_object* v_opt_2016_, uint8_t v_val_2017_){
_start:
{
lean_object* v_name_2018_; lean_object* v_map_2019_; uint8_t v___x_2020_; 
v_name_2018_ = lean_ctor_get(v_opt_2016_, 0);
v_map_2019_ = lean_ctor_get(v_opts_2015_, 0);
v___x_2020_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_2018_, v_map_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2015_, v_opt_2016_, v_val_2017_);
return v___x_2021_;
}
else
{
lean_dec_ref(v_opt_2016_);
return v_opts_2015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_2022_, lean_object* v_opt_2023_, lean_object* v_val_2024_){
_start:
{
uint8_t v_val_boxed_2025_; lean_object* v_res_2026_; 
v_val_boxed_2025_ = lean_unbox(v_val_2024_);
v_res_2026_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2022_, v_opt_2023_, v_val_boxed_2025_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_as_2027_, size_t v_i_2028_, size_t v_stop_2029_, lean_object* v_b_2030_){
_start:
{
lean_object* v___y_2032_; uint8_t v___x_2036_; 
v___x_2036_ = lean_usize_dec_eq(v_i_2028_, v_stop_2029_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v_infoTree_x3f_2038_; 
v___x_2037_ = lean_array_uget_borrowed(v_as_2027_, v_i_2028_);
v_infoTree_x3f_2038_ = lean_ctor_get(v___x_2037_, 2);
if (lean_obj_tag(v_infoTree_x3f_2038_) == 1)
{
lean_object* v_val_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_val_2039_ = lean_ctor_get(v_infoTree_x3f_2038_, 0);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_mk_empty_array_with_capacity(v___x_2040_);
lean_inc(v_val_2039_);
v___x_2042_ = lean_array_push(v___x_2041_, v_val_2039_);
v___x_2043_ = l_Array_append___redArg(v_b_2030_, v___x_2042_);
lean_dec_ref(v___x_2042_);
v___y_2032_ = v___x_2043_;
goto v___jp_2031_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_2045_ = l_Array_append___redArg(v_b_2030_, v___x_2044_);
v___y_2032_ = v___x_2045_;
goto v___jp_2031_;
}
}
else
{
return v_b_2030_;
}
v___jp_2031_:
{
size_t v___x_2033_; size_t v___x_2034_; 
v___x_2033_ = ((size_t)1ULL);
v___x_2034_ = lean_usize_add(v_i_2028_, v___x_2033_);
v_i_2028_ = v___x_2034_;
v_b_2030_ = v___y_2032_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_as_2046_, lean_object* v_i_2047_, lean_object* v_stop_2048_, lean_object* v_b_2049_){
_start:
{
size_t v_i_boxed_2050_; size_t v_stop_boxed_2051_; lean_object* v_res_2052_; 
v_i_boxed_2050_ = lean_unbox_usize(v_i_2047_);
lean_dec(v_i_2047_);
v_stop_boxed_2051_ = lean_unbox_usize(v_stop_2048_);
lean_dec(v_stop_2048_);
v_res_2052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v_as_2046_, v_i_boxed_2050_, v_stop_boxed_2051_, v_b_2049_);
lean_dec_ref(v_as_2046_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__4(size_t v_sz_2053_, size_t v_i_2054_, lean_object* v_bs_2055_){
_start:
{
uint8_t v___x_2056_; 
v___x_2056_ = lean_usize_dec_lt(v_i_2054_, v_sz_2053_);
if (v___x_2056_ == 0)
{
return v_bs_2055_;
}
else
{
lean_object* v_v_2057_; lean_object* v_traces_2058_; lean_object* v___x_2059_; lean_object* v_bs_x27_2060_; size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; 
v_v_2057_ = lean_array_uget_borrowed(v_bs_2055_, v_i_2054_);
v_traces_2058_ = lean_ctor_get(v_v_2057_, 3);
lean_inc_ref(v_traces_2058_);
v___x_2059_ = lean_unsigned_to_nat(0u);
v_bs_x27_2060_ = lean_array_uset(v_bs_2055_, v_i_2054_, v___x_2059_);
v___x_2061_ = ((size_t)1ULL);
v___x_2062_ = lean_usize_add(v_i_2054_, v___x_2061_);
v___x_2063_ = lean_array_uset(v_bs_x27_2060_, v_i_2054_, v_traces_2058_);
v_i_2054_ = v___x_2062_;
v_bs_2055_ = v___x_2063_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_sz_2065_, lean_object* v_i_2066_, lean_object* v_bs_2067_){
_start:
{
size_t v_sz_boxed_2068_; size_t v_i_boxed_2069_; lean_object* v_res_2070_; 
v_sz_boxed_2068_ = lean_unbox_usize(v_sz_2065_);
lean_dec(v_sz_2065_);
v_i_boxed_2069_ = lean_unbox_usize(v_i_2066_);
lean_dec(v_i_2066_);
v_res_2070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__4(v_sz_boxed_2068_, v_i_boxed_2069_, v_bs_2067_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_2071_, size_t v_i_2072_, size_t v_stop_2073_, lean_object* v_b_2074_){
_start:
{
uint8_t v___x_2075_; 
v___x_2075_ = lean_usize_dec_eq(v_i_2072_, v_stop_2073_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; size_t v___x_2080_; size_t v___x_2081_; 
v___x_2076_ = lean_array_uget_borrowed(v_as_2071_, v_i_2072_);
v___x_2077_ = 2;
v___x_2078_ = lean_box(v___x_2077_);
lean_inc(v___x_2076_);
v___x_2079_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2076_, v___x_2078_, v_b_2074_);
v___x_2080_ = ((size_t)1ULL);
v___x_2081_ = lean_usize_add(v_i_2072_, v___x_2080_);
v_i_2072_ = v___x_2081_;
v_b_2074_ = v___x_2079_;
goto _start;
}
else
{
return v_b_2074_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_2083_, lean_object* v_i_2084_, lean_object* v_stop_2085_, lean_object* v_b_2086_){
_start:
{
size_t v_i_boxed_2087_; size_t v_stop_boxed_2088_; lean_object* v_res_2089_; 
v_i_boxed_2087_ = lean_unbox_usize(v_i_2084_);
lean_dec(v_i_2084_);
v_stop_boxed_2088_ = lean_unbox_usize(v_stop_2085_);
lean_dec(v_stop_2085_);
v_res_2089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_2083_, v_i_boxed_2087_, v_stop_boxed_2088_, v_b_2086_);
lean_dec_ref(v_as_2083_);
return v_res_2089_;
}
}
static double _init_l_Lean_Elab_runFrontend___closed__3(void){
_start:
{
lean_object* v___x_2094_; double v___x_2095_; 
v___x_2094_ = lean_unsigned_to_nat(1000000000u);
v___x_2095_ = lean_float_of_nat(v___x_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_2097_, lean_object* v_opts_2098_, lean_object* v_fileName_2099_, lean_object* v_mainModuleName_2100_, uint32_t v_trustLevel_2101_, lean_object* v_oleanFileName_x3f_2102_, lean_object* v_ileanFileName_x3f_2103_, uint8_t v_jsonOutput_2104_, lean_object* v_errorOnKinds_2105_, lean_object* v_plugins_2106_, uint8_t v_printStats_2107_, lean_object* v_setup_x3f_2108_, lean_object* v_incrSaveFileName_x3f_2109_, lean_object* v_incrLoadFileName_x3f_2110_, lean_object* v_incrHeaderSaveFileName_x3f_2111_){
_start:
{
lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___x_2119_; lean_object* v___f_2120_; lean_object* v___f_2121_; lean_object* v___f_2122_; lean_object* v___x_2123_; double v___x_2124_; double v___x_2125_; double v___x_2126_; uint8_t v___x_2127_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2240_; uint8_t v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; uint8_t v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2272_; uint8_t v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; uint8_t v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2292_; uint8_t v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; uint8_t v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2362_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v_a_2390_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v___y_2419_; 
v___x_2119_ = lean_io_mono_nanos_now();
v___f_2120_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___f_2121_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__1));
v___f_2122_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__2));
v___x_2123_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2124_ = lean_float_of_nat(v___x_2119_);
v___x_2125_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__3, &l_Lean_Elab_runFrontend___closed__3_once, _init_l_Lean_Elab_runFrontend___closed__3);
v___x_2126_ = lean_float_div(v___x_2124_, v___x_2125_);
v___x_2127_ = 1;
v___x_2190_ = lean_string_utf8_byte_size(v_input_2097_);
v___x_2191_ = l_Lean_Parser_mkInputContext___redArg(v_input_2097_, v_fileName_2099_, v___x_2127_, v___x_2190_);
v___x_2417_ = l_Lean_internal_cmdlineSnapshots;
if (lean_obj_tag(v_incrSaveFileName_x3f_2109_) == 0)
{
v___y_2419_ = v___x_2127_;
goto v___jp_2418_;
}
else
{
uint8_t v___x_2461_; 
v___x_2461_ = 0;
v___y_2419_ = v___x_2461_;
goto v___jp_2418_;
}
v___jp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = lean_runtime_forget(v___y_2115_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___y_2114_);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
v___jp_2128_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = l_Lean_trace_profiler_output;
v___x_2134_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__3(v___y_2130_, v___x_2133_);
if (lean_obj_tag(v___x_2134_) == 1)
{
lean_object* v_val_2135_; lean_object* v___x_2136_; size_t v_sz_2137_; size_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_dec_ref(v___y_2131_);
v_val_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_val_2135_);
lean_dec_ref_known(v___x_2134_, 1);
lean_inc_ref(v___y_2132_);
v___x_2136_ = l_Lean_Language_SnapshotTree_getAll(v___y_2132_);
v_sz_2137_ = lean_array_size(v___x_2136_);
v___x_2138_ = ((size_t)0ULL);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__4(v_sz_2137_, v___x_2138_, v___x_2136_);
v___x_2140_ = l_Lean_Name_toString(v_mainModuleName_2100_, v___x_2127_);
v___x_2141_ = l_Lean_Firefox_Profile_export(v___x_2140_, v___x_2126_, v___x_2139_, v___y_2130_);
lean_dec_ref(v___y_2130_);
lean_dec_ref(v___x_2139_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2142_);
v___x_2144_ = l_Lean_Json_compress(v___x_2143_);
v___x_2145_ = l_IO_FS_writeFile(v_val_2135_, v___x_2144_);
lean_dec_ref(v___x_2144_);
lean_dec(v_val_2135_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_dec_ref_known(v___x_2145_, 1);
v___y_2114_ = v___y_2129_;
v___y_2115_ = v___y_2132_;
goto v___jp_2113_;
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec_ref(v___y_2132_);
lean_dec_ref(v___y_2129_);
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_val_2135_);
lean_dec_ref(v___y_2132_);
lean_dec_ref(v___y_2129_);
v_a_2154_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2141_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2141_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
lean_dec(v___x_2134_);
v___x_2162_ = l_Lean_trace_profiler_serve;
v___x_2163_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(v___y_2131_, v___x_2162_);
lean_dec_ref(v___y_2131_);
if (v___x_2163_ == 0)
{
lean_dec_ref(v___y_2130_);
lean_dec(v_mainModuleName_2100_);
v___y_2114_ = v___y_2129_;
v___y_2115_ = v___y_2132_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2164_; size_t v_sz_2165_; size_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_inc_ref(v___y_2132_);
v___x_2164_ = l_Lean_Language_SnapshotTree_getAll(v___y_2132_);
v_sz_2165_ = lean_array_size(v___x_2164_);
v___x_2166_ = ((size_t)0ULL);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__4(v_sz_2165_, v___x_2166_, v___x_2164_);
v___x_2168_ = l_Lean_Name_toString(v_mainModuleName_2100_, v___x_2127_);
v___x_2169_ = l_Lean_Firefox_Profile_export(v___x_2168_, v___x_2126_, v___x_2167_, v___y_2130_);
lean_dec_ref(v___y_2130_);
lean_dec_ref(v___x_2167_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2170_);
v___x_2172_ = l_Lean_Json_compress(v___x_2171_);
v___x_2173_ = l_Lean_Firefox_Profile_serve(v___x_2172_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_dec_ref_known(v___x_2173_, 1);
v___y_2114_ = v___y_2129_;
v___y_2115_ = v___y_2132_;
goto v___jp_2113_;
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec_ref(v___y_2132_);
lean_dec_ref(v___y_2129_);
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec_ref(v___y_2132_);
lean_dec_ref(v___y_2129_);
v_a_2182_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2169_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2169_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
}
v___jp_2192_:
{
lean_object* v_fileMap_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v_fst_2204_; lean_object* v_snd_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_fileMap_2200_ = lean_ctor_get(v___x_2191_, 2);
lean_inc_ref(v_fileMap_2200_);
lean_dec_ref(v___x_2191_);
v___x_2201_ = 0;
v___x_2202_ = l_Lean_Server_findModuleRefs(v_fileMap_2200_, v___y_2199_, v___x_2201_, v___x_2201_);
lean_dec_ref(v___y_2199_);
v___x_2203_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_2202_);
v_fst_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_fst_2204_);
v_snd_2205_ = lean_ctor_get(v___x_2203_, 1);
lean_inc(v_snd_2205_);
lean_dec_ref(v___x_2203_);
v___x_2206_ = lean_unsigned_to_nat(5u);
v___x_2207_ = l_Lean_Server_collectImports(v___y_2197_);
lean_inc(v_mainModuleName_2100_);
v___x_2208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2206_);
lean_ctor_set(v___x_2208_, 1, v_mainModuleName_2100_);
lean_ctor_set(v___x_2208_, 2, v___x_2207_);
lean_ctor_set(v___x_2208_, 3, v_fst_2204_);
lean_ctor_set(v___x_2208_, 4, v_snd_2205_);
v___x_2209_ = l_Lean_Server_instToJsonIlean_toJson(v___x_2208_);
v___x_2210_ = l_Lean_Json_compress(v___x_2209_);
v___x_2211_ = l_IO_FS_writeFile(v___y_2196_, v___x_2210_);
lean_dec_ref(v___x_2210_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_dec_ref_known(v___x_2211_, 1);
v___y_2129_ = v___y_2194_;
v___y_2130_ = v___y_2193_;
v___y_2131_ = v___y_2195_;
v___y_2132_ = v___y_2198_;
goto v___jp_2128_;
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec_ref(v___y_2198_);
lean_dec_ref(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v_mainModuleName_2100_);
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
v___jp_2220_:
{
if (lean_obj_tag(v_ileanFileName_x3f_2103_) == 1)
{
lean_object* v_val_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
v_val_2227_ = lean_ctor_get(v_ileanFileName_x3f_2103_, 0);
lean_inc_ref(v___y_2226_);
v___x_2228_ = l_Lean_Language_SnapshotTree_getAll(v___y_2226_);
v___x_2229_ = lean_mk_empty_array_with_capacity(v___y_2223_);
v___x_2230_ = lean_array_get_size(v___x_2228_);
v___x_2231_ = lean_nat_dec_lt(v___y_2223_, v___x_2230_);
lean_dec(v___y_2223_);
if (v___x_2231_ == 0)
{
lean_dec_ref(v___x_2228_);
v___y_2193_ = v___y_2222_;
v___y_2194_ = v___y_2221_;
v___y_2195_ = v___y_2224_;
v___y_2196_ = v_val_2227_;
v___y_2197_ = v___y_2225_;
v___y_2198_ = v___y_2226_;
v___y_2199_ = v___x_2229_;
goto v___jp_2192_;
}
else
{
uint8_t v___x_2232_; 
v___x_2232_ = lean_nat_dec_le(v___x_2230_, v___x_2230_);
if (v___x_2232_ == 0)
{
if (v___x_2231_ == 0)
{
lean_dec_ref(v___x_2228_);
v___y_2193_ = v___y_2222_;
v___y_2194_ = v___y_2221_;
v___y_2195_ = v___y_2224_;
v___y_2196_ = v_val_2227_;
v___y_2197_ = v___y_2225_;
v___y_2198_ = v___y_2226_;
v___y_2199_ = v___x_2229_;
goto v___jp_2192_;
}
else
{
size_t v___x_2233_; size_t v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = ((size_t)0ULL);
v___x_2234_ = lean_usize_of_nat(v___x_2230_);
v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v___x_2228_, v___x_2233_, v___x_2234_, v___x_2229_);
lean_dec_ref(v___x_2228_);
v___y_2193_ = v___y_2222_;
v___y_2194_ = v___y_2221_;
v___y_2195_ = v___y_2224_;
v___y_2196_ = v_val_2227_;
v___y_2197_ = v___y_2225_;
v___y_2198_ = v___y_2226_;
v___y_2199_ = v___x_2235_;
goto v___jp_2192_;
}
}
else
{
size_t v___x_2236_; size_t v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = ((size_t)0ULL);
v___x_2237_ = lean_usize_of_nat(v___x_2230_);
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v___x_2228_, v___x_2236_, v___x_2237_, v___x_2229_);
lean_dec_ref(v___x_2228_);
v___y_2193_ = v___y_2222_;
v___y_2194_ = v___y_2221_;
v___y_2195_ = v___y_2224_;
v___y_2196_ = v_val_2227_;
v___y_2197_ = v___y_2225_;
v___y_2198_ = v___y_2226_;
v___y_2199_ = v___x_2238_;
goto v___jp_2192_;
}
}
}
else
{
lean_dec(v___y_2225_);
lean_dec(v___y_2223_);
lean_dec_ref(v___x_2191_);
v___y_2129_ = v___y_2221_;
v___y_2130_ = v___y_2222_;
v___y_2131_ = v___y_2224_;
v___y_2132_ = v___y_2226_;
goto v___jp_2128_;
}
}
v___jp_2239_:
{
if (v___y_2245_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_2102_) == 1)
{
lean_object* v_val_2250_; lean_object* v_fileMap_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___f_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v_val_2250_ = lean_ctor_get(v_oleanFileName_x3f_2102_, 0);
lean_inc(v_val_2250_);
lean_dec_ref_known(v_oleanFileName_x3f_2102_, 1);
v_fileMap_2251_ = lean_ctor_get(v___x_2191_, 2);
lean_inc_ref(v_fileMap_2251_);
v___x_2252_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__4));
v___x_2253_ = lean_box(0);
v___x_2254_ = lean_mk_empty_array_with_capacity(v___y_2246_);
lean_inc_ref(v___y_2249_);
v___x_2255_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___y_2249_, v___x_2253_, v___x_2254_);
v___x_2256_ = lean_box(v___x_2127_);
v___x_2257_ = lean_box(v___y_2241_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2258_, 0, v_fileMap_2251_);
lean_closure_set(v___f_2258_, 1, v___y_2240_);
lean_closure_set(v___f_2258_, 2, v___x_2255_);
lean_closure_set(v___f_2258_, 3, v___y_2242_);
lean_closure_set(v___f_2258_, 4, v_val_2250_);
lean_closure_set(v___f_2258_, 5, v___x_2256_);
lean_closure_set(v___f_2258_, 6, v___x_2257_);
v___x_2259_ = lean_box(0);
v___x_2260_ = l_Lean_profileitIOUnsafe___redArg(v___x_2252_, v___y_2247_, v___f_2258_, v___x_2259_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_dec_ref_known(v___x_2260_, 1);
v___y_2221_ = v___y_2244_;
v___y_2222_ = v___y_2243_;
v___y_2223_ = v___y_2246_;
v___y_2224_ = v___y_2247_;
v___y_2225_ = v___y_2248_;
v___y_2226_ = v___y_2249_;
goto v___jp_2220_;
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec_ref(v___x_2191_);
lean_dec(v_mainModuleName_2100_);
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2260_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
else
{
lean_dec_ref(v___y_2242_);
lean_dec_ref(v___y_2240_);
lean_dec(v_oleanFileName_x3f_2102_);
v___y_2221_ = v___y_2244_;
v___y_2222_ = v___y_2243_;
v___y_2223_ = v___y_2246_;
v___y_2224_ = v___y_2247_;
v___y_2225_ = v___y_2248_;
v___y_2226_ = v___y_2249_;
goto v___jp_2220_;
}
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v___y_2240_);
lean_dec_ref(v___x_2191_);
lean_dec(v_oleanFileName_x3f_2102_);
lean_dec(v_mainModuleName_2100_);
v___x_2269_ = lean_box(0);
v___x_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
return v___x_2270_;
}
}
v___jp_2271_:
{
if (v_printStats_2107_ == 0)
{
v___y_2240_ = v___y_2272_;
v___y_2241_ = v___y_2273_;
v___y_2242_ = v___y_2274_;
v___y_2243_ = v___y_2276_;
v___y_2244_ = v___y_2275_;
v___y_2245_ = v___y_2277_;
v___y_2246_ = v___y_2278_;
v___y_2247_ = v___y_2279_;
v___y_2248_ = v___y_2280_;
v___y_2249_ = v___y_2281_;
goto v___jp_2239_;
}
else
{
lean_object* v___x_2282_; 
lean_inc_ref(v___y_2275_);
v___x_2282_ = l_Lean_Environment_displayStats(v___y_2275_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_dec_ref_known(v___x_2282_, 1);
v___y_2240_ = v___y_2272_;
v___y_2241_ = v___y_2273_;
v___y_2242_ = v___y_2274_;
v___y_2243_ = v___y_2276_;
v___y_2244_ = v___y_2275_;
v___y_2245_ = v___y_2277_;
v___y_2246_ = v___y_2278_;
v___y_2247_ = v___y_2279_;
v___y_2248_ = v___y_2280_;
v___y_2249_ = v___y_2281_;
goto v___jp_2239_;
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v___x_2191_);
lean_dec(v_oleanFileName_x3f_2102_);
lean_dec(v_mainModuleName_2100_);
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
v___jp_2291_:
{
if (lean_obj_tag(v_incrHeaderSaveFileName_x3f_2111_) == 1)
{
lean_object* v_val_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_val_2303_ = lean_ctor_get(v_incrHeaderSaveFileName_x3f_2111_, 0);
lean_inc(v_val_2303_);
lean_dec_ref_known(v_incrHeaderSaveFileName_x3f_2111_, 1);
v___x_2304_ = l_Lean_Language_Lean_truncateToHeader(v___y_2299_);
v___x_2305_ = lean_apply_3(v___y_2295_, v_val_2303_, v___x_2304_, lean_box(0));
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_dec_ref_known(v___x_2305_, 1);
lean_inc_ref(v___y_2294_);
v___y_2272_ = v___y_2292_;
v___y_2273_ = v___y_2293_;
v___y_2274_ = v___y_2294_;
v___y_2275_ = v___y_2297_;
v___y_2276_ = v___y_2296_;
v___y_2277_ = v___y_2298_;
v___y_2278_ = v___y_2300_;
v___y_2279_ = v___y_2294_;
v___y_2280_ = v___y_2301_;
v___y_2281_ = v___y_2302_;
goto v___jp_2271_;
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec_ref(v___y_2294_);
lean_dec_ref(v___y_2292_);
lean_dec_ref(v___x_2191_);
lean_dec(v_oleanFileName_x3f_2102_);
lean_dec(v_mainModuleName_2100_);
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
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
else
{
lean_dec_ref(v___y_2299_);
lean_dec_ref(v___y_2295_);
lean_dec(v_incrHeaderSaveFileName_x3f_2111_);
lean_inc_ref(v___y_2294_);
v___y_2272_ = v___y_2292_;
v___y_2273_ = v___y_2293_;
v___y_2274_ = v___y_2294_;
v___y_2275_ = v___y_2297_;
v___y_2276_ = v___y_2296_;
v___y_2277_ = v___y_2298_;
v___y_2278_ = v___y_2300_;
v___y_2279_ = v___y_2294_;
v___y_2280_ = v___y_2301_;
v___y_2281_ = v___y_2302_;
goto v___jp_2271_;
}
}
v___jp_2314_:
{
lean_object* v___x_2321_; 
lean_inc_ref(v___y_2319_);
v___x_2321_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_2319_, v___y_2315_, v_jsonOutput_2104_, v___y_2320_);
lean_dec(v___y_2320_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2352_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2352_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2352_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; 
lean_inc_ref(v___y_2316_);
v___x_2326_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___y_2316_);
if (lean_obj_tag(v___x_2326_) == 1)
{
lean_object* v_val_2327_; lean_object* v_env_2328_; lean_object* v_scopes_2329_; lean_object* v___x_2330_; lean_object* v_opts_2331_; lean_object* v___f_2332_; 
lean_del_object(v___x_2324_);
v_val_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_val_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v_env_2328_ = lean_ctor_get(v_val_2327_, 0);
lean_inc_ref_n(v_env_2328_, 2);
v_scopes_2329_ = lean_ctor_get(v_val_2327_, 2);
lean_inc(v_scopes_2329_);
lean_dec(v_val_2327_);
lean_inc(v___y_2317_);
v___x_2330_ = l_List_get_x21Internal___redArg(v___x_2123_, v_scopes_2329_, v___y_2317_);
lean_dec(v_scopes_2329_);
v_opts_2331_ = lean_ctor_get(v___x_2330_, 1);
lean_inc_ref(v_opts_2331_);
lean_dec(v___x_2330_);
v___f_2332_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2332_, 0, v_env_2328_);
if (lean_obj_tag(v_incrSaveFileName_x3f_2109_) == 1)
{
lean_object* v_val_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v_val_2333_ = lean_ctor_get(v_incrSaveFileName_x3f_2109_, 0);
lean_inc(v_val_2333_);
lean_dec_ref_known(v_incrSaveFileName_x3f_2109_, 1);
v___x_2334_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___y_2319_);
lean_inc_ref(v___y_2316_);
v___x_2335_ = l_Lean_Elab_runFrontend___lam__4(v_env_2328_, v_val_2333_, v___y_2316_);
if (lean_obj_tag(v___x_2335_) == 0)
{
uint8_t v___x_2336_; uint8_t v___x_2337_; 
lean_dec_ref_known(v___x_2335_, 1);
v___x_2336_ = lean_unbox(v_a_2322_);
v___x_2337_ = lean_unbox(v_a_2322_);
lean_dec(v_a_2322_);
lean_inc_ref(v_env_2328_);
v___y_2292_ = v_env_2328_;
v___y_2293_ = v___x_2336_;
v___y_2294_ = v_opts_2331_;
v___y_2295_ = v___f_2332_;
v___y_2296_ = v___y_2315_;
v___y_2297_ = v_env_2328_;
v___y_2298_ = v___x_2337_;
v___y_2299_ = v___y_2316_;
v___y_2300_ = v___y_2317_;
v___y_2301_ = v___y_2318_;
v___y_2302_ = v___y_2319_;
goto v___jp_2291_;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v___f_2332_);
lean_dec_ref(v_opts_2331_);
lean_dec_ref(v_env_2328_);
lean_dec(v_a_2322_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec_ref(v___x_2191_);
lean_dec(v_incrHeaderSaveFileName_x3f_2111_);
lean_dec(v_oleanFileName_x3f_2102_);
lean_dec(v_mainModuleName_2100_);
v_a_2338_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2335_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2335_);
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
uint8_t v___x_2346_; uint8_t v___x_2347_; 
lean_dec(v_incrSaveFileName_x3f_2109_);
v___x_2346_ = lean_unbox(v_a_2322_);
v___x_2347_ = lean_unbox(v_a_2322_);
lean_dec(v_a_2322_);
lean_inc_ref(v_env_2328_);
v___y_2292_ = v_env_2328_;
v___y_2293_ = v___x_2346_;
v___y_2294_ = v_opts_2331_;
v___y_2295_ = v___f_2332_;
v___y_2296_ = v___y_2315_;
v___y_2297_ = v_env_2328_;
v___y_2298_ = v___x_2347_;
v___y_2299_ = v___y_2316_;
v___y_2300_ = v___y_2317_;
v___y_2301_ = v___y_2318_;
v___y_2302_ = v___y_2319_;
goto v___jp_2291_;
}
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
lean_dec(v___x_2326_);
lean_dec(v_a_2322_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec_ref(v___x_2191_);
lean_dec(v_incrHeaderSaveFileName_x3f_2111_);
lean_dec(v_incrSaveFileName_x3f_2109_);
lean_dec(v_oleanFileName_x3f_2102_);
lean_dec(v_mainModuleName_2100_);
v___x_2348_ = lean_box(0);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2348_);
v___x_2350_ = v___x_2324_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec_ref(v___x_2191_);
lean_dec(v_incrHeaderSaveFileName_x3f_2111_);
lean_dec(v_incrSaveFileName_x3f_2109_);
lean_dec(v_oleanFileName_x3f_2102_);
lean_dec(v_mainModuleName_2100_);
v_a_2353_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2321_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2321_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
v___jp_2361_:
{
lean_object* v_stx_x3f_2368_; lean_object* v_reportingRange_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
v_stx_x3f_2368_ = lean_ctor_get(v___y_2365_, 0);
lean_inc(v_stx_x3f_2368_);
v_reportingRange_2369_ = lean_ctor_get(v___y_2365_, 1);
lean_inc(v_reportingRange_2369_);
v___x_2370_ = l_Lean_Language_SnapshotTask_map___redArg(v___y_2365_, v___f_2121_, v_stx_x3f_2368_, v_reportingRange_2369_, v___x_2127_);
v___x_2371_ = lean_unsigned_to_nat(1u);
v___x_2372_ = lean_mk_empty_array_with_capacity(v___x_2371_);
v___x_2373_ = lean_array_push(v___x_2372_, v___x_2370_);
v___x_2374_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2367_, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___y_2364_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = lean_box(1);
v___x_2377_ = lean_unsigned_to_nat(0u);
v___x_2378_ = lean_array_get_size(v_errorOnKinds_2105_);
v___x_2379_ = lean_nat_dec_lt(v___x_2377_, v___x_2378_);
if (v___x_2379_ == 0)
{
v___y_2315_ = v___y_2362_;
v___y_2316_ = v___y_2363_;
v___y_2317_ = v___x_2377_;
v___y_2318_ = v___y_2366_;
v___y_2319_ = v___x_2375_;
v___y_2320_ = v___x_2376_;
goto v___jp_2314_;
}
else
{
uint8_t v___x_2380_; 
v___x_2380_ = lean_nat_dec_le(v___x_2378_, v___x_2378_);
if (v___x_2380_ == 0)
{
if (v___x_2379_ == 0)
{
v___y_2315_ = v___y_2362_;
v___y_2316_ = v___y_2363_;
v___y_2317_ = v___x_2377_;
v___y_2318_ = v___y_2366_;
v___y_2319_ = v___x_2375_;
v___y_2320_ = v___x_2376_;
goto v___jp_2314_;
}
else
{
size_t v___x_2381_; size_t v___x_2382_; lean_object* v___x_2383_; 
v___x_2381_ = ((size_t)0ULL);
v___x_2382_ = lean_usize_of_nat(v___x_2378_);
v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_errorOnKinds_2105_, v___x_2381_, v___x_2382_, v___x_2376_);
v___y_2315_ = v___y_2362_;
v___y_2316_ = v___y_2363_;
v___y_2317_ = v___x_2377_;
v___y_2318_ = v___y_2366_;
v___y_2319_ = v___x_2375_;
v___y_2320_ = v___x_2383_;
goto v___jp_2314_;
}
}
else
{
size_t v___x_2384_; size_t v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = ((size_t)0ULL);
v___x_2385_ = lean_usize_of_nat(v___x_2378_);
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_errorOnKinds_2105_, v___x_2384_, v___x_2385_, v___x_2376_);
v___y_2315_ = v___y_2362_;
v___y_2316_ = v___y_2363_;
v___y_2317_ = v___x_2377_;
v___y_2318_ = v___y_2366_;
v___y_2319_ = v___x_2375_;
v___y_2320_ = v___x_2386_;
goto v___jp_2314_;
}
}
}
v___jp_2387_:
{
lean_object* v___x_2391_; lean_object* v_result_x3f_2392_; 
v___x_2391_ = l_Lean_Language_Lean_process(v___y_2389_, v_a_2390_, v___x_2191_);
v_result_x3f_2392_ = lean_ctor_get(v___x_2391_, 4);
lean_inc(v_result_x3f_2392_);
if (lean_obj_tag(v_result_x3f_2392_) == 0)
{
lean_object* v_toSnapshot_2393_; lean_object* v_metaSnap_2394_; lean_object* v_stx_2395_; lean_object* v___x_2396_; 
v_toSnapshot_2393_ = lean_ctor_get(v___x_2391_, 0);
lean_inc_ref(v_toSnapshot_2393_);
v_metaSnap_2394_ = lean_ctor_get(v___x_2391_, 1);
lean_inc_ref(v_metaSnap_2394_);
v_stx_2395_ = lean_ctor_get(v___x_2391_, 3);
lean_inc(v_stx_2395_);
v___x_2396_ = lean_box(0);
v___y_2362_ = v___y_2388_;
v___y_2363_ = v___x_2391_;
v___y_2364_ = v_toSnapshot_2393_;
v___y_2365_ = v_metaSnap_2394_;
v___y_2366_ = v_stx_2395_;
v___y_2367_ = v___x_2396_;
goto v___jp_2361_;
}
else
{
lean_object* v_val_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2411_; 
v_val_2397_ = lean_ctor_get(v_result_x3f_2392_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_result_x3f_2392_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2399_ = v_result_x3f_2392_;
v_isShared_2400_ = v_isSharedCheck_2411_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_val_2397_);
lean_dec(v_result_x3f_2392_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2411_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_processedSnap_2401_; lean_object* v_toSnapshot_2402_; lean_object* v_metaSnap_2403_; lean_object* v_stx_2404_; lean_object* v_stx_x3f_2405_; lean_object* v_reportingRange_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v_processedSnap_2401_ = lean_ctor_get(v_val_2397_, 1);
lean_inc_ref(v_processedSnap_2401_);
lean_dec(v_val_2397_);
v_toSnapshot_2402_ = lean_ctor_get(v___x_2391_, 0);
lean_inc_ref(v_toSnapshot_2402_);
v_metaSnap_2403_ = lean_ctor_get(v___x_2391_, 1);
lean_inc_ref(v_metaSnap_2403_);
v_stx_2404_ = lean_ctor_get(v___x_2391_, 3);
lean_inc(v_stx_2404_);
v_stx_x3f_2405_ = lean_ctor_get(v_processedSnap_2401_, 0);
lean_inc(v_stx_x3f_2405_);
v_reportingRange_2406_ = lean_ctor_get(v_processedSnap_2401_, 1);
lean_inc(v_reportingRange_2406_);
v___x_2407_ = l_Lean_Language_SnapshotTask_map___redArg(v_processedSnap_2401_, v___f_2122_, v_stx_x3f_2405_, v_reportingRange_2406_, v___x_2127_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2407_);
v___x_2409_ = v___x_2399_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
v___y_2362_ = v___y_2388_;
v___y_2363_ = v___x_2391_;
v___y_2364_ = v_toSnapshot_2402_;
v___y_2365_ = v_metaSnap_2403_;
v___y_2366_ = v_stx_2404_;
v___y_2367_ = v___x_2409_;
goto v___jp_2361_;
}
}
}
}
v___jp_2412_:
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_a_2415_);
v___y_2388_ = v___y_2413_;
v___y_2389_ = v___y_2414_;
v_a_2390_ = v___x_2416_;
goto v___jp_2387_;
}
v___jp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___f_2425_; 
v___x_2420_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2098_, v___x_2417_, v___y_2419_);
v___x_2421_ = l_Lean_Elab_async;
v___x_2422_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_2420_, v___x_2421_, v___x_2127_);
v___x_2423_ = lean_box_uint32(v_trustLevel_2101_);
v___x_2424_ = lean_box(v___x_2127_);
lean_inc(v_mainModuleName_2100_);
lean_inc_ref(v___x_2422_);
v___f_2425_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__5___boxed), 10, 7);
lean_closure_set(v___f_2425_, 0, v_setup_x3f_2108_);
lean_closure_set(v___f_2425_, 1, v___f_2120_);
lean_closure_set(v___f_2425_, 2, v___x_2422_);
lean_closure_set(v___f_2425_, 3, v_plugins_2106_);
lean_closure_set(v___f_2425_, 4, v___x_2423_);
lean_closure_set(v___f_2425_, 5, v___x_2424_);
lean_closure_set(v___f_2425_, 6, v_mainModuleName_2100_);
if (lean_obj_tag(v_incrLoadFileName_x3f_2110_) == 0)
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_box(0);
v___y_2388_ = v___x_2422_;
v___y_2389_ = v___f_2425_;
v_a_2390_ = v___x_2426_;
goto v___jp_2387_;
}
else
{
lean_object* v_val_2427_; lean_object* v___x_2428_; 
v_val_2427_ = lean_ctor_get(v_incrLoadFileName_x3f_2110_, 0);
lean_inc(v_val_2427_);
lean_dec_ref_known(v_incrLoadFileName_x3f_2110_, 1);
v___x_2428_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_val_2427_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v_snap_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___x_2428_, 1);
v_snap_2430_ = lean_ctor_get(v_a_2429_, 0);
lean_inc_ref_n(v_snap_2430_, 2);
v___x_2431_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_snap_2430_);
v___x_2432_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_2431_);
if (lean_obj_tag(v___x_2432_) == 1)
{
lean_object* v_val_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v_val_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_val_2433_);
lean_dec_ref_known(v___x_2432_, 1);
lean_inc_ref(v___x_2422_);
v___x_2434_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed), 4, 3);
lean_closure_set(v___x_2434_, 0, v___x_2422_);
lean_closure_set(v___x_2434_, 1, v_a_2429_);
lean_closure_set(v___x_2434_, 2, v_val_2433_);
v___x_2435_ = l_Lean_withImporting___redArg(v___x_2434_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v___x_2436_; 
lean_dec_ref_known(v___x_2435_, 1);
v___x_2436_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_dec_ref_known(v___x_2436_, 1);
v___y_2413_ = v___x_2422_;
v___y_2414_ = v___f_2425_;
v_a_2415_ = v_snap_2430_;
goto v___jp_2412_;
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec_ref(v_snap_2430_);
lean_dec_ref(v___f_2425_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2191_);
lean_dec(v_incrHeaderSaveFileName_x3f_2111_);
lean_dec(v_incrSaveFileName_x3f_2109_);
lean_dec(v_oleanFileName_x3f_2102_);
lean_dec(v_mainModuleName_2100_);
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v_snap_2430_);
lean_dec_ref(v___f_2425_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2191_);
lean_dec(v_incrHeaderSaveFileName_x3f_2111_);
lean_dec(v_incrSaveFileName_x3f_2109_);
lean_dec(v_oleanFileName_x3f_2102_);
lean_dec(v_mainModuleName_2100_);
v_a_2445_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2435_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2435_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
lean_dec(v___x_2432_);
lean_dec(v_a_2429_);
v___y_2413_ = v___x_2422_;
v___y_2414_ = v___f_2425_;
v_a_2415_ = v_snap_2430_;
goto v___jp_2412_;
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec_ref(v___f_2425_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v___x_2191_);
lean_dec(v_incrHeaderSaveFileName_x3f_2111_);
lean_dec(v_incrSaveFileName_x3f_2109_);
lean_dec(v_oleanFileName_x3f_2102_);
lean_dec(v_mainModuleName_2100_);
v_a_2453_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2428_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2428_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_2462_, lean_object* v_opts_2463_, lean_object* v_fileName_2464_, lean_object* v_mainModuleName_2465_, lean_object* v_trustLevel_2466_, lean_object* v_oleanFileName_x3f_2467_, lean_object* v_ileanFileName_x3f_2468_, lean_object* v_jsonOutput_2469_, lean_object* v_errorOnKinds_2470_, lean_object* v_plugins_2471_, lean_object* v_printStats_2472_, lean_object* v_setup_x3f_2473_, lean_object* v_incrSaveFileName_x3f_2474_, lean_object* v_incrLoadFileName_x3f_2475_, lean_object* v_incrHeaderSaveFileName_x3f_2476_, lean_object* v_a_2477_){
_start:
{
uint32_t v_trustLevel_boxed_2478_; uint8_t v_jsonOutput_boxed_2479_; uint8_t v_printStats_boxed_2480_; lean_object* v_res_2481_; 
v_trustLevel_boxed_2478_ = lean_unbox_uint32(v_trustLevel_2466_);
lean_dec(v_trustLevel_2466_);
v_jsonOutput_boxed_2479_ = lean_unbox(v_jsonOutput_2469_);
v_printStats_boxed_2480_ = lean_unbox(v_printStats_2472_);
v_res_2481_ = l_Lean_Elab_runFrontend(v_input_2462_, v_opts_2463_, v_fileName_2464_, v_mainModuleName_2465_, v_trustLevel_boxed_2478_, v_oleanFileName_x3f_2467_, v_ileanFileName_x3f_2468_, v_jsonOutput_boxed_2479_, v_errorOnKinds_2470_, v_plugins_2471_, v_printStats_boxed_2480_, v_setup_x3f_2473_, v_incrSaveFileName_x3f_2474_, v_incrLoadFileName_x3f_2475_, v_incrHeaderSaveFileName_x3f_2476_);
lean_dec_ref(v_errorOnKinds_2470_);
lean_dec(v_ileanFileName_x3f_2468_);
return v_res_2481_;
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
