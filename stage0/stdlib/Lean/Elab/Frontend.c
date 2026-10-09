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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_runFrontend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__0_value;
static const lean_closure_object l_Lean_Elab_runFrontend___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__1 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__1_value;
static lean_once_cell_t l_Lean_Elab_runFrontend___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_runFrontend___closed__2;
static const lean_string_object l_Lean_Elab_runFrontend___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ".olean serialization"};
static const lean_object* l_Lean_Elab_runFrontend___closed__3 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Frontend_setCommandState___redArg(lean_object* v_commandState_1_, lean_object* v_a_2_){
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
LEAN_EXPORT void l_Lean_Elab_Frontend_setCommandState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_commandState_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_Elab_Frontend_setCommandState___redArg(v_commandState_1_, v_a_2_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___redArg___boxed(lean_object* v_commandState_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Elab_Frontend_setCommandState___redArg(v_commandState_20_, v_a_21_);
lean_dec(v_a_21_);
return v_res_23_;
}
}
lean_object* l_Lean_Elab_Frontend_setCommandState(lean_object* v_commandState_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Elab_Frontend_setCommandState___redArg(v_commandState_24_, v_a_26_);
return v___x_28_;
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_setCommandState_0interp(lean_interpreter_value* stack)
{
lean_object* v_commandState_24_ = stack[0].m_obj;
lean_object* v_a_25_ = stack[1].m_obj;
lean_object* v_a_26_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Elab_Frontend_setCommandState(v_commandState_24_, v_a_25_, v_a_26_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___boxed(lean_object* v_commandState_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Elab_Frontend_setCommandState(v_commandState_30_, v_a_31_, v_a_32_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
return v_res_34_;
}
}
lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg(lean_object* v_x_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v___x_40_; lean_object* v_fileName_41_; lean_object* v_fileMap_42_; lean_object* v_commandState_43_; lean_object* v_cmdPos_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_40_ = lean_st_ref_get(v_a_38_);
v_fileName_41_ = lean_ctor_get(v_a_37_, 1);
v_fileMap_42_ = lean_ctor_get(v_a_37_, 2);
v_commandState_43_ = lean_ctor_get(v___x_40_, 0);
lean_inc_ref(v_commandState_43_);
v_cmdPos_44_ = lean_ctor_get(v___x_40_, 2);
lean_inc(v_cmdPos_44_);
lean_dec(v___x_40_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_box(0);
v___x_47_ = lean_box(0);
v___x_48_ = l_Lean_firstFrontendMacroScope;
v___x_49_ = lean_box(0);
v___x_50_ = 0;
lean_inc_ref(v_fileMap_42_);
lean_inc_ref(v_fileName_41_);
v___x_51_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_51_, 0, v_fileName_41_);
lean_ctor_set(v___x_51_, 1, v_fileMap_42_);
lean_ctor_set(v___x_51_, 2, v___x_45_);
lean_ctor_set(v___x_51_, 3, v_cmdPos_44_);
lean_ctor_set(v___x_51_, 4, v___x_46_);
lean_ctor_set(v___x_51_, 5, v___x_47_);
lean_ctor_set(v___x_51_, 6, v___x_48_);
lean_ctor_set(v___x_51_, 7, v___x_49_);
lean_ctor_set(v___x_51_, 8, v___x_47_);
lean_ctor_set(v___x_51_, 9, v___x_47_);
lean_ctor_set_uint8(v___x_51_, sizeof(void*)*10, v___x_50_);
v___x_52_ = lean_st_mk_ref(v_commandState_43_);
lean_inc(v___x_52_);
v___x_53_ = lean_apply_3(v_x_36_, v___x_51_, v___x_52_, lean_box(0));
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_a_54_);
lean_dec_ref_known(v___x_53_, 1);
v___x_55_ = lean_st_ref_get(v___x_52_);
lean_dec(v___x_52_);
v___x_56_ = l_Lean_Elab_Frontend_setCommandState___redArg(v___x_55_, v_a_38_);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_63_ == 0)
{
lean_object* v_unused_64_; 
v_unused_64_ = lean_ctor_get(v___x_56_, 0);
lean_dec(v_unused_64_);
v___x_58_ = v___x_56_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_dec(v___x_56_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v_a_54_);
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_54_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
else
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_77_; 
lean_dec(v___x_52_);
v_a_65_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_77_ == 0)
{
v___x_67_ = v___x_53_;
v_isShared_68_ = v_isSharedCheck_77_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_53_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_77_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_69_ = l_Lean_Exception_toMessageData(v_a_65_);
v___x_70_ = l_Lean_MessageData_toString(v___x_69_);
v___x_71_ = ((lean_object*)(l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0));
v___x_72_ = lean_string_append(v___x_71_, v___x_70_);
lean_dec_ref(v___x_70_);
v___x_73_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 0, v___x_73_);
v___x_75_ = v___x_67_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_73_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_runCommandElabM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_36_ = stack[0].m_obj;
lean_object* v_a_37_ = stack[1].m_obj;
lean_object* v_a_38_ = stack[2].m_obj;
lean_object* v_res_78_;
v_res_78_ = l_Lean_Elab_Frontend_runCommandElabM___redArg(v_x_36_, v_a_37_, v_a_38_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg___boxed(lean_object* v_x_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Elab_Frontend_runCommandElabM___redArg(v_x_79_, v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
return v_res_83_;
}
}
lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object* v_00_u03b1_84_, lean_object* v_x_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_89_; lean_object* v_fileName_90_; lean_object* v_fileMap_91_; lean_object* v_commandState_92_; lean_object* v_cmdPos_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_89_ = lean_st_ref_get(v_a_87_);
v_fileName_90_ = lean_ctor_get(v_a_86_, 1);
v_fileMap_91_ = lean_ctor_get(v_a_86_, 2);
v_commandState_92_ = lean_ctor_get(v___x_89_, 0);
lean_inc_ref(v_commandState_92_);
v_cmdPos_93_ = lean_ctor_get(v___x_89_, 2);
lean_inc(v_cmdPos_93_);
lean_dec(v___x_89_);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_box(0);
v___x_96_ = lean_box(0);
v___x_97_ = l_Lean_firstFrontendMacroScope;
v___x_98_ = lean_box(0);
v___x_99_ = 0;
lean_inc_ref(v_fileMap_91_);
lean_inc_ref(v_fileName_90_);
v___x_100_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_100_, 0, v_fileName_90_);
lean_ctor_set(v___x_100_, 1, v_fileMap_91_);
lean_ctor_set(v___x_100_, 2, v___x_94_);
lean_ctor_set(v___x_100_, 3, v_cmdPos_93_);
lean_ctor_set(v___x_100_, 4, v___x_95_);
lean_ctor_set(v___x_100_, 5, v___x_96_);
lean_ctor_set(v___x_100_, 6, v___x_97_);
lean_ctor_set(v___x_100_, 7, v___x_98_);
lean_ctor_set(v___x_100_, 8, v___x_96_);
lean_ctor_set(v___x_100_, 9, v___x_96_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*10, v___x_99_);
v___x_101_ = lean_st_mk_ref(v_commandState_92_);
lean_inc(v___x_101_);
v___x_102_ = lean_apply_3(v_x_85_, v___x_100_, v___x_101_, lean_box(0));
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_102_, 1);
v___x_104_ = lean_st_ref_get(v___x_101_);
lean_dec(v___x_101_);
v___x_105_ = l_Lean_Elab_Frontend_setCommandState___redArg(v___x_104_, v_a_87_);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_112_ == 0)
{
lean_object* v_unused_113_; 
v_unused_113_ = lean_ctor_get(v___x_105_, 0);
lean_dec(v_unused_113_);
v___x_107_ = v___x_105_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_dec(v___x_105_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v_a_103_);
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_103_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_126_; 
lean_dec(v___x_101_);
v_a_114_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_126_ == 0)
{
v___x_116_ = v___x_102_;
v_isShared_117_ = v_isSharedCheck_126_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_102_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_126_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_118_ = l_Lean_Exception_toMessageData(v_a_114_);
v___x_119_ = l_Lean_MessageData_toString(v___x_118_);
v___x_120_ = ((lean_object*)(l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0));
v___x_121_ = lean_string_append(v___x_120_, v___x_119_);
lean_dec_ref(v___x_119_);
v___x_122_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_122_);
v___x_124_ = v___x_116_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_runCommandElabM_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_85_ = stack[1].m_obj;
lean_object* v_a_86_ = stack[2].m_obj;
lean_object* v_a_87_ = stack[3].m_obj;
lean_object* v_res_127_;
v_res_127_ = l_Lean_Elab_Frontend_runCommandElabM(lean_box(0), v_x_85_, v_a_86_, v_a_87_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___boxed(lean_object* v_00_u03b1_128_, lean_object* v_x_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Elab_Frontend_runCommandElabM(v_00_u03b1_128_, v_x_129_, v_a_130_, v_a_131_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
return v_res_133_;
}
}
lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object* v_stx_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; lean_object* v_fileName_139_; lean_object* v_fileMap_140_; lean_object* v_commandState_141_; lean_object* v_cmdPos_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_138_ = lean_st_ref_get(v_a_136_);
v_fileName_139_ = lean_ctor_get(v_a_135_, 1);
v_fileMap_140_ = lean_ctor_get(v_a_135_, 2);
v_commandState_141_ = lean_ctor_get(v___x_138_, 0);
lean_inc_ref(v_commandState_141_);
v_cmdPos_142_ = lean_ctor_get(v___x_138_, 2);
lean_inc(v_cmdPos_142_);
lean_dec(v___x_138_);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_box(0);
v___x_145_ = lean_box(0);
v___x_146_ = l_Lean_firstFrontendMacroScope;
v___x_147_ = lean_box(0);
v___x_148_ = 0;
lean_inc_ref(v_fileMap_140_);
lean_inc_ref(v_fileName_139_);
v___x_149_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_149_, 0, v_fileName_139_);
lean_ctor_set(v___x_149_, 1, v_fileMap_140_);
lean_ctor_set(v___x_149_, 2, v___x_143_);
lean_ctor_set(v___x_149_, 3, v_cmdPos_142_);
lean_ctor_set(v___x_149_, 4, v___x_144_);
lean_ctor_set(v___x_149_, 5, v___x_145_);
lean_ctor_set(v___x_149_, 6, v___x_146_);
lean_ctor_set(v___x_149_, 7, v___x_147_);
lean_ctor_set(v___x_149_, 8, v___x_145_);
lean_ctor_set(v___x_149_, 9, v___x_145_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*10, v___x_148_);
v___x_150_ = lean_st_mk_ref(v_commandState_141_);
v___x_151_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_134_, v___x_149_, v___x_150_);
lean_dec_ref_known(v___x_149_, 10);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v___x_153_ = lean_st_ref_get(v___x_150_);
lean_dec(v___x_150_);
v___x_154_ = l_Lean_Elab_Frontend_setCommandState___redArg(v___x_153_, v_a_136_);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; 
v_unused_162_ = lean_ctor_get(v___x_154_, 0);
lean_dec(v_unused_162_);
v___x_156_ = v___x_154_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_dec(v___x_154_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v_a_152_);
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_152_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_175_; 
lean_dec(v___x_150_);
v_a_163_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_175_ == 0)
{
v___x_165_ = v___x_151_;
v_isShared_166_ = v_isSharedCheck_175_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_151_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_175_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_167_ = l_Lean_Exception_toMessageData(v_a_163_);
v___x_168_ = l_Lean_MessageData_toString(v___x_167_);
v___x_169_ = ((lean_object*)(l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0));
v___x_170_ = lean_string_append(v___x_169_, v___x_168_);
lean_dec_ref(v___x_168_);
v___x_171_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_171_);
v___x_173_ = v___x_165_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_elabCommandAtFrontend_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_134_ = stack[0].m_obj;
lean_object* v_a_135_ = stack[1].m_obj;
lean_object* v_a_136_ = stack[2].m_obj;
lean_object* v_res_176_;
v_res_176_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_stx_134_, v_a_135_, v_a_136_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed(lean_object* v_stx_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_stx_177_, v_a_178_, v_a_179_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
return v_res_181_;
}
}
lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg(lean_object* v_a_182_){
_start:
{
lean_object* v___x_184_; lean_object* v_parserState_185_; lean_object* v_commandState_186_; lean_object* v_commands_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_198_; 
v___x_184_ = lean_st_ref_take(v_a_182_);
v_parserState_185_ = lean_ctor_get(v___x_184_, 1);
v_commandState_186_ = lean_ctor_get(v___x_184_, 0);
v_commands_187_ = lean_ctor_get(v___x_184_, 3);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v___x_184_, 2);
lean_dec(v_unused_199_);
v___x_189_ = v___x_184_;
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_commands_187_);
lean_inc(v_parserState_185_);
lean_inc(v_commandState_186_);
lean_dec(v___x_184_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_pos_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v_pos_191_ = lean_ctor_get(v_parserState_185_, 0);
lean_inc(v_pos_191_);
v___x_192_ = lean_box(0);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 2, v_pos_191_);
v___x_194_ = v___x_189_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_commandState_186_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_parserState_185_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_pos_191_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v_commands_187_);
v___x_194_ = v_reuseFailAlloc_197_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_st_ref_put(v_a_182_, v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_192_);
return v___x_196_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_updateCmdPos___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_182_ = stack[0].m_obj;
lean_object* v_res_200_;
v_res_200_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_182_);
stack->m_obj
 = v_res_200_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg___boxed(lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_201_);
lean_dec(v_a_201_);
return v_res_203_;
}
}
lean_object* l_Lean_Elab_Frontend_updateCmdPos(lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_205_);
return v___x_207_;
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_updateCmdPos_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_204_ = stack[0].m_obj;
lean_object* v_a_205_ = stack[1].m_obj;
lean_object* v_res_208_;
v_res_208_ = l_Lean_Elab_Frontend_updateCmdPos(v_a_204_, v_a_205_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___boxed(lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Elab_Frontend_updateCmdPos(v_a_209_, v_a_210_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
return v_res_212_;
}
}
lean_object* l_Lean_Elab_Frontend_getParserState___redArg(lean_object* v_a_213_){
_start:
{
lean_object* v___x_215_; lean_object* v_parserState_216_; lean_object* v___x_217_; 
v___x_215_ = lean_st_ref_get(v_a_213_);
v_parserState_216_ = lean_ctor_get(v___x_215_, 1);
lean_inc_ref(v_parserState_216_);
lean_dec(v___x_215_);
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v_parserState_216_);
return v___x_217_;
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_getParserState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_213_ = stack[0].m_obj;
lean_object* v_res_218_;
v_res_218_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_213_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___redArg___boxed(lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_219_);
lean_dec(v_a_219_);
return v_res_221_;
}
}
lean_object* l_Lean_Elab_Frontend_getParserState(lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_223_);
return v___x_225_;
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_getParserState_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_222_ = stack[0].m_obj;
lean_object* v_a_223_ = stack[1].m_obj;
lean_object* v_res_226_;
v_res_226_ = l_Lean_Elab_Frontend_getParserState(v_a_222_, v_a_223_);
stack->m_obj
 = v_res_226_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___boxed(lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Elab_Frontend_getParserState(v_a_227_, v_a_228_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
return v_res_230_;
}
}
lean_object* l_Lean_Elab_Frontend_getCommandState___redArg(lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; lean_object* v_commandState_234_; lean_object* v___x_235_; 
v___x_233_ = lean_st_ref_get(v_a_231_);
v_commandState_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_commandState_234_);
lean_dec(v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v_commandState_234_);
return v___x_235_;
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_getCommandState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_231_ = stack[0].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_231_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___redArg___boxed(lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_237_);
lean_dec(v_a_237_);
return v_res_239_;
}
}
lean_object* l_Lean_Elab_Frontend_getCommandState(lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_241_);
return v___x_243_;
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_getCommandState_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_240_ = stack[0].m_obj;
lean_object* v_a_241_ = stack[1].m_obj;
lean_object* v_res_244_;
v_res_244_ = l_Lean_Elab_Frontend_getCommandState(v_a_240_, v_a_241_);
stack->m_obj
 = v_res_244_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___boxed(lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Elab_Frontend_getCommandState(v_a_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
return v_res_248_;
}
}
lean_object* l_Lean_Elab_Frontend_setParserState___redArg(lean_object* v_ps_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_252_; lean_object* v_commandState_253_; lean_object* v_cmdPos_254_; lean_object* v_commands_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_265_; 
v___x_252_ = lean_st_ref_take(v_a_250_);
v_commandState_253_ = lean_ctor_get(v___x_252_, 0);
v_cmdPos_254_ = lean_ctor_get(v___x_252_, 2);
v_commands_255_ = lean_ctor_get(v___x_252_, 3);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v___x_252_, 1);
lean_dec(v_unused_266_);
v___x_257_ = v___x_252_;
v_isShared_258_ = v_isSharedCheck_265_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_commands_255_);
lean_inc(v_cmdPos_254_);
lean_inc(v_commandState_253_);
lean_dec(v___x_252_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_265_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = lean_box(0);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v_ps_249_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_commandState_253_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_ps_249_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v_cmdPos_254_);
lean_ctor_set(v_reuseFailAlloc_264_, 3, v_commands_255_);
v___x_261_ = v_reuseFailAlloc_264_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_st_ref_put(v_a_250_, v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_259_);
return v___x_263_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_setParserState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ps_249_ = stack[0].m_obj;
lean_object* v_a_250_ = stack[1].m_obj;
lean_object* v_res_267_;
v_res_267_ = l_Lean_Elab_Frontend_setParserState___redArg(v_ps_249_, v_a_250_);
stack->m_obj
 = v_res_267_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg___boxed(lean_object* v_ps_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Elab_Frontend_setParserState___redArg(v_ps_268_, v_a_269_);
lean_dec(v_a_269_);
return v_res_271_;
}
}
lean_object* l_Lean_Elab_Frontend_setParserState(lean_object* v_ps_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Elab_Frontend_setParserState___redArg(v_ps_272_, v_a_274_);
return v___x_276_;
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_setParserState_0interp(lean_interpreter_value* stack)
{
lean_object* v_ps_272_ = stack[0].m_obj;
lean_object* v_a_273_ = stack[1].m_obj;
lean_object* v_a_274_ = stack[2].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Lean_Elab_Frontend_setParserState(v_ps_272_, v_a_273_, v_a_274_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___boxed(lean_object* v_ps_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Elab_Frontend_setParserState(v_ps_278_, v_a_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
return v_res_282_;
}
}
lean_object* l_Lean_Elab_Frontend_setMessages___redArg(lean_object* v_msgs_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_286_; lean_object* v_commandState_287_; lean_object* v_parserState_288_; lean_object* v_cmdPos_289_; lean_object* v_commands_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_320_; 
v___x_286_ = lean_st_ref_take(v_a_284_);
v_commandState_287_ = lean_ctor_get(v___x_286_, 0);
v_parserState_288_ = lean_ctor_get(v___x_286_, 1);
v_cmdPos_289_ = lean_ctor_get(v___x_286_, 2);
v_commands_290_ = lean_ctor_get(v___x_286_, 3);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_320_ == 0)
{
v___x_292_ = v___x_286_;
v_isShared_293_ = v_isSharedCheck_320_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_commands_290_);
lean_inc(v_cmdPos_289_);
lean_inc(v_parserState_288_);
lean_inc(v_commandState_287_);
lean_dec(v___x_286_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_320_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_env_294_; lean_object* v_scopes_295_; lean_object* v_usedQuotCtxts_296_; lean_object* v_nextMacroScope_297_; lean_object* v_maxRecDepth_298_; lean_object* v_ngen_299_; lean_object* v_auxDeclNGen_300_; lean_object* v_infoState_301_; lean_object* v_traceState_302_; lean_object* v_snapshotTasks_303_; lean_object* v_prevLinterStates_304_; lean_object* v_codeQualityEntryTasks_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_318_; 
v_env_294_ = lean_ctor_get(v_commandState_287_, 0);
v_scopes_295_ = lean_ctor_get(v_commandState_287_, 2);
v_usedQuotCtxts_296_ = lean_ctor_get(v_commandState_287_, 3);
v_nextMacroScope_297_ = lean_ctor_get(v_commandState_287_, 4);
v_maxRecDepth_298_ = lean_ctor_get(v_commandState_287_, 5);
v_ngen_299_ = lean_ctor_get(v_commandState_287_, 6);
v_auxDeclNGen_300_ = lean_ctor_get(v_commandState_287_, 7);
v_infoState_301_ = lean_ctor_get(v_commandState_287_, 8);
v_traceState_302_ = lean_ctor_get(v_commandState_287_, 9);
v_snapshotTasks_303_ = lean_ctor_get(v_commandState_287_, 10);
v_prevLinterStates_304_ = lean_ctor_get(v_commandState_287_, 11);
v_codeQualityEntryTasks_305_ = lean_ctor_get(v_commandState_287_, 12);
v_isSharedCheck_318_ = !lean_is_exclusive(v_commandState_287_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; 
v_unused_319_ = lean_ctor_get(v_commandState_287_, 1);
lean_dec(v_unused_319_);
v___x_307_ = v_commandState_287_;
v_isShared_308_ = v_isSharedCheck_318_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_codeQualityEntryTasks_305_);
lean_inc(v_prevLinterStates_304_);
lean_inc(v_snapshotTasks_303_);
lean_inc(v_traceState_302_);
lean_inc(v_infoState_301_);
lean_inc(v_auxDeclNGen_300_);
lean_inc(v_ngen_299_);
lean_inc(v_maxRecDepth_298_);
lean_inc(v_nextMacroScope_297_);
lean_inc(v_usedQuotCtxts_296_);
lean_inc(v_scopes_295_);
lean_inc(v_env_294_);
lean_dec(v_commandState_287_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_318_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_box(0);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v_msgs_283_);
v___x_311_ = v___x_307_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_env_294_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_msgs_283_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_scopes_295_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v_usedQuotCtxts_296_);
lean_ctor_set(v_reuseFailAlloc_317_, 4, v_nextMacroScope_297_);
lean_ctor_set(v_reuseFailAlloc_317_, 5, v_maxRecDepth_298_);
lean_ctor_set(v_reuseFailAlloc_317_, 6, v_ngen_299_);
lean_ctor_set(v_reuseFailAlloc_317_, 7, v_auxDeclNGen_300_);
lean_ctor_set(v_reuseFailAlloc_317_, 8, v_infoState_301_);
lean_ctor_set(v_reuseFailAlloc_317_, 9, v_traceState_302_);
lean_ctor_set(v_reuseFailAlloc_317_, 10, v_snapshotTasks_303_);
lean_ctor_set(v_reuseFailAlloc_317_, 11, v_prevLinterStates_304_);
lean_ctor_set(v_reuseFailAlloc_317_, 12, v_codeQualityEntryTasks_305_);
v___x_311_ = v_reuseFailAlloc_317_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_311_);
v___x_313_ = v___x_292_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_parserState_288_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_cmdPos_289_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_commands_290_);
v___x_313_ = v_reuseFailAlloc_316_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_st_ref_put(v_a_284_, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_309_);
return v___x_315_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_setMessages___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgs_283_ = stack[0].m_obj;
lean_object* v_a_284_ = stack[1].m_obj;
lean_object* v_res_321_;
v_res_321_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_283_, v_a_284_);
stack->m_obj
 = v_res_321_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg___boxed(lean_object* v_msgs_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_322_, v_a_323_);
lean_dec(v_a_323_);
return v_res_325_;
}
}
lean_object* l_Lean_Elab_Frontend_setMessages(lean_object* v_msgs_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_326_, v_a_328_);
return v___x_330_;
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_setMessages_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgs_326_ = stack[0].m_obj;
lean_object* v_a_327_ = stack[1].m_obj;
lean_object* v_a_328_ = stack[2].m_obj;
lean_object* v_res_331_;
v_res_331_ = l_Lean_Elab_Frontend_setMessages(v_msgs_326_, v_a_327_, v_a_328_);
stack->m_obj
 = v_res_331_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___boxed(lean_object* v_msgs_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Elab_Frontend_setMessages(v_msgs_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_336_;
}
}
lean_object* l_Lean_Elab_Frontend_getInputContext___redArg(lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; 
lean_inc_ref(v_a_337_);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v_a_337_);
return v___x_339_;
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_getInputContext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_337_ = stack[0].m_obj;
lean_object* v_res_340_;
v_res_340_ = l_Lean_Elab_Frontend_getInputContext___redArg(v_a_337_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg___boxed(lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Elab_Frontend_getInputContext___redArg(v_a_341_);
lean_dec_ref(v_a_341_);
return v_res_343_;
}
}
lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_347_; 
lean_inc_ref(v_a_344_);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v_a_344_);
return v___x_347_;
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_getInputContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_344_ = stack[0].m_obj;
lean_object* v_a_345_ = stack[1].m_obj;
lean_object* v_res_348_;
v_res_348_ = l_Lean_Elab_Frontend_getInputContext(v_a_344_, v_a_345_);
stack->m_obj
 = v_res_348_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Elab_Frontend_getInputContext(v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0(lean_object* v_a_353_, lean_object* v___x_354_, lean_object* v_a_355_, lean_object* v_messages_356_, lean_object* v_x_357_){
_start:
{
lean_object* v___x_358_; 
lean_inc_ref(v_a_353_);
v___x_358_ = l_Lean_Parser_parseCommand(v_a_353_, v___x_354_, v_a_355_, v_messages_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0___boxed(lean_object* v_a_359_, lean_object* v___x_360_, lean_object* v_a_361_, lean_object* v_messages_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Elab_Frontend_processCommand___lam__0(v_a_359_, v___x_360_, v_a_361_, v_messages_362_, v_x_363_);
lean_dec_ref(v_a_359_);
return v_res_364_;
}
}
lean_object* l_Lean_Elab_Frontend_processCommand(lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_a_372_; lean_object* v___x_373_; lean_object* v_a_374_; lean_object* v_env_375_; lean_object* v_messages_376_; lean_object* v_scopes_377_; lean_object* v___x_378_; lean_object* v_opts_379_; lean_object* v_currNamespace_380_; lean_object* v_openDecls_381_; lean_object* v___x_382_; lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v_snd_387_; lean_object* v_fst_388_; lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___x_391_; lean_object* v_commandState_392_; lean_object* v_parserState_393_; lean_object* v_cmdPos_394_; lean_object* v_commands_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_425_; 
v___x_369_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_370_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_367_);
lean_dec_ref(v___x_370_);
v___x_371_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_367_);
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref(v___x_371_);
v___x_373_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_367_);
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref(v___x_373_);
v_env_375_ = lean_ctor_get(v_a_372_, 0);
lean_inc_ref(v_env_375_);
v_messages_376_ = lean_ctor_get(v_a_372_, 1);
lean_inc_ref(v_messages_376_);
v_scopes_377_ = lean_ctor_get(v_a_372_, 2);
lean_inc(v_scopes_377_);
lean_dec(v_a_372_);
v___x_378_ = l_List_head_x21___redArg(v___x_369_, v_scopes_377_);
lean_dec(v_scopes_377_);
v_opts_379_ = lean_ctor_get(v___x_378_, 1);
lean_inc_ref_n(v_opts_379_, 2);
v_currNamespace_380_ = lean_ctor_get(v___x_378_, 2);
lean_inc(v_currNamespace_380_);
v_openDecls_381_ = lean_ctor_get(v___x_378_, 3);
lean_inc(v_openDecls_381_);
lean_dec(v___x_378_);
v___x_382_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_382_, 0, v_env_375_);
lean_ctor_set(v___x_382_, 1, v_opts_379_);
lean_ctor_set(v___x_382_, 2, v_currNamespace_380_);
lean_ctor_set(v___x_382_, 3, v_openDecls_381_);
lean_inc_ref(v_a_366_);
v___f_383_ = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommand___lam__0___boxed), 5, 4);
lean_closure_set(v___f_383_, 0, v_a_366_);
lean_closure_set(v___f_383_, 1, v___x_382_);
lean_closure_set(v___f_383_, 2, v_a_374_);
lean_closure_set(v___f_383_, 3, v_messages_376_);
v___x_384_ = ((lean_object*)(l_Lean_Elab_Frontend_processCommand___closed__0));
v___x_385_ = lean_box(0);
v___x_386_ = lean_profileit(v___x_384_, v_opts_379_, v___f_383_, v___x_385_);
lean_dec_ref(v_opts_379_);
v_snd_387_ = lean_ctor_get(v___x_386_, 1);
lean_inc(v_snd_387_);
v_fst_388_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_fst_388_);
lean_dec(v___x_386_);
v_fst_389_ = lean_ctor_get(v_snd_387_, 0);
lean_inc(v_fst_389_);
v_snd_390_ = lean_ctor_get(v_snd_387_, 1);
lean_inc(v_snd_390_);
lean_dec(v_snd_387_);
v___x_391_ = lean_st_ref_take(v_a_367_);
v_commandState_392_ = lean_ctor_get(v___x_391_, 0);
v_parserState_393_ = lean_ctor_get(v___x_391_, 1);
v_cmdPos_394_ = lean_ctor_get(v___x_391_, 2);
v_commands_395_ = lean_ctor_get(v___x_391_, 3);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_425_ == 0)
{
v___x_397_ = v___x_391_;
v_isShared_398_ = v_isSharedCheck_425_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_commands_395_);
lean_inc(v_cmdPos_394_);
lean_inc(v_parserState_393_);
lean_inc(v_commandState_392_);
lean_dec(v___x_391_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_425_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
lean_inc(v_fst_388_);
v___x_399_ = lean_array_push(v_commands_395_, v_fst_388_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 3, v___x_399_);
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_commandState_392_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_parserState_393_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_cmdPos_394_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v___x_399_);
v___x_401_ = v_reuseFailAlloc_424_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = lean_st_ref_put(v_a_367_, v___x_401_);
v___x_403_ = l_Lean_Elab_Frontend_setParserState___redArg(v_fst_389_, v_a_367_);
lean_dec_ref(v___x_403_);
v___x_404_ = l_Lean_Elab_Frontend_setMessages___redArg(v_snd_390_, v_a_367_);
lean_dec_ref(v___x_404_);
lean_inc(v_fst_388_);
v___x_405_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_fst_388_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_414_; 
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v___x_405_, 0);
lean_dec(v_unused_415_);
v___x_407_ = v___x_405_;
v_isShared_408_ = v_isSharedCheck_414_;
goto v_resetjp_406_;
}
else
{
lean_dec(v___x_405_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_414_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_409_ = l_Lean_Parser_isTerminalCommand(v_fst_388_);
v___x_410_ = lean_box(v___x_409_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_410_);
v___x_412_ = v___x_407_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_fst_388_);
v_a_416_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_405_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_405_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_processCommand_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_366_ = stack[0].m_obj;
lean_object* v_a_367_ = stack[1].m_obj;
lean_object* v_res_426_;
v_res_426_ = l_Lean_Elab_Frontend_processCommand(v_a_366_, v_a_367_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Elab_Frontend_processCommand(v_a_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_430_;
}
}
lean_object* l_Lean_Elab_Frontend_processCommands(lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Elab_Frontend_processCommand(v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_445_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_445_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint8_t v___x_439_; 
v___x_439_ = lean_unbox(v_a_435_);
lean_dec(v_a_435_);
if (v___x_439_ == 0)
{
lean_del_object(v___x_437_);
goto _start;
}
else
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = lean_box(0);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_441_);
v___x_443_ = v___x_437_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_a_446_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_434_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_434_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Frontend_processCommands_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_431_ = stack[0].m_obj;
lean_object* v_a_432_ = stack[1].m_obj;
lean_object* v_res_454_;
v_res_454_ = l_Lean_Elab_Frontend_processCommands(v_a_431_, v_a_432_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands___boxed(lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Elab_Frontend_processCommands(v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(lean_object* v_a_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_461_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_459_, v___x_460_);
return v___x_461_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object* v_as_462_, size_t v_i_463_, size_t v_stop_464_, lean_object* v_b_465_){
_start:
{
lean_object* v___y_467_; uint8_t v___x_471_; 
v___x_471_ = lean_usize_dec_eq(v_i_463_, v_stop_464_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
v___x_472_ = lean_array_uget_borrowed(v_as_462_, v_i_463_);
if (lean_obj_tag(v___x_472_) == 0)
{
v___y_467_ = v_b_465_;
goto v___jp_466_;
}
else
{
lean_object* v_val_473_; lean_object* v___x_474_; 
v_val_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_val_473_);
v___x_474_ = lean_array_push(v_b_465_, v_val_473_);
v___y_467_ = v___x_474_;
goto v___jp_466_;
}
}
else
{
return v_b_465_;
}
v___jp_466_:
{
size_t v___x_468_; size_t v___x_469_; 
v___x_468_ = ((size_t)1ULL);
v___x_469_ = lean_usize_add(v_i_463_, v___x_468_);
v_i_463_ = v___x_469_;
v_b_465_ = v___y_467_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_462_ = stack[0].m_obj;
size_t v_i_463_ = stack[1].m_num;
size_t v_stop_464_ = stack[2].m_num;
lean_object* v_b_465_ = stack[3].m_obj;
lean_object* v_res_475_;
v_res_475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_462_, v_i_463_, v_stop_464_, v_b_465_);
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object* v_as_476_, lean_object* v_i_477_, lean_object* v_stop_478_, lean_object* v_b_479_){
_start:
{
size_t v_i_boxed_480_; size_t v_stop_boxed_481_; lean_object* v_res_482_; 
v_i_boxed_480_ = lean_unbox_usize(v_i_477_);
lean_dec(v_i_477_);
v_stop_boxed_481_ = lean_unbox_usize(v_stop_478_);
lean_dec(v_stop_478_);
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_476_, v_i_boxed_480_, v_stop_boxed_481_, v_b_479_);
lean_dec_ref(v_as_476_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object* v_as_485_, lean_object* v_start_486_, lean_object* v_stop_487_){
_start:
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_489_ = lean_nat_dec_lt(v_start_486_, v_stop_487_);
if (v___x_489_ == 0)
{
return v___x_488_;
}
else
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_array_get_size(v_as_485_);
v___x_491_ = lean_nat_dec_le(v_stop_487_, v___x_490_);
if (v___x_491_ == 0)
{
uint8_t v___x_492_; 
v___x_492_ = lean_nat_dec_lt(v_start_486_, v___x_490_);
if (v___x_492_ == 0)
{
return v___x_488_;
}
else
{
size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_usize_of_nat(v_start_486_);
v___x_494_ = lean_usize_of_nat(v___x_490_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_485_, v___x_493_, v___x_494_, v___x_488_);
return v___x_495_;
}
}
else
{
size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_usize_of_nat(v_start_486_);
v___x_497_ = lean_usize_of_nat(v_stop_487_);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_485_, v___x_496_, v___x_497_, v___x_488_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object* v_as_499_, lean_object* v_start_500_, lean_object* v_stop_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v_as_499_, v_start_500_, v_stop_501_);
lean_dec(v_stop_501_);
lean_dec(v_start_500_);
lean_dec_ref(v_as_499_);
return v_res_502_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(size_t v_sz_503_, size_t v_i_504_, lean_object* v_bs_505_){
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
lean_object* v_v_507_; lean_object* v_diagnostics_508_; lean_object* v_msgLog_509_; lean_object* v___x_510_; lean_object* v_bs_x27_511_; size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v_v_507_ = lean_array_uget_borrowed(v_bs_505_, v_i_504_);
v_diagnostics_508_ = lean_ctor_get(v_v_507_, 1);
v_msgLog_509_ = lean_ctor_get(v_diagnostics_508_, 0);
lean_inc_ref(v_msgLog_509_);
v___x_510_ = lean_unsigned_to_nat(0u);
v_bs_x27_511_ = lean_array_uset(v_bs_505_, v_i_504_, v___x_510_);
v___x_512_ = ((size_t)1ULL);
v___x_513_ = lean_usize_add(v_i_504_, v___x_512_);
v___x_514_ = lean_array_uset(v_bs_x27_511_, v_i_504_, v_msgLog_509_);
v_i_504_ = v___x_513_;
v_bs_505_ = v___x_514_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_503_ = stack[0].m_num;
size_t v_i_504_ = stack[1].m_num;
lean_object* v_bs_505_ = stack[2].m_obj;
lean_object* v_res_516_;
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_503_, v_i_504_, v_bs_505_);
stack->m_obj
 = v_res_516_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object* v_sz_517_, lean_object* v_i_518_, lean_object* v_bs_519_){
_start:
{
size_t v_sz_boxed_520_; size_t v_i_boxed_521_; lean_object* v_res_522_; 
v_sz_boxed_520_ = lean_unbox_usize(v_sz_517_);
lean_dec(v_sz_517_);
v_i_boxed_521_ = lean_unbox_usize(v_i_518_);
lean_dec(v_i_518_);
v_res_522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_boxed_520_, v_i_boxed_521_, v_bs_519_);
return v_res_522_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t v_sz_523_, size_t v_i_524_, lean_object* v_bs_525_){
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
lean_object* v_v_527_; lean_object* v_elabSnap_528_; lean_object* v_infoTreeSnap_529_; lean_object* v___x_530_; lean_object* v_infoTree_x3f_531_; lean_object* v___x_532_; lean_object* v_bs_x27_533_; size_t v___x_534_; size_t v___x_535_; lean_object* v___x_536_; 
v_v_527_ = lean_array_uget_borrowed(v_bs_525_, v_i_524_);
v_elabSnap_528_ = lean_ctor_get(v_v_527_, 3);
v_infoTreeSnap_529_ = lean_ctor_get(v_elabSnap_528_, 3);
lean_inc_ref(v_infoTreeSnap_529_);
v___x_530_ = l_Lean_Language_SnapshotTask_get___redArg(v_infoTreeSnap_529_);
v_infoTree_x3f_531_ = lean_ctor_get(v___x_530_, 2);
lean_inc(v_infoTree_x3f_531_);
lean_dec(v___x_530_);
v___x_532_ = lean_unsigned_to_nat(0u);
v_bs_x27_533_ = lean_array_uset(v_bs_525_, v_i_524_, v___x_532_);
v___x_534_ = ((size_t)1ULL);
v___x_535_ = lean_usize_add(v_i_524_, v___x_534_);
v___x_536_ = lean_array_uset(v_bs_x27_533_, v_i_524_, v_infoTree_x3f_531_);
v_i_524_ = v___x_535_;
v_bs_525_ = v___x_536_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_523_ = stack[0].m_num;
size_t v_i_524_ = stack[1].m_num;
lean_object* v_bs_525_ = stack[2].m_obj;
lean_object* v_res_538_;
v_res_538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_523_, v_i_524_, v_bs_525_);
stack->m_obj
 = v_res_538_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object* v_sz_539_, lean_object* v_i_540_, lean_object* v_bs_541_){
_start:
{
size_t v_sz_boxed_542_; size_t v_i_boxed_543_; lean_object* v_res_544_; 
v_sz_boxed_542_ = lean_unbox_usize(v_sz_539_);
lean_dec(v_sz_539_);
v_i_boxed_543_ = lean_unbox_usize(v_i_540_);
lean_dec(v_i_540_);
v_res_544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_boxed_542_, v_i_boxed_543_, v_bs_541_);
return v_res_544_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t v_sz_545_, size_t v_i_546_, lean_object* v_bs_547_){
_start:
{
uint8_t v___x_548_; 
v___x_548_ = lean_usize_dec_lt(v_i_546_, v_sz_545_);
if (v___x_548_ == 0)
{
return v_bs_547_;
}
else
{
lean_object* v_v_549_; lean_object* v_stx_550_; lean_object* v___x_551_; lean_object* v_bs_x27_552_; size_t v___x_553_; size_t v___x_554_; lean_object* v___x_555_; 
v_v_549_ = lean_array_uget_borrowed(v_bs_547_, v_i_546_);
v_stx_550_ = lean_ctor_get(v_v_549_, 1);
lean_inc(v_stx_550_);
v___x_551_ = lean_unsigned_to_nat(0u);
v_bs_x27_552_ = lean_array_uset(v_bs_547_, v_i_546_, v___x_551_);
v___x_553_ = ((size_t)1ULL);
v___x_554_ = lean_usize_add(v_i_546_, v___x_553_);
v___x_555_ = lean_array_uset(v_bs_x27_552_, v_i_546_, v_stx_550_);
v_i_546_ = v___x_554_;
v_bs_547_ = v___x_555_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_545_ = stack[0].m_num;
size_t v_i_546_ = stack[1].m_num;
lean_object* v_bs_547_ = stack[2].m_obj;
lean_object* v_res_557_;
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_545_, v_i_546_, v_bs_547_);
stack->m_obj
 = v_res_557_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object* v_sz_558_, lean_object* v_i_559_, lean_object* v_bs_560_){
_start:
{
size_t v_sz_boxed_561_; size_t v_i_boxed_562_; lean_object* v_res_563_; 
v_sz_boxed_561_ = lean_unbox_usize(v_sz_558_);
lean_dec(v_sz_558_);
v_i_boxed_562_ = lean_unbox_usize(v_i_559_);
lean_dec(v_i_559_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_boxed_561_, v_i_boxed_562_, v_bs_560_);
return v_res_563_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(lean_object* v_as_564_, size_t v_i_565_, size_t v_stop_566_, lean_object* v_b_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = lean_usize_dec_eq(v_i_565_, v_stop_566_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; size_t v___x_571_; size_t v___x_572_; 
v___x_569_ = lean_array_uget_borrowed(v_as_564_, v_i_565_);
lean_inc(v___x_569_);
v___x_570_ = l_Lean_MessageLog_append(v_b_567_, v___x_569_);
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_565_, v___x_571_);
v_i_565_ = v___x_572_;
v_b_567_ = v___x_570_;
goto _start;
}
else
{
return v_b_567_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_564_ = stack[0].m_obj;
size_t v_i_565_ = stack[1].m_num;
size_t v_stop_566_ = stack[2].m_num;
lean_object* v_b_567_ = stack[3].m_obj;
lean_object* v_res_574_;
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v_as_564_, v_i_565_, v_stop_566_, v_b_567_);
stack->m_obj
 = v_res_574_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5___boxed(lean_object* v_as_575_, lean_object* v_i_576_, lean_object* v_stop_577_, lean_object* v_b_578_){
_start:
{
size_t v_i_boxed_579_; size_t v_stop_boxed_580_; lean_object* v_res_581_; 
v_i_boxed_579_ = lean_unbox_usize(v_i_576_);
lean_dec(v_i_576_);
v_stop_boxed_580_ = lean_unbox_usize(v_stop_577_);
lean_dec(v_stop_577_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v_as_575_, v_i_boxed_579_, v_stop_boxed_580_, v_b_578_);
lean_dec_ref(v_as_575_);
return v_res_581_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_unsigned_to_nat(32u);
v___x_583_ = lean_mk_empty_array_with_capacity(v___x_582_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1(void){
_start:
{
size_t v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_585_ = ((size_t)5ULL);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_unsigned_to_nat(32u);
v___x_588_ = lean_mk_empty_array_with_capacity(v___x_587_);
v___x_589_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0);
v___x_590_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___x_588_);
lean_ctor_set(v___x_590_, 2, v___x_586_);
lean_ctor_set(v___x_590_, 3, v___x_586_);
lean_ctor_set_usize(v___x_590_, 4, v___x_585_);
return v___x_590_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = l_Lean_NameSet_empty;
v___x_592_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1);
v___x_593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
lean_ctor_set(v___x_593_, 2, v___x_591_);
return v___x_593_;
}
}
lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(lean_object* v_inputCtx_594_, lean_object* v_initialSnap_595_, lean_object* v_t_596_, lean_object* v_commands_597_){
_start:
{
lean_object* v_snap_599_; lean_object* v_parserState_600_; lean_object* v_elabSnap_601_; lean_object* v_nextCmdSnap_x3f_602_; lean_object* v_commands_603_; 
v_snap_599_ = lean_task_get_own(v_t_596_);
v_parserState_600_ = lean_ctor_get(v_snap_599_, 2);
lean_inc_ref(v_parserState_600_);
v_elabSnap_601_ = lean_ctor_get(v_snap_599_, 3);
lean_inc_ref(v_elabSnap_601_);
v_nextCmdSnap_x3f_602_ = lean_ctor_get(v_snap_599_, 4);
lean_inc(v_nextCmdSnap_x3f_602_);
v_commands_603_ = lean_array_push(v_commands_597_, v_snap_599_);
if (lean_obj_tag(v_nextCmdSnap_x3f_602_) == 1)
{
lean_object* v_val_604_; lean_object* v_task_605_; 
lean_dec_ref(v_elabSnap_601_);
lean_dec_ref(v_parserState_600_);
v_val_604_ = lean_ctor_get(v_nextCmdSnap_x3f_602_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v_nextCmdSnap_x3f_602_, 1);
v_task_605_ = lean_ctor_get(v_val_604_, 3);
lean_inc_ref(v_task_605_);
lean_dec(v_val_604_);
v_t_596_ = v_task_605_;
v_commands_597_ = v_commands_603_;
goto _start;
}
else
{
lean_object* v___x_607_; lean_object* v___y_609_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; size_t v_sz_665_; size_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
lean_dec(v_nextCmdSnap_x3f_602_);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_662_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
lean_inc_ref(v_initialSnap_595_);
v___x_663_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_initialSnap_595_);
v___x_664_ = l_Lean_Language_SnapshotTree_getAll(v___x_663_);
v_sz_665_ = lean_array_size(v___x_664_);
v___x_666_ = ((size_t)0ULL);
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_665_, v___x_666_, v___x_664_);
v___x_668_ = lean_array_get_size(v___x_667_);
v___x_669_ = lean_nat_dec_lt(v___x_607_, v___x_668_);
if (v___x_669_ == 0)
{
lean_dec_ref(v___x_667_);
v___y_609_ = v___x_662_;
goto v___jp_608_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_le(v___x_668_, v___x_668_);
if (v___x_670_ == 0)
{
if (v___x_669_ == 0)
{
lean_dec_ref(v___x_667_);
v___y_609_ = v___x_662_;
goto v___jp_608_;
}
else
{
size_t v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_usize_of_nat(v___x_668_);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v___x_667_, v___x_666_, v___x_671_, v___x_662_);
lean_dec_ref(v___x_667_);
v___y_609_ = v___x_672_;
goto v___jp_608_;
}
}
else
{
size_t v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_usize_of_nat(v___x_668_);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v___x_667_, v___x_666_, v___x_673_, v___x_662_);
lean_dec_ref(v___x_667_);
v___y_609_ = v___x_674_;
goto v___jp_608_;
}
}
v___jp_608_:
{
size_t v_sz_610_; lean_object* v_resultSnap_611_; lean_object* v___x_612_; lean_object* v_cmdState_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_659_; 
v_sz_610_ = lean_array_size(v_commands_603_);
v_resultSnap_611_ = lean_ctor_get(v_elabSnap_601_, 2);
lean_inc_ref(v_resultSnap_611_);
lean_dec_ref(v_elabSnap_601_);
v___x_612_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_611_);
v_cmdState_613_ = lean_ctor_get(v___x_612_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; lean_object* v_unused_661_; 
v_unused_660_ = lean_ctor_get(v___x_612_, 2);
lean_dec(v_unused_660_);
v_unused_661_ = lean_ctor_get(v___x_612_, 0);
lean_dec(v_unused_661_);
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_659_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_cmdState_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_659_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_infoState_617_; lean_object* v_env_618_; lean_object* v_scopes_619_; lean_object* v_usedQuotCtxts_620_; lean_object* v_nextMacroScope_621_; lean_object* v_maxRecDepth_622_; lean_object* v_ngen_623_; lean_object* v_auxDeclNGen_624_; lean_object* v_traceState_625_; lean_object* v_snapshotTasks_626_; lean_object* v_prevLinterStates_627_; lean_object* v_codeQualityEntryTasks_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_657_; 
v_infoState_617_ = lean_ctor_get(v_cmdState_613_, 8);
v_env_618_ = lean_ctor_get(v_cmdState_613_, 0);
v_scopes_619_ = lean_ctor_get(v_cmdState_613_, 2);
v_usedQuotCtxts_620_ = lean_ctor_get(v_cmdState_613_, 3);
v_nextMacroScope_621_ = lean_ctor_get(v_cmdState_613_, 4);
v_maxRecDepth_622_ = lean_ctor_get(v_cmdState_613_, 5);
v_ngen_623_ = lean_ctor_get(v_cmdState_613_, 6);
v_auxDeclNGen_624_ = lean_ctor_get(v_cmdState_613_, 7);
v_traceState_625_ = lean_ctor_get(v_cmdState_613_, 9);
v_snapshotTasks_626_ = lean_ctor_get(v_cmdState_613_, 10);
v_prevLinterStates_627_ = lean_ctor_get(v_cmdState_613_, 11);
v_codeQualityEntryTasks_628_ = lean_ctor_get(v_cmdState_613_, 12);
v_isSharedCheck_657_ = !lean_is_exclusive(v_cmdState_613_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v_cmdState_613_, 1);
lean_dec(v_unused_658_);
v___x_630_ = v_cmdState_613_;
v_isShared_631_ = v_isSharedCheck_657_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_codeQualityEntryTasks_628_);
lean_inc(v_prevLinterStates_627_);
lean_inc(v_snapshotTasks_626_);
lean_inc(v_traceState_625_);
lean_inc(v_infoState_617_);
lean_inc(v_auxDeclNGen_624_);
lean_inc(v_ngen_623_);
lean_inc(v_maxRecDepth_622_);
lean_inc(v_nextMacroScope_621_);
lean_inc(v_usedQuotCtxts_620_);
lean_inc(v_scopes_619_);
lean_inc(v_env_618_);
lean_dec(v_cmdState_613_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_657_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
uint8_t v_enabled_632_; lean_object* v_assignment_633_; lean_object* v_lazyAssignment_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_655_; 
v_enabled_632_ = lean_ctor_get_uint8(v_infoState_617_, sizeof(void*)*3);
v_assignment_633_ = lean_ctor_get(v_infoState_617_, 0);
v_lazyAssignment_634_ = lean_ctor_get(v_infoState_617_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_infoState_617_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v_infoState_617_, 2);
lean_dec(v_unused_656_);
v___x_636_ = v_infoState_617_;
v_isShared_637_ = v_isSharedCheck_655_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_lazyAssignment_634_);
lean_inc(v_assignment_633_);
lean_dec(v_infoState_617_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_655_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v_pos_638_; size_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v_trees_643_; lean_object* v___x_645_; 
v_pos_638_ = lean_ctor_get(v_parserState_600_, 0);
lean_inc(v_pos_638_);
v___x_639_ = ((size_t)0ULL);
lean_inc_ref(v_commands_603_);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_610_, v___x_639_, v_commands_603_);
v___x_641_ = lean_array_get_size(v___x_640_);
v___x_642_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v___x_640_, v___x_607_, v___x_641_);
lean_dec_ref(v___x_640_);
v_trees_643_ = l_Lean_Array_toPArray_x27___redArg(v___x_642_);
lean_dec_ref(v___x_642_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 2, v_trees_643_);
v___x_645_ = v___x_636_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_assignment_633_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_lazyAssignment_634_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_trees_643_);
lean_ctor_set_uint8(v_reuseFailAlloc_654_, sizeof(void*)*3, v_enabled_632_);
v___x_645_ = v_reuseFailAlloc_654_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_647_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 8, v___x_645_);
lean_ctor_set(v___x_630_, 1, v___y_609_);
v___x_647_ = v___x_630_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_env_618_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___y_609_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_scopes_619_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_usedQuotCtxts_620_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v_nextMacroScope_621_);
lean_ctor_set(v_reuseFailAlloc_653_, 5, v_maxRecDepth_622_);
lean_ctor_set(v_reuseFailAlloc_653_, 6, v_ngen_623_);
lean_ctor_set(v_reuseFailAlloc_653_, 7, v_auxDeclNGen_624_);
lean_ctor_set(v_reuseFailAlloc_653_, 8, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_653_, 9, v_traceState_625_);
lean_ctor_set(v_reuseFailAlloc_653_, 10, v_snapshotTasks_626_);
lean_ctor_set(v_reuseFailAlloc_653_, 11, v_prevLinterStates_627_);
lean_ctor_set(v_reuseFailAlloc_653_, 12, v_codeQualityEntryTasks_628_);
v___x_647_ = v_reuseFailAlloc_653_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_610_, v___x_639_, v_commands_603_);
v___x_649_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v_parserState_600_);
lean_ctor_set(v___x_649_, 2, v_pos_638_);
lean_ctor_set(v___x_649_, 3, v___x_648_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 2, v_initialSnap_595_);
lean_ctor_set(v___x_615_, 1, v_inputCtx_594_);
lean_ctor_set(v___x_615_, 0, v___x_649_);
v___x_651_ = v___x_615_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_inputCtx_594_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_initialSnap_595_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
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
LEAN_EXPORT void l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_inputCtx_594_ = stack[0].m_obj;
lean_object* v_initialSnap_595_ = stack[1].m_obj;
lean_object* v_t_596_ = stack[2].m_obj;
lean_object* v_commands_597_ = stack[3].m_obj;
lean_object* v_res_675_;
v_res_675_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_594_, v_initialSnap_595_, v_t_596_, v_commands_597_);
stack->m_obj
 = v_res_675_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___boxed(lean_object* v_inputCtx_676_, lean_object* v_initialSnap_677_, lean_object* v_t_678_, lean_object* v_commands_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_676_, v_initialSnap_677_, v_t_678_, v_commands_679_);
return v_res_681_;
}
}
lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object* v_inputCtx_684_, lean_object* v_parserState_685_, lean_object* v_commandState_686_, lean_object* v_old_x3f_687_){
_start:
{
lean_object* v___y_690_; 
if (lean_obj_tag(v_old_x3f_687_) == 0)
{
lean_object* v___x_695_; 
v___x_695_ = lean_box(0);
v___y_690_ = v___x_695_;
goto v___jp_689_;
}
else
{
lean_object* v_val_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_706_; 
v_val_696_ = lean_ctor_get(v_old_x3f_687_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v_old_x3f_687_);
if (v_isSharedCheck_706_ == 0)
{
v___x_698_ = v_old_x3f_687_;
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_val_696_);
lean_dec(v_old_x3f_687_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_inputCtx_700_; lean_object* v_initialSnap_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v_inputCtx_700_ = lean_ctor_get(v_val_696_, 1);
lean_inc_ref(v_inputCtx_700_);
v_initialSnap_701_ = lean_ctor_get(v_val_696_, 2);
lean_inc_ref(v_initialSnap_701_);
lean_dec(v_val_696_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_inputCtx_700_);
lean_ctor_set(v___x_702_, 1, v_initialSnap_701_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_702_);
v___x_704_ = v___x_698_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
v___y_690_ = v___x_704_;
goto v___jp_689_;
}
}
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_691_ = l_Lean_Language_Lean_processCommands(v_inputCtx_684_, v_parserState_685_, v_commandState_686_, v___y_690_);
lean_inc_ref(v___x_691_);
v___x_692_ = lean_task_get_own(v___x_691_);
v___x_693_ = ((lean_object*)(l_Lean_Elab_IO_processCommandsIncrementally___closed__0));
v___x_694_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_684_, v___x_692_, v___x_691_, v___x_693_);
return v___x_694_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_IO_processCommandsIncrementally_0interp(lean_interpreter_value* stack)
{
lean_object* v_inputCtx_684_ = stack[0].m_obj;
lean_object* v_parserState_685_ = stack[1].m_obj;
lean_object* v_commandState_686_ = stack[2].m_obj;
lean_object* v_old_x3f_687_ = stack[3].m_obj;
lean_object* v_res_707_;
v_res_707_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_684_, v_parserState_685_, v_commandState_686_, v_old_x3f_687_);
stack->m_obj
 = v_res_707_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally___boxed(lean_object* v_inputCtx_708_, lean_object* v_parserState_709_, lean_object* v_commandState_710_, lean_object* v_old_x3f_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_708_, v_parserState_709_, v_commandState_710_, v_old_x3f_711_);
return v_res_713_;
}
}
lean_object* l_Lean_Elab_IO_processCommands(lean_object* v_inputCtx_714_, lean_object* v_parserState_715_, lean_object* v_commandState_716_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_toState_720_; lean_object* v___x_721_; 
v___x_718_ = lean_box(0);
v___x_719_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_714_, v_parserState_715_, v_commandState_716_, v___x_718_);
v_toState_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc_ref(v_toState_720_);
lean_dec_ref(v___x_719_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_toState_720_);
return v___x_721_;
}
}
LEAN_EXPORT void l_Lean_Elab_IO_processCommands_0interp(lean_interpreter_value* stack)
{
lean_object* v_inputCtx_714_ = stack[0].m_obj;
lean_object* v_parserState_715_ = stack[1].m_obj;
lean_object* v_commandState_716_ = stack[2].m_obj;
lean_object* v_res_722_;
v_res_722_ = l_Lean_Elab_IO_processCommands(v_inputCtx_714_, v_parserState_715_, v_commandState_716_);
stack->m_obj
 = v_res_722_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands___boxed(lean_object* v_inputCtx_723_, lean_object* v_parserState_724_, lean_object* v_commandState_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Elab_IO_processCommands(v_inputCtx_723_, v_parserState_724_, v_commandState_725_);
return v_res_727_;
}
}
lean_object* l_Lean_Elab_process(lean_object* v_input_733_, lean_object* v_env_734_, lean_object* v_opts_735_, lean_object* v_fileName_736_){
_start:
{
lean_object* v___y_739_; 
if (lean_obj_tag(v_fileName_736_) == 0)
{
lean_object* v___x_759_; 
v___x_759_ = ((lean_object*)(l_Lean_Elab_process___closed__1));
v___y_739_ = v___x_759_;
goto v___jp_738_;
}
else
{
lean_object* v_val_760_; 
v_val_760_ = lean_ctor_get(v_fileName_736_, 0);
lean_inc(v_val_760_);
lean_dec_ref_known(v_fileName_736_, 1);
v___y_739_ = v_val_760_;
goto v___jp_738_;
}
v___jp_738_:
{
uint8_t v___x_740_; lean_object* v___x_741_; lean_object* v_inputCtx_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_758_; 
v___x_740_ = 1;
v___x_741_ = lean_string_utf8_byte_size(v_input_733_);
v_inputCtx_742_ = l_Lean_Parser_mkInputContext___redArg(v_input_733_, v___y_739_, v___x_740_, v___x_741_);
v___x_743_ = ((lean_object*)(l_Lean_Elab_process___closed__0));
v___x_744_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
v___x_745_ = l_Lean_Elab_Command_mkState(v_env_734_, v___x_744_, v_opts_735_);
v___x_746_ = l_Lean_Elab_IO_processCommands(v_inputCtx_742_, v___x_743_, v___x_745_);
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_758_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_758_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_758_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_commandState_751_; lean_object* v_env_752_; lean_object* v_messages_753_; lean_object* v___x_754_; lean_object* v___x_756_; 
v_commandState_751_ = lean_ctor_get(v_a_747_, 0);
lean_inc_ref(v_commandState_751_);
lean_dec(v_a_747_);
v_env_752_ = lean_ctor_get(v_commandState_751_, 0);
lean_inc_ref(v_env_752_);
v_messages_753_ = lean_ctor_get(v_commandState_751_, 1);
lean_inc_ref(v_messages_753_);
lean_dec_ref(v_commandState_751_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_env_752_);
lean_ctor_set(v___x_754_, 1, v_messages_753_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_754_);
v___x_756_ = v___x_749_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_process_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_733_ = stack[0].m_obj;
lean_object* v_env_734_ = stack[1].m_obj;
lean_object* v_opts_735_ = stack[2].m_obj;
lean_object* v_fileName_736_ = stack[3].m_obj;
lean_object* v_res_761_;
v_res_761_ = l_Lean_Elab_process(v_input_733_, v_env_734_, v_opts_735_, v_fileName_736_);
stack->m_obj
 = v_res_761_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_process___boxed(lean_object* v_input_762_, lean_object* v_env_763_, lean_object* v_opts_764_, lean_object* v_fileName_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Elab_process(v_input_762_, v_env_763_, v_opts_764_, v_fileName_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(lean_object* v_t_768_, lean_object* v_cmdStx_x3f_769_, lean_object* v_acc_770_){
_start:
{
lean_object* v_element_771_; lean_object* v_diagnostics_772_; lean_object* v_children_773_; lean_object* v_msgLog_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_792_; 
v_element_771_ = lean_ctor_get(v_t_768_, 0);
v_diagnostics_772_ = lean_ctor_get(v_element_771_, 1);
lean_inc_ref(v_diagnostics_772_);
v_children_773_ = lean_ctor_get(v_t_768_, 1);
lean_inc_ref(v_children_773_);
lean_dec_ref(v_t_768_);
v_msgLog_774_ = lean_ctor_get(v_diagnostics_772_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v_diagnostics_772_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_diagnostics_772_, 1);
lean_dec(v_unused_793_);
v___x_776_ = v_diagnostics_772_;
v_isShared_777_ = v_isSharedCheck_792_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_msgLog_774_);
lean_dec(v_diagnostics_772_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_792_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
lean_inc(v_cmdStx_x3f_769_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v_msgLog_774_);
lean_ctor_set(v___x_776_, 0, v_cmdStx_x3f_769_);
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_cmdStx_x3f_769_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_msgLog_774_);
v___x_779_ = v_reuseFailAlloc_791_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v_acc_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_acc_780_ = lean_array_push(v_acc_770_, v___x_779_);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_array_get_size(v_children_773_);
v___x_783_ = lean_nat_dec_lt(v___x_781_, v___x_782_);
if (v___x_783_ == 0)
{
lean_dec_ref(v_children_773_);
lean_dec(v_cmdStx_x3f_769_);
return v_acc_780_;
}
else
{
uint8_t v___x_784_; 
v___x_784_ = lean_nat_dec_le(v___x_782_, v___x_782_);
if (v___x_784_ == 0)
{
if (v___x_783_ == 0)
{
lean_dec_ref(v_children_773_);
lean_dec(v_cmdStx_x3f_769_);
return v_acc_780_;
}
else
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
v___x_785_ = ((size_t)0ULL);
v___x_786_ = lean_usize_of_nat(v___x_782_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_769_, v_children_773_, v___x_785_, v___x_786_, v_acc_780_);
lean_dec_ref(v_children_773_);
return v___x_787_;
}
}
else
{
size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; 
v___x_788_ = ((size_t)0ULL);
v___x_789_ = lean_usize_of_nat(v___x_782_);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_769_, v_children_773_, v___x_788_, v___x_789_, v_acc_780_);
lean_dec_ref(v_children_773_);
return v___x_790_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(lean_object* v_cmdStx_x3f_794_, lean_object* v_as_795_, size_t v_i_796_, size_t v_stop_797_, lean_object* v_b_798_){
_start:
{
lean_object* v___y_800_; uint8_t v___x_804_; 
v___x_804_ = lean_usize_dec_eq(v_i_796_, v_stop_797_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v_stx_x3f_806_; lean_object* v___x_807_; 
v___x_805_ = lean_array_uget_borrowed(v_as_795_, v_i_796_);
v_stx_x3f_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v___x_805_);
v___x_807_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_805_);
if (lean_obj_tag(v_stx_x3f_806_) == 0)
{
lean_object* v___x_808_; 
lean_inc(v_cmdStx_x3f_794_);
v___x_808_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_807_, v_cmdStx_x3f_794_, v_b_798_);
v___y_800_ = v___x_808_;
goto v___jp_799_;
}
else
{
lean_object* v___x_809_; 
lean_inc_ref(v_stx_x3f_806_);
v___x_809_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_807_, v_stx_x3f_806_, v_b_798_);
v___y_800_ = v___x_809_;
goto v___jp_799_;
}
}
else
{
lean_dec(v_cmdStx_x3f_794_);
return v_b_798_;
}
v___jp_799_:
{
size_t v___x_801_; size_t v___x_802_; 
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_796_, v___x_801_);
v_i_796_ = v___x_802_;
v_b_798_ = v___y_800_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmdStx_x3f_794_ = stack[0].m_obj;
lean_object* v_as_795_ = stack[1].m_obj;
size_t v_i_796_ = stack[2].m_num;
size_t v_stop_797_ = stack[3].m_num;
lean_object* v_b_798_ = stack[4].m_obj;
lean_object* v_res_810_;
v_res_810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_794_, v_as_795_, v_i_796_, v_stop_797_, v_b_798_);
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0___boxed(lean_object* v_cmdStx_x3f_811_, lean_object* v_as_812_, lean_object* v_i_813_, lean_object* v_stop_814_, lean_object* v_b_815_){
_start:
{
size_t v_i_boxed_816_; size_t v_stop_boxed_817_; lean_object* v_res_818_; 
v_i_boxed_816_ = lean_unbox_usize(v_i_813_);
lean_dec(v_i_813_);
v_stop_boxed_817_ = lean_unbox_usize(v_stop_814_);
lean_dec(v_stop_814_);
v_res_818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_811_, v_as_812_, v_i_boxed_816_, v_stop_boxed_817_, v_b_815_);
lean_dec_ref(v_as_812_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3(lean_object* v_filePath_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_lean_x3f_821_; lean_object* v_olean_x3f_822_; lean_object* v_oleanServer_x3f_823_; lean_object* v_ilean_x3f_824_; lean_object* v_irSig_x3f_825_; lean_object* v_ir_x3f_826_; lean_object* v_c_x3f_827_; lean_object* v_bc_x3f_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_836_; 
v_lean_x3f_821_ = lean_ctor_get(v_a_820_, 0);
v_olean_x3f_822_ = lean_ctor_get(v_a_820_, 1);
v_oleanServer_x3f_823_ = lean_ctor_get(v_a_820_, 2);
v_ilean_x3f_824_ = lean_ctor_get(v_a_820_, 4);
v_irSig_x3f_825_ = lean_ctor_get(v_a_820_, 5);
v_ir_x3f_826_ = lean_ctor_get(v_a_820_, 6);
v_c_x3f_827_ = lean_ctor_get(v_a_820_, 7);
v_bc_x3f_828_ = lean_ctor_get(v_a_820_, 8);
v_isSharedCheck_836_ = !lean_is_exclusive(v_a_820_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v_a_820_, 3);
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
lean_inc(v_oleanServer_x3f_823_);
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
lean_ctor_set(v___x_830_, 3, v___x_832_);
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_lean_x3f_821_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_olean_x3f_822_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_oleanServer_x3f_823_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v___x_832_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1(lean_object* v_filePath_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_lean_x3f_840_; lean_object* v_olean_x3f_841_; lean_object* v_oleanServer_x3f_842_; lean_object* v_oleanPrivate_x3f_843_; lean_object* v_ilean_x3f_844_; lean_object* v_ir_x3f_845_; lean_object* v_c_x3f_846_; lean_object* v_bc_x3f_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_855_; 
v_lean_x3f_840_ = lean_ctor_get(v_a_839_, 0);
v_olean_x3f_841_ = lean_ctor_get(v_a_839_, 1);
v_oleanServer_x3f_842_ = lean_ctor_get(v_a_839_, 2);
v_oleanPrivate_x3f_843_ = lean_ctor_get(v_a_839_, 3);
v_ilean_x3f_844_ = lean_ctor_get(v_a_839_, 4);
v_ir_x3f_845_ = lean_ctor_get(v_a_839_, 6);
v_c_x3f_846_ = lean_ctor_get(v_a_839_, 7);
v_bc_x3f_847_ = lean_ctor_get(v_a_839_, 8);
v_isSharedCheck_855_ = !lean_is_exclusive(v_a_839_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; 
v_unused_856_ = lean_ctor_get(v_a_839_, 5);
lean_dec(v_unused_856_);
v___x_849_ = v_a_839_;
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_bc_x3f_847_);
lean_inc(v_c_x3f_846_);
lean_inc(v_ir_x3f_845_);
lean_inc(v_ilean_x3f_844_);
lean_inc(v_oleanPrivate_x3f_843_);
lean_inc(v_oleanServer_x3f_842_);
lean_inc(v_olean_x3f_841_);
lean_inc(v_lean_x3f_840_);
lean_dec(v_a_839_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v_filePath_838_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 5, v___x_851_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_lean_x3f_840_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_olean_x3f_841_);
lean_ctor_set(v_reuseFailAlloc_854_, 2, v_oleanServer_x3f_842_);
lean_ctor_set(v_reuseFailAlloc_854_, 3, v_oleanPrivate_x3f_843_);
lean_ctor_set(v_reuseFailAlloc_854_, 4, v_ilean_x3f_844_);
lean_ctor_set(v_reuseFailAlloc_854_, 5, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_854_, 6, v_ir_x3f_845_);
lean_ctor_set(v_reuseFailAlloc_854_, 7, v_c_x3f_846_);
lean_ctor_set(v_reuseFailAlloc_854_, 8, v_bc_x3f_847_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4(lean_object* v_filePath_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_lean_x3f_859_; lean_object* v_olean_x3f_860_; lean_object* v_oleanPrivate_x3f_861_; lean_object* v_ilean_x3f_862_; lean_object* v_irSig_x3f_863_; lean_object* v_ir_x3f_864_; lean_object* v_c_x3f_865_; lean_object* v_bc_x3f_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_874_; 
v_lean_x3f_859_ = lean_ctor_get(v_a_858_, 0);
v_olean_x3f_860_ = lean_ctor_get(v_a_858_, 1);
v_oleanPrivate_x3f_861_ = lean_ctor_get(v_a_858_, 3);
v_ilean_x3f_862_ = lean_ctor_get(v_a_858_, 4);
v_irSig_x3f_863_ = lean_ctor_get(v_a_858_, 5);
v_ir_x3f_864_ = lean_ctor_get(v_a_858_, 6);
v_c_x3f_865_ = lean_ctor_get(v_a_858_, 7);
v_bc_x3f_866_ = lean_ctor_get(v_a_858_, 8);
v_isSharedCheck_874_ = !lean_is_exclusive(v_a_858_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v_a_858_, 2);
lean_dec(v_unused_875_);
v___x_868_ = v_a_858_;
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_bc_x3f_866_);
lean_inc(v_c_x3f_865_);
lean_inc(v_ir_x3f_864_);
lean_inc(v_irSig_x3f_863_);
lean_inc(v_ilean_x3f_862_);
lean_inc(v_oleanPrivate_x3f_861_);
lean_inc(v_olean_x3f_860_);
lean_inc(v_lean_x3f_859_);
lean_dec(v_a_858_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_870_, 0, v_filePath_857_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 2, v___x_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_lean_x3f_859_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_olean_x3f_860_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_873_, 3, v_oleanPrivate_x3f_861_);
lean_ctor_set(v_reuseFailAlloc_873_, 4, v_ilean_x3f_862_);
lean_ctor_set(v_reuseFailAlloc_873_, 5, v_irSig_x3f_863_);
lean_ctor_set(v_reuseFailAlloc_873_, 6, v_ir_x3f_864_);
lean_ctor_set(v_reuseFailAlloc_873_, 7, v_c_x3f_865_);
lean_ctor_set(v_reuseFailAlloc_873_, 8, v_bc_x3f_866_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(lean_object* v_a_876_, lean_object* v_x_877_){
_start:
{
if (lean_obj_tag(v_x_877_) == 0)
{
uint8_t v___x_878_; 
v___x_878_ = 0;
return v___x_878_;
}
else
{
lean_object* v_key_879_; lean_object* v_tail_880_; uint8_t v___x_881_; 
v_key_879_ = lean_ctor_get(v_x_877_, 0);
v_tail_880_ = lean_ctor_get(v_x_877_, 2);
v___x_881_ = lean_string_dec_eq(v_key_879_, v_a_876_);
if (v___x_881_ == 0)
{
v_x_877_ = v_tail_880_;
goto _start;
}
else
{
return v___x_881_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_876_ = stack[0].m_obj;
lean_object* v_x_877_ = stack[1].m_obj;
uint8_t v_res_883_;
v_res_883_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_876_, v_x_877_);
stack->m_num = v_res_883_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg___boxed(lean_object* v_a_884_, lean_object* v_x_885_){
_start:
{
uint8_t v_res_886_; lean_object* v_r_887_; 
v_res_886_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_884_, v_x_885_);
lean_dec(v_x_885_);
lean_dec_ref(v_a_884_);
v_r_887_ = lean_box(v_res_886_);
return v_r_887_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(lean_object* v_m_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_buckets_890_; lean_object* v___x_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v_fold_895_; uint64_t v___x_896_; uint64_t v___x_897_; uint64_t v___x_898_; size_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_buckets_890_ = lean_ctor_get(v_m_888_, 1);
v___x_891_ = lean_array_get_size(v_buckets_890_);
v___x_892_ = lean_string_hash(v_a_889_);
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
v___x_905_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_889_, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_888_ = stack[0].m_obj;
lean_object* v_a_889_ = stack[1].m_obj;
uint8_t v_res_906_;
v_res_906_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_888_, v_a_889_);
stack->m_num = v_res_906_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg___boxed(lean_object* v_m_907_, lean_object* v_a_908_){
_start:
{
uint8_t v_res_909_; lean_object* v_r_910_; 
v_res_909_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_907_, v_a_908_);
lean_dec_ref(v_a_908_);
lean_dec_ref(v_m_907_);
v_r_910_ = lean_box(v_res_909_);
return v_r_910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(lean_object* v_a_911_, lean_object* v_fallback_912_, lean_object* v_x_913_){
_start:
{
if (lean_obj_tag(v_x_913_) == 0)
{
lean_inc(v_fallback_912_);
return v_fallback_912_;
}
else
{
lean_object* v_key_914_; lean_object* v_value_915_; lean_object* v_tail_916_; uint8_t v___x_917_; 
v_key_914_ = lean_ctor_get(v_x_913_, 0);
v_value_915_ = lean_ctor_get(v_x_913_, 1);
v_tail_916_ = lean_ctor_get(v_x_913_, 2);
v___x_917_ = lean_string_dec_eq(v_key_914_, v_a_911_);
if (v___x_917_ == 0)
{
v_x_913_ = v_tail_916_;
goto _start;
}
else
{
lean_inc(v_value_915_);
return v_value_915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg___boxed(lean_object* v_a_919_, lean_object* v_fallback_920_, lean_object* v_x_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_919_, v_fallback_920_, v_x_921_);
lean_dec(v_x_921_);
lean_dec(v_fallback_920_);
lean_dec_ref(v_a_919_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(lean_object* v_m_923_, lean_object* v_a_924_, lean_object* v_fallback_925_){
_start:
{
lean_object* v_buckets_926_; lean_object* v___x_927_; uint64_t v___x_928_; uint64_t v___x_929_; uint64_t v___x_930_; uint64_t v_fold_931_; uint64_t v___x_932_; uint64_t v___x_933_; uint64_t v___x_934_; size_t v___x_935_; size_t v___x_936_; size_t v___x_937_; size_t v___x_938_; size_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_buckets_926_ = lean_ctor_get(v_m_923_, 1);
v___x_927_ = lean_array_get_size(v_buckets_926_);
v___x_928_ = lean_string_hash(v_a_924_);
v___x_929_ = 32ULL;
v___x_930_ = lean_uint64_shift_right(v___x_928_, v___x_929_);
v_fold_931_ = lean_uint64_xor(v___x_928_, v___x_930_);
v___x_932_ = 16ULL;
v___x_933_ = lean_uint64_shift_right(v_fold_931_, v___x_932_);
v___x_934_ = lean_uint64_xor(v_fold_931_, v___x_933_);
v___x_935_ = lean_uint64_to_usize(v___x_934_);
v___x_936_ = lean_usize_of_nat(v___x_927_);
v___x_937_ = ((size_t)1ULL);
v___x_938_ = lean_usize_sub(v___x_936_, v___x_937_);
v___x_939_ = lean_usize_land(v___x_935_, v___x_938_);
v___x_940_ = lean_array_uget_borrowed(v_buckets_926_, v___x_939_);
v___x_941_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_924_, v_fallback_925_, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg___boxed(lean_object* v_m_942_, lean_object* v_a_943_, lean_object* v_fallback_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_942_, v_a_943_, v_fallback_944_);
lean_dec(v_fallback_944_);
lean_dec_ref(v_a_943_);
lean_dec_ref(v_m_942_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2(lean_object* v_filePath_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_lean_x3f_948_; lean_object* v_olean_x3f_949_; lean_object* v_oleanServer_x3f_950_; lean_object* v_oleanPrivate_x3f_951_; lean_object* v_ilean_x3f_952_; lean_object* v_irSig_x3f_953_; lean_object* v_c_x3f_954_; lean_object* v_bc_x3f_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_963_; 
v_lean_x3f_948_ = lean_ctor_get(v_a_947_, 0);
v_olean_x3f_949_ = lean_ctor_get(v_a_947_, 1);
v_oleanServer_x3f_950_ = lean_ctor_get(v_a_947_, 2);
v_oleanPrivate_x3f_951_ = lean_ctor_get(v_a_947_, 3);
v_ilean_x3f_952_ = lean_ctor_get(v_a_947_, 4);
v_irSig_x3f_953_ = lean_ctor_get(v_a_947_, 5);
v_c_x3f_954_ = lean_ctor_get(v_a_947_, 7);
v_bc_x3f_955_ = lean_ctor_get(v_a_947_, 8);
v_isSharedCheck_963_ = !lean_is_exclusive(v_a_947_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v_a_947_, 6);
lean_dec(v_unused_964_);
v___x_957_ = v_a_947_;
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_bc_x3f_955_);
lean_inc(v_c_x3f_954_);
lean_inc(v_irSig_x3f_953_);
lean_inc(v_ilean_x3f_952_);
lean_inc(v_oleanPrivate_x3f_951_);
lean_inc(v_oleanServer_x3f_950_);
lean_inc(v_olean_x3f_949_);
lean_inc(v_lean_x3f_948_);
lean_dec(v_a_947_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v_filePath_946_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 6, v___x_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_lean_x3f_948_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_olean_x3f_949_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_oleanServer_x3f_950_);
lean_ctor_set(v_reuseFailAlloc_962_, 3, v_oleanPrivate_x3f_951_);
lean_ctor_set(v_reuseFailAlloc_962_, 4, v_ilean_x3f_952_);
lean_ctor_set(v_reuseFailAlloc_962_, 5, v_irSig_x3f_953_);
lean_ctor_set(v_reuseFailAlloc_962_, 6, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_962_, 7, v_c_x3f_954_);
lean_ctor_set(v_reuseFailAlloc_962_, 8, v_bc_x3f_955_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0(lean_object* v_filePath_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_lean_x3f_967_; lean_object* v_oleanServer_x3f_968_; lean_object* v_oleanPrivate_x3f_969_; lean_object* v_ilean_x3f_970_; lean_object* v_irSig_x3f_971_; lean_object* v_ir_x3f_972_; lean_object* v_c_x3f_973_; lean_object* v_bc_x3f_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_982_; 
v_lean_x3f_967_ = lean_ctor_get(v_a_966_, 0);
v_oleanServer_x3f_968_ = lean_ctor_get(v_a_966_, 2);
v_oleanPrivate_x3f_969_ = lean_ctor_get(v_a_966_, 3);
v_ilean_x3f_970_ = lean_ctor_get(v_a_966_, 4);
v_irSig_x3f_971_ = lean_ctor_get(v_a_966_, 5);
v_ir_x3f_972_ = lean_ctor_get(v_a_966_, 6);
v_c_x3f_973_ = lean_ctor_get(v_a_966_, 7);
v_bc_x3f_974_ = lean_ctor_get(v_a_966_, 8);
v_isSharedCheck_982_ = !lean_is_exclusive(v_a_966_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_a_966_, 1);
lean_dec(v_unused_983_);
v___x_976_ = v_a_966_;
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_bc_x3f_974_);
lean_inc(v_c_x3f_973_);
lean_inc(v_ir_x3f_972_);
lean_inc(v_irSig_x3f_971_);
lean_inc(v_ilean_x3f_970_);
lean_inc(v_oleanPrivate_x3f_969_);
lean_inc(v_oleanServer_x3f_968_);
lean_inc(v_lean_x3f_967_);
lean_dec(v_a_966_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v_filePath_965_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_lean_x3f_967_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_oleanServer_x3f_968_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_oleanPrivate_x3f_969_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_ilean_x3f_970_);
lean_ctor_set(v_reuseFailAlloc_981_, 5, v_irSig_x3f_971_);
lean_ctor_set(v_reuseFailAlloc_981_, 6, v_ir_x3f_972_);
lean_ctor_set(v_reuseFailAlloc_981_, 7, v_c_x3f_973_);
lean_ctor_set(v_reuseFailAlloc_981_, 8, v_bc_x3f_974_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(lean_object* v_a_984_, lean_object* v_b_985_, lean_object* v_x_986_){
_start:
{
if (lean_obj_tag(v_x_986_) == 0)
{
lean_dec(v_b_985_);
lean_dec_ref(v_a_984_);
return v_x_986_;
}
else
{
lean_object* v_key_987_; lean_object* v_value_988_; lean_object* v_tail_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1001_; 
v_key_987_ = lean_ctor_get(v_x_986_, 0);
v_value_988_ = lean_ctor_get(v_x_986_, 1);
v_tail_989_ = lean_ctor_get(v_x_986_, 2);
v_isSharedCheck_1001_ = !lean_is_exclusive(v_x_986_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_991_ = v_x_986_;
v_isShared_992_ = v_isSharedCheck_1001_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_tail_989_);
lean_inc(v_value_988_);
lean_inc(v_key_987_);
lean_dec(v_x_986_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1001_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
uint8_t v___x_993_; 
v___x_993_ = lean_string_dec_eq(v_key_987_, v_a_984_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_984_, v_b_985_, v_tail_989_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 2, v___x_994_);
v___x_996_ = v___x_991_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_key_987_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_value_988_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
lean_object* v___x_999_; 
lean_dec(v_value_988_);
lean_dec(v_key_987_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v_b_985_);
lean_ctor_set(v___x_991_, 0, v_a_984_);
v___x_999_ = v___x_991_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_984_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_b_985_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_tail_989_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
if (lean_obj_tag(v_x_1003_) == 0)
{
return v_x_1002_;
}
else
{
lean_object* v_key_1004_; lean_object* v_value_1005_; lean_object* v_tail_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1029_; 
v_key_1004_ = lean_ctor_get(v_x_1003_, 0);
v_value_1005_ = lean_ctor_get(v_x_1003_, 1);
v_tail_1006_ = lean_ctor_get(v_x_1003_, 2);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_x_1003_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1008_ = v_x_1003_;
v_isShared_1009_ = v_isSharedCheck_1029_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_tail_1006_);
lean_inc(v_value_1005_);
lean_inc(v_key_1004_);
lean_dec(v_x_1003_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1029_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; uint64_t v___x_1011_; uint64_t v___x_1012_; uint64_t v___x_1013_; uint64_t v_fold_1014_; uint64_t v___x_1015_; uint64_t v___x_1016_; uint64_t v___x_1017_; size_t v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; size_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1010_ = lean_array_get_size(v_x_1002_);
v___x_1011_ = lean_string_hash(v_key_1004_);
v___x_1012_ = 32ULL;
v___x_1013_ = lean_uint64_shift_right(v___x_1011_, v___x_1012_);
v_fold_1014_ = lean_uint64_xor(v___x_1011_, v___x_1013_);
v___x_1015_ = 16ULL;
v___x_1016_ = lean_uint64_shift_right(v_fold_1014_, v___x_1015_);
v___x_1017_ = lean_uint64_xor(v_fold_1014_, v___x_1016_);
v___x_1018_ = lean_uint64_to_usize(v___x_1017_);
v___x_1019_ = lean_usize_of_nat(v___x_1010_);
v___x_1020_ = ((size_t)1ULL);
v___x_1021_ = lean_usize_sub(v___x_1019_, v___x_1020_);
v___x_1022_ = lean_usize_land(v___x_1018_, v___x_1021_);
v___x_1023_ = lean_array_uget_borrowed(v_x_1002_, v___x_1022_);
lean_inc(v___x_1023_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 2, v___x_1023_);
v___x_1025_ = v___x_1008_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_key_1004_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_value_1005_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_array_uset(v_x_1002_, v___x_1022_, v___x_1025_);
v_x_1002_ = v___x_1026_;
v_x_1003_ = v_tail_1006_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1030_, lean_object* v_source_1031_, lean_object* v_target_1032_){
_start:
{
lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = lean_array_get_size(v_source_1031_);
v___x_1034_ = lean_nat_dec_lt(v_i_1030_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_dec_ref(v_source_1031_);
lean_dec(v_i_1030_);
return v_target_1032_;
}
else
{
lean_object* v_es_1035_; lean_object* v___x_1036_; lean_object* v_source_1037_; lean_object* v_target_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_es_1035_ = lean_array_fget(v_source_1031_, v_i_1030_);
v___x_1036_ = lean_box(0);
v_source_1037_ = lean_array_fset(v_source_1031_, v_i_1030_, v___x_1036_);
v_target_1038_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_target_1032_, v_es_1035_);
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_nat_add(v_i_1030_, v___x_1039_);
lean_dec(v_i_1030_);
v_i_1030_ = v___x_1040_;
v_source_1031_ = v_source_1037_;
v_target_1032_ = v_target_1038_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(lean_object* v_data_1042_){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_nbuckets_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1043_ = lean_array_get_size(v_data_1042_);
v___x_1044_ = lean_unsigned_to_nat(2u);
v_nbuckets_1045_ = lean_nat_mul(v___x_1043_, v___x_1044_);
v___x_1046_ = lean_unsigned_to_nat(0u);
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_mk_array(v_nbuckets_1045_, v___x_1047_);
v___x_1049_ = lean_array_propagate_mark(v_data_1042_, v___x_1048_);
v___x_1050_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v___x_1046_, v_data_1042_, v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object* v_m_1051_, lean_object* v_a_1052_, lean_object* v_b_1053_){
_start:
{
lean_object* v_size_1054_; lean_object* v_buckets_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1098_; 
v_size_1054_ = lean_ctor_get(v_m_1051_, 0);
v_buckets_1055_ = lean_ctor_get(v_m_1051_, 1);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_m_1051_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1057_ = v_m_1051_;
v_isShared_1058_ = v_isSharedCheck_1098_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_buckets_1055_);
lean_inc(v_size_1054_);
lean_dec(v_m_1051_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1098_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; uint64_t v___x_1060_; uint64_t v___x_1061_; uint64_t v___x_1062_; uint64_t v_fold_1063_; uint64_t v___x_1064_; uint64_t v___x_1065_; uint64_t v___x_1066_; size_t v___x_1067_; size_t v___x_1068_; size_t v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; lean_object* v_bkt_1072_; uint8_t v___x_1073_; 
v___x_1059_ = lean_array_get_size(v_buckets_1055_);
v___x_1060_ = lean_string_hash(v_a_1052_);
v___x_1061_ = 32ULL;
v___x_1062_ = lean_uint64_shift_right(v___x_1060_, v___x_1061_);
v_fold_1063_ = lean_uint64_xor(v___x_1060_, v___x_1062_);
v___x_1064_ = 16ULL;
v___x_1065_ = lean_uint64_shift_right(v_fold_1063_, v___x_1064_);
v___x_1066_ = lean_uint64_xor(v_fold_1063_, v___x_1065_);
v___x_1067_ = lean_uint64_to_usize(v___x_1066_);
v___x_1068_ = lean_usize_of_nat(v___x_1059_);
v___x_1069_ = ((size_t)1ULL);
v___x_1070_ = lean_usize_sub(v___x_1068_, v___x_1069_);
v___x_1071_ = lean_usize_land(v___x_1067_, v___x_1070_);
v_bkt_1072_ = lean_array_uget_borrowed(v_buckets_1055_, v___x_1071_);
v___x_1073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1052_, v_bkt_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v_size_x27_1075_; lean_object* v___x_1076_; lean_object* v_buckets_x27_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1074_ = lean_unsigned_to_nat(1u);
v_size_x27_1075_ = lean_nat_add(v_size_1054_, v___x_1074_);
lean_dec(v_size_1054_);
lean_inc(v_bkt_1072_);
v___x_1076_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1076_, 0, v_a_1052_);
lean_ctor_set(v___x_1076_, 1, v_b_1053_);
lean_ctor_set(v___x_1076_, 2, v_bkt_1072_);
v_buckets_x27_1077_ = lean_array_uset(v_buckets_1055_, v___x_1071_, v___x_1076_);
v___x_1078_ = lean_unsigned_to_nat(4u);
v___x_1079_ = lean_nat_mul(v_size_x27_1075_, v___x_1078_);
v___x_1080_ = lean_unsigned_to_nat(3u);
v___x_1081_ = lean_nat_div(v___x_1079_, v___x_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_array_get_size(v_buckets_x27_1077_);
v___x_1083_ = lean_nat_dec_le(v___x_1081_, v___x_1082_);
lean_dec(v___x_1081_);
if (v___x_1083_ == 0)
{
lean_object* v_val_1084_; lean_object* v___x_1086_; 
v_val_1084_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_buckets_x27_1077_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v_val_1084_);
lean_ctor_set(v___x_1057_, 0, v_size_x27_1075_);
v___x_1086_ = v___x_1057_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_size_x27_1075_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_val_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
else
{
lean_object* v___x_1089_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v_buckets_x27_1077_);
lean_ctor_set(v___x_1057_, 0, v_size_x27_1075_);
v___x_1089_ = v___x_1057_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_size_x27_1075_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_buckets_x27_1077_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
else
{
lean_object* v___x_1091_; lean_object* v_buckets_x27_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
lean_inc(v_bkt_1072_);
v___x_1091_ = lean_box(0);
v_buckets_x27_1092_ = lean_array_uset(v_buckets_1055_, v___x_1071_, v___x_1091_);
v___x_1093_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1052_, v_b_1053_, v_bkt_1072_);
v___x_1094_ = lean_array_uset(v_buckets_x27_1092_, v___x_1071_, v___x_1093_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v___x_1094_);
v___x_1096_ = v___x_1057_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_size_1054_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object* v_as_1107_, size_t v_sz_1108_, size_t v_i_1109_, lean_object* v_b_1110_){
_start:
{
uint8_t v___x_1111_; 
v___x_1111_ = lean_usize_dec_lt(v_i_1109_, v_sz_1108_);
if (v___x_1111_ == 0)
{
return v_b_1110_;
}
else
{
lean_object* v_fst_1112_; lean_object* v_snd_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1163_; 
v_fst_1112_ = lean_ctor_get(v_b_1110_, 0);
v_snd_1113_ = lean_ctor_get(v_b_1110_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_b_1110_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1115_ = v_b_1110_;
v_isShared_1116_ = v_isSharedCheck_1163_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_snd_1113_);
lean_inc(v_fst_1112_);
lean_dec(v_b_1110_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1163_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v_order_1120_; lean_object* v_fst_1132_; lean_object* v_snd_1133_; lean_object* v_a_1136_; lean_object* v_filePath_1137_; lean_object* v___f_1138_; lean_object* v___x_1139_; 
v_a_1136_ = lean_array_uget_borrowed(v_as_1107_, v_i_1109_);
v_filePath_1137_ = lean_ctor_get(v_a_1136_, 0);
lean_inc_ref_n(v_filePath_1137_, 2);
v___f_1138_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1138_, 0, v_filePath_1137_);
v___x_1139_ = l_System_FilePath_extension(v_filePath_1137_);
if (lean_obj_tag(v___x_1139_) == 1)
{
lean_object* v_val_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v_val_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_val_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1));
v___x_1142_ = lean_string_dec_eq(v_val_1140_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2));
v___x_1144_ = lean_string_dec_eq(v_val_1140_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3));
v___x_1146_ = lean_string_dec_eq(v_val_1140_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4));
v___x_1148_ = lean_string_dec_eq(v_val_1140_, v___x_1147_);
lean_dec(v_val_1140_);
if (v___x_1148_ == 0)
{
lean_inc_ref(v_filePath_1137_);
v_fst_1132_ = v_filePath_1137_;
v_snd_1133_ = v___f_1138_;
goto v___jp_1131_;
}
else
{
lean_object* v___f_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec_ref(v___f_1138_);
lean_inc_ref_n(v_filePath_1137_, 2);
v___f_1149_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1), 2, 1);
lean_closure_set(v___f_1149_, 0, v_filePath_1137_);
v___x_1150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1151_ = l_System_FilePath_withExtension(v_filePath_1137_, v___x_1150_);
v___x_1152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1153_ = l_System_FilePath_withExtension(v___x_1151_, v___x_1152_);
v_fst_1132_ = v___x_1153_;
v_snd_1133_ = v___f_1149_;
goto v___jp_1131_;
}
}
else
{
lean_object* v___f_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec(v_val_1140_);
lean_dec_ref(v___f_1138_);
lean_inc_ref_n(v_filePath_1137_, 2);
v___f_1154_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2), 2, 1);
lean_closure_set(v___f_1154_, 0, v_filePath_1137_);
v___x_1155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1156_ = l_System_FilePath_withExtension(v_filePath_1137_, v___x_1155_);
v_fst_1132_ = v___x_1156_;
v_snd_1133_ = v___f_1154_;
goto v___jp_1131_;
}
}
else
{
lean_object* v___f_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_dec(v_val_1140_);
lean_dec_ref(v___f_1138_);
lean_inc_ref_n(v_filePath_1137_, 2);
v___f_1157_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3), 2, 1);
lean_closure_set(v___f_1157_, 0, v_filePath_1137_);
v___x_1158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1159_ = l_System_FilePath_withExtension(v_filePath_1137_, v___x_1158_);
v_fst_1132_ = v___x_1159_;
v_snd_1133_ = v___f_1157_;
goto v___jp_1131_;
}
}
else
{
lean_object* v___f_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec(v_val_1140_);
lean_dec_ref(v___f_1138_);
lean_inc_ref_n(v_filePath_1137_, 2);
v___f_1160_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4), 2, 1);
lean_closure_set(v___f_1160_, 0, v_filePath_1137_);
v___x_1161_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1162_ = l_System_FilePath_withExtension(v_filePath_1137_, v___x_1161_);
v_fst_1132_ = v___x_1162_;
v_snd_1133_ = v___f_1160_;
goto v___jp_1131_;
}
}
else
{
lean_dec(v___x_1139_);
lean_inc_ref(v_filePath_1137_);
v_fst_1132_ = v_filePath_1137_;
v_snd_1133_ = v___f_1138_;
goto v___jp_1131_;
}
v___jp_1117_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0));
v___x_1122_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_snd_1113_, v___y_1118_, v___x_1121_);
v___x_1123_ = lean_apply_1(v___y_1119_, v___x_1122_);
v___x_1124_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_snd_1113_, v___y_1118_, v___x_1123_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 1, v___x_1124_);
lean_ctor_set(v___x_1115_, 0, v_order_1120_);
v___x_1126_ = v___x_1115_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_order_1120_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
size_t v___x_1127_; size_t v___x_1128_; 
v___x_1127_ = ((size_t)1ULL);
v___x_1128_ = lean_usize_add(v_i_1109_, v___x_1127_);
v_i_1109_ = v___x_1128_;
v_b_1110_ = v___x_1126_;
goto _start;
}
}
v___jp_1131_:
{
uint8_t v___x_1134_; 
v___x_1134_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1113_, v_fst_1132_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_inc_ref(v_fst_1132_);
v___x_1135_ = lean_array_push(v_fst_1112_, v_fst_1132_);
v___y_1118_ = v_fst_1132_;
v___y_1119_ = v_snd_1133_;
v_order_1120_ = v___x_1135_;
goto v___jp_1117_;
}
else
{
v___y_1118_ = v_fst_1132_;
v___y_1119_ = v_snd_1133_;
v_order_1120_ = v_fst_1112_;
goto v___jp_1117_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1107_ = stack[0].m_obj;
size_t v_sz_1108_ = stack[1].m_num;
size_t v_i_1109_ = stack[2].m_num;
lean_object* v_b_1110_ = stack[3].m_obj;
lean_object* v_res_1164_;
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_as_1107_, v_sz_1108_, v_i_1109_, v_b_1110_);
stack->m_obj
 = v_res_1164_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object* v_as_1165_, lean_object* v_sz_1166_, lean_object* v_i_1167_, lean_object* v_b_1168_){
_start:
{
size_t v_sz_boxed_1169_; size_t v_i_boxed_1170_; lean_object* v_res_1171_; 
v_sz_boxed_1169_ = lean_unbox_usize(v_sz_1166_);
lean_dec(v_sz_1166_);
v_i_boxed_1170_ = lean_unbox_usize(v_i_1167_);
lean_dec(v_i_1167_);
v_res_1171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_as_1165_, v_sz_boxed_1169_, v_i_boxed_1170_, v_b_1168_);
lean_dec_ref(v_as_1165_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(lean_object* v_msg_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1174_ = lean_panic_fn_borrowed(v___x_1173_, v_msg_1172_);
return v___x_1174_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1178_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2));
v___x_1179_ = lean_unsigned_to_nat(11u);
v___x_1180_ = lean_unsigned_to_nat(163u);
v___x_1181_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1));
v___x_1182_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0));
v___x_1183_ = l_mkPanicMessageWithDecl(v___x_1182_, v___x_1181_, v___x_1180_, v___x_1179_, v___x_1178_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(lean_object* v_a_1184_, lean_object* v_x_1185_){
_start:
{
if (lean_obj_tag(v_x_1185_) == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3);
v___x_1187_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(v___x_1186_);
return v___x_1187_;
}
else
{
lean_object* v_key_1188_; lean_object* v_value_1189_; lean_object* v_tail_1190_; uint8_t v___x_1191_; 
v_key_1188_ = lean_ctor_get(v_x_1185_, 0);
v_value_1189_ = lean_ctor_get(v_x_1185_, 1);
v_tail_1190_ = lean_ctor_get(v_x_1185_, 2);
v___x_1191_ = lean_string_dec_eq(v_key_1188_, v_a_1184_);
if (v___x_1191_ == 0)
{
v_x_1185_ = v_tail_1190_;
goto _start;
}
else
{
lean_inc(v_value_1189_);
return v_value_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___boxed(lean_object* v_a_1193_, lean_object* v_x_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1193_, v_x_1194_);
lean_dec(v_x_1194_);
lean_dec_ref(v_a_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object* v_m_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_buckets_1198_; lean_object* v___x_1199_; uint64_t v___x_1200_; uint64_t v___x_1201_; uint64_t v___x_1202_; uint64_t v_fold_1203_; uint64_t v___x_1204_; uint64_t v___x_1205_; uint64_t v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; size_t v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_buckets_1198_ = lean_ctor_get(v_m_1196_, 1);
v___x_1199_ = lean_array_get_size(v_buckets_1198_);
v___x_1200_ = lean_string_hash(v_a_1197_);
v___x_1201_ = 32ULL;
v___x_1202_ = lean_uint64_shift_right(v___x_1200_, v___x_1201_);
v_fold_1203_ = lean_uint64_xor(v___x_1200_, v___x_1202_);
v___x_1204_ = 16ULL;
v___x_1205_ = lean_uint64_shift_right(v_fold_1203_, v___x_1204_);
v___x_1206_ = lean_uint64_xor(v_fold_1203_, v___x_1205_);
v___x_1207_ = lean_uint64_to_usize(v___x_1206_);
v___x_1208_ = lean_usize_of_nat(v___x_1199_);
v___x_1209_ = ((size_t)1ULL);
v___x_1210_ = lean_usize_sub(v___x_1208_, v___x_1209_);
v___x_1211_ = lean_usize_land(v___x_1207_, v___x_1210_);
v___x_1212_ = lean_array_uget_borrowed(v_buckets_1198_, v___x_1211_);
v___x_1213_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1197_, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object* v_m_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v_m_1214_, v_a_1215_);
lean_dec_ref(v_a_1215_);
lean_dec_ref(v_m_1214_);
return v_res_1216_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object* v___x_1217_, size_t v_sz_1218_, size_t v_i_1219_, lean_object* v_bs_1220_){
_start:
{
uint8_t v___x_1221_; 
v___x_1221_ = lean_usize_dec_lt(v_i_1219_, v_sz_1218_);
if (v___x_1221_ == 0)
{
return v_bs_1220_;
}
else
{
lean_object* v_v_1222_; lean_object* v___x_1223_; lean_object* v_bs_x27_1224_; lean_object* v___x_1225_; size_t v___x_1226_; size_t v___x_1227_; lean_object* v___x_1228_; 
v_v_1222_ = lean_array_uget(v_bs_1220_, v_i_1219_);
v___x_1223_ = lean_unsigned_to_nat(0u);
v_bs_x27_1224_ = lean_array_uset(v_bs_1220_, v_i_1219_, v___x_1223_);
v___x_1225_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v___x_1217_, v_v_1222_);
lean_dec(v_v_1222_);
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_add(v_i_1219_, v___x_1226_);
v___x_1228_ = lean_array_uset(v_bs_x27_1224_, v_i_1219_, v___x_1225_);
v_i_1219_ = v___x_1227_;
v_bs_1220_ = v___x_1228_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1217_ = stack[0].m_obj;
size_t v_sz_1218_ = stack[1].m_num;
size_t v_i_1219_ = stack[2].m_num;
lean_object* v_bs_1220_ = stack[3].m_obj;
lean_object* v_res_1230_;
v_res_1230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v___x_1217_, v_sz_1218_, v_i_1219_, v_bs_1220_);
stack->m_obj
 = v_res_1230_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object* v___x_1231_, lean_object* v_sz_1232_, lean_object* v_i_1233_, lean_object* v_bs_1234_){
_start:
{
size_t v_sz_boxed_1235_; size_t v_i_boxed_1236_; lean_object* v_res_1237_; 
v_sz_boxed_1235_ = lean_unbox_usize(v_sz_1232_);
lean_dec(v_sz_1232_);
v_i_boxed_1236_ = lean_unbox_usize(v_i_1233_);
lean_dec(v_i_1233_);
v_res_1237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v___x_1231_, v_sz_boxed_1235_, v_i_boxed_1236_, v_bs_1234_);
lean_dec_ref(v___x_1231_);
return v_res_1237_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_unsigned_to_nat(16u);
v___x_1242_ = lean_mk_array(v___x_1241_, v___x_1240_);
return v___x_1242_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_byBase_1245_; 
v___x_1243_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1);
v___x_1244_ = lean_unsigned_to_nat(0u);
v_byBase_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byBase_1245_, 0, v___x_1244_);
lean_ctor_set(v_byBase_1245_, 1, v___x_1243_);
return v_byBase_1245_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3(void){
_start:
{
lean_object* v_byBase_1246_; lean_object* v_order_1247_; lean_object* v___x_1248_; 
v_byBase_1246_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2);
v_order_1247_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0));
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_order_1247_);
lean_ctor_set(v___x_1248_, 1, v_byBase_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object* v_regions_1249_){
_start:
{
lean_object* v___x_1250_; size_t v_sz_1251_; size_t v___x_1252_; lean_object* v___x_1253_; lean_object* v_fst_1254_; lean_object* v_snd_1255_; size_t v_sz_1256_; lean_object* v___x_1257_; 
v___x_1250_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3);
v_sz_1251_ = lean_array_size(v_regions_1249_);
v___x_1252_ = ((size_t)0ULL);
v___x_1253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_regions_1249_, v_sz_1251_, v___x_1252_, v___x_1250_);
v_fst_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_fst_1254_);
v_snd_1255_ = lean_ctor_get(v___x_1253_, 1);
lean_inc(v_snd_1255_);
lean_dec_ref(v___x_1253_);
v_sz_1256_ = lean_array_size(v_fst_1254_);
v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v_snd_1255_, v_sz_1256_, v___x_1252_, v_fst_1254_);
lean_dec(v_snd_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object* v_regions_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1258_);
lean_dec_ref(v_regions_1258_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object* v_00_u03b2_1260_, lean_object* v_m_1261_, lean_object* v_a_1262_, lean_object* v_fallback_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_1261_, v_a_1262_, v_fallback_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object* v_00_u03b2_1265_, lean_object* v_m_1266_, lean_object* v_a_1267_, lean_object* v_fallback_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(v_00_u03b2_1265_, v_m_1266_, v_a_1267_, v_fallback_1268_);
lean_dec(v_fallback_1268_);
lean_dec_ref(v_a_1267_);
lean_dec_ref(v_m_1266_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object* v_00_u03b2_1270_, lean_object* v_m_1271_, lean_object* v_a_1272_, lean_object* v_b_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_1271_, v_a_1272_, v_b_1273_);
return v___x_1274_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object* v_00_u03b2_1275_, lean_object* v_m_1276_, lean_object* v_a_1277_){
_start:
{
uint8_t v___x_1278_; 
v___x_1278_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_1276_, v_a_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1276_ = stack[1].m_obj;
lean_object* v_a_1277_ = stack[2].m_obj;
uint8_t v_res_1279_;
v_res_1279_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_box(0), v_m_1276_, v_a_1277_);
stack->m_num = v_res_1279_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object* v_00_u03b2_1280_, lean_object* v_m_1281_, lean_object* v_a_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(v_00_u03b2_1280_, v_m_1281_, v_a_1282_);
lean_dec_ref(v_a_1282_);
lean_dec_ref(v_m_1281_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object* v_00_u03b2_1285_, lean_object* v_a_1286_, lean_object* v_fallback_1287_, lean_object* v_x_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_1286_, v_fallback_1287_, v_x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1290_, lean_object* v_a_1291_, lean_object* v_fallback_1292_, lean_object* v_x_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(v_00_u03b2_1290_, v_a_1291_, v_fallback_1292_, v_x_1293_);
lean_dec(v_x_1293_);
lean_dec(v_fallback_1292_);
lean_dec_ref(v_a_1291_);
return v_res_1294_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object* v_00_u03b2_1295_, lean_object* v_a_1296_, lean_object* v_x_1297_){
_start:
{
uint8_t v___x_1298_; 
v___x_1298_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1296_, v_x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1296_ = stack[1].m_obj;
lean_object* v_x_1297_ = stack[2].m_obj;
uint8_t v_res_1299_;
v_res_1299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_box(0), v_a_1296_, v_x_1297_);
stack->m_num = v_res_1299_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1300_, lean_object* v_a_1301_, lean_object* v_x_1302_){
_start:
{
uint8_t v_res_1303_; lean_object* v_r_1304_; 
v_res_1303_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(v_00_u03b2_1300_, v_a_1301_, v_x_1302_);
lean_dec(v_x_1302_);
lean_dec_ref(v_a_1301_);
v_r_1304_ = lean_box(v_res_1303_);
return v_r_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3(lean_object* v_00_u03b2_1305_, lean_object* v_data_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_data_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4(lean_object* v_00_u03b2_1308_, lean_object* v_a_1309_, lean_object* v_b_1310_, lean_object* v_x_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1309_, v_b_1310_, v_x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1313_, lean_object* v_i_1314_, lean_object* v_source_1315_, lean_object* v_target_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v_i_1314_, v_source_1315_, v_target_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1318_, lean_object* v_x_1319_, lean_object* v_x_1320_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_x_1319_, v_x_1320_);
return v___x_1321_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(lean_object* v_as_1322_, size_t v_sz_1323_, size_t v_i_1324_, lean_object* v_b_1325_){
_start:
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_usize_dec_lt(v_i_1324_, v_sz_1323_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_b_1325_);
return v___x_1328_;
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1330_; 
v_a_1329_ = lean_array_uget_borrowed(v_as_1322_, v_i_1324_);
v___x_1330_ = lean_compacted_region_read(v_a_1329_, v_b_1325_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v_snd_1332_; lean_object* v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v_snd_1332_ = lean_ctor_get(v_a_1331_, 1);
lean_inc(v_snd_1332_);
lean_dec(v_a_1331_);
v___x_1333_ = lean_array_push(v_b_1325_, v_snd_1332_);
v___x_1334_ = ((size_t)1ULL);
v___x_1335_ = lean_usize_add(v_i_1324_, v___x_1334_);
v_i_1324_ = v___x_1335_;
v_b_1325_ = v___x_1333_;
goto _start;
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec_ref(v_b_1325_);
v_a_1337_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1330_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1330_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1322_ = stack[0].m_obj;
size_t v_sz_1323_ = stack[1].m_num;
size_t v_i_1324_ = stack[2].m_num;
lean_object* v_b_1325_ = stack[3].m_obj;
lean_object* v_res_1345_;
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v_as_1322_, v_sz_1323_, v_i_1324_, v_b_1325_);
stack->m_obj
 = v_res_1345_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0___boxed(lean_object* v_as_1346_, lean_object* v_sz_1347_, lean_object* v_i_1348_, lean_object* v_b_1349_, lean_object* v___y_1350_){
_start:
{
size_t v_sz_boxed_1351_; size_t v_i_boxed_1352_; lean_object* v_res_1353_; 
v_sz_boxed_1351_ = lean_unbox_usize(v_sz_1347_);
lean_dec(v_sz_1347_);
v_i_boxed_1352_ = lean_unbox_usize(v_i_1348_);
lean_dec(v_i_1348_);
v_res_1353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v_as_1346_, v_sz_boxed_1351_, v_i_boxed_1352_, v_b_1349_);
lean_dec_ref(v_as_1346_);
return v_res_1353_;
}
}
lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(lean_object* v_arts_1356_){
_start:
{
lean_object* v_oleanRegions_1358_; lean_object* v___x_1359_; size_t v_sz_1360_; size_t v___x_1361_; lean_object* v___x_1362_; 
v_oleanRegions_1358_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc_ref(v_arts_1356_);
v___x_1359_ = l_Lean_ModuleArtifacts_oleanParts(v_arts_1356_);
v_sz_1360_ = lean_array_size(v___x_1359_);
v___x_1361_ = ((size_t)0ULL);
v___x_1362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1359_, v_sz_1360_, v___x_1361_, v_oleanRegions_1358_);
lean_dec_ref(v___x_1359_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; size_t v_sz_1365_; lean_object* v___x_1366_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1364_ = l_Lean_ModuleArtifacts_irParts(v_arts_1356_);
v_sz_1365_ = lean_array_size(v___x_1364_);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1364_, v_sz_1365_, v___x_1361_, v_oleanRegions_1358_);
lean_dec_ref(v___x_1364_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1375_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = l_Array_append___redArg(v_a_1363_, v_a_1367_);
lean_dec(v_a_1367_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
else
{
lean_dec(v_a_1363_);
return v___x_1366_;
}
}
else
{
lean_dec_ref(v_arts_1356_);
return v___x_1362_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_0interp(lean_interpreter_value* stack)
{
lean_object* v_arts_1356_ = stack[0].m_obj;
lean_object* v_res_1376_;
v_res_1376_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v_arts_1356_);
stack->m_obj
 = v_res_1376_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___boxed(lean_object* v_arts_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v_arts_1377_);
return v_res_1379_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(lean_object* v_e_1380_){
_start:
{
if (lean_obj_tag(v_e_1380_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1391_; 
v_a_1382_ = lean_ctor_get(v_e_1380_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_e_1380_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1384_ = v_e_1380_;
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v_e_1380_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1386_ = lean_io_error_to_string(v_a_1382_);
v___x_1387_ = lean_mk_io_user_error(v___x_1386_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set_tag(v___x_1384_, 1);
lean_ctor_set(v___x_1384_, 0, v___x_1387_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
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
v_a_1392_ = lean_ctor_get(v_e_1380_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_e_1380_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v_e_1380_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v_e_1380_);
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
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1380_ = stack[0].m_obj;
lean_object* v_res_1400_;
v_res_1400_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1380_);
stack->m_obj
 = v_res_1400_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg___boxed(lean_object* v_e_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1401_);
return v_res_1403_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_object* v_00_u03b1_1404_, lean_object* v_e_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1405_ = stack[1].m_obj;
lean_object* v_res_1408_;
v_res_1408_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_box(0), v_e_1405_);
stack->m_obj
 = v_res_1408_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___boxed(lean_object* v_00_u03b1_1409_, lean_object* v_e_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(v_00_u03b1_1409_, v_e_1410_);
return v_res_1412_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object* v_a_1413_, lean_object* v___y_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_fst_1417_; lean_object* v_snd_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1446_; 
v_fst_1417_ = lean_ctor_get(v_a_1415_, 0);
v_snd_1418_ = lean_ctor_get(v_a_1415_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_a_1415_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1420_ = v_a_1415_;
v_isShared_1421_ = v_isSharedCheck_1446_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_snd_1418_);
lean_inc(v_fst_1417_);
lean_dec(v_a_1415_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1446_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = lean_array_get_size(v_a_1413_);
v___x_1423_ = lean_nat_dec_lt(v_snd_1418_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1425_; 
if (v_isShared_1421_ == 0)
{
v___x_1425_ = v___x_1420_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_fst_1417_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_snd_1418_);
v___x_1425_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1429_ = lean_array_get_borrowed(v___x_1428_, v_a_1413_, v_snd_1418_);
lean_inc(v___x_1429_);
v___x_1430_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v___x_1429_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = l_Array_append___redArg(v_fst_1417_, v_a_1431_);
lean_dec(v_a_1431_);
v___x_1433_ = lean_nat_add(v_snd_1418_, v___y_1414_);
lean_dec(v_snd_1418_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v___x_1433_);
lean_ctor_set(v___x_1420_, 0, v___x_1432_);
v___x_1435_ = v___x_1420_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
v_a_1415_ = v___x_1435_;
goto _start;
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_del_object(v___x_1420_);
lean_dec(v_snd_1418_);
lean_dec(v_fst_1417_);
v_a_1438_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1430_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1430_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1413_ = stack[0].m_obj;
lean_object* v___y_1414_ = stack[1].m_obj;
lean_object* v_a_1415_ = stack[2].m_obj;
lean_object* v_res_1447_;
v_res_1447_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1413_, v___y_1414_, v_a_1415_);
stack->m_obj
 = v_res_1447_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object* v_a_1448_, lean_object* v___y_1449_, lean_object* v_a_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1448_, v___y_1449_, v_a_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v_a_1448_);
return v_res_1452_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(lean_object* v_a_1453_, lean_object* v___y_1454_, lean_object* v___x_1455_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1453_, v___y_1454_, v___x_1455_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1466_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v_fst_1462_; lean_object* v___x_1464_; 
v_fst_1462_ = lean_ctor_get(v_a_1458_, 0);
lean_inc(v_fst_1462_);
lean_dec(v_a_1458_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set_tag(v___x_1460_, 1);
lean_ctor_set(v___x_1460_, 0, v_fst_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_fst_1462_);
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
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
v_a_1467_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1457_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1457_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set_tag(v___x_1469_, 0);
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1453_ = stack[0].m_obj;
lean_object* v___y_1454_ = stack[1].m_obj;
lean_object* v___x_1455_ = stack[2].m_obj;
lean_object* v_res_1475_;
v_res_1475_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(v_a_1453_, v___y_1454_, v___x_1455_);
stack->m_obj
 = v_res_1475_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed(lean_object* v_a_1476_, lean_object* v___y_1477_, lean_object* v___x_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(v_a_1476_, v___y_1477_, v___x_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v_a_1476_);
return v_res_1480_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(lean_object* v_upperBound_1481_, lean_object* v_a_1482_, lean_object* v___y_1483_, lean_object* v_a_1484_, lean_object* v_b_1485_){
_start:
{
uint8_t v___x_1487_; 
v___x_1487_ = lean_nat_dec_lt(v_a_1484_, v_upperBound_1481_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; 
lean_dec(v_a_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v_a_1482_);
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v_b_1485_);
return v___x_1488_;
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc(v_a_1484_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v_a_1484_);
lean_inc(v___y_1483_);
lean_inc_ref(v_a_1482_);
v___f_1492_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1492_, 0, v_a_1482_);
lean_closure_set(v___f_1492_, 1, v___y_1483_);
lean_closure_set(v___f_1492_, 2, v___x_1491_);
v___x_1493_ = lean_io_as_task(v___f_1492_, v___x_1489_);
v___x_1494_ = lean_array_push(v_b_1485_, v___x_1493_);
v___x_1495_ = lean_unsigned_to_nat(1u);
v___x_1496_ = lean_nat_add(v_a_1484_, v___x_1495_);
lean_dec(v_a_1484_);
v_a_1484_ = v___x_1496_;
v_b_1485_ = v___x_1494_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1481_ = stack[0].m_obj;
lean_object* v_a_1482_ = stack[1].m_obj;
lean_object* v___y_1483_ = stack[2].m_obj;
lean_object* v_a_1484_ = stack[3].m_obj;
lean_object* v_b_1485_ = stack[4].m_obj;
lean_object* v_res_1498_;
v_res_1498_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1481_, v_a_1482_, v___y_1483_, v_a_1484_, v_b_1485_);
stack->m_obj
 = v_res_1498_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___boxed(lean_object* v_upperBound_1499_, lean_object* v_a_1500_, lean_object* v___y_1501_, lean_object* v_a_1502_, lean_object* v_b_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1499_, v_a_1500_, v___y_1501_, v_a_1502_, v_b_1503_);
lean_dec(v_upperBound_1499_);
return v_res_1505_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(lean_object* v_as_1506_, size_t v_sz_1507_, size_t v_i_1508_, lean_object* v_b_1509_){
_start:
{
uint8_t v___x_1511_; 
v___x_1511_ = lean_usize_dec_lt(v_i_1508_, v_sz_1507_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_b_1509_);
return v___x_1512_;
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v_a_1513_ = lean_array_uget_borrowed(v_as_1506_, v_i_1508_);
lean_inc(v_a_1513_);
v___x_1514_ = lean_task_get_own(v_a_1513_);
v___x_1515_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v___x_1514_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1517_ = l_Array_append___redArg(v_b_1509_, v_a_1516_);
lean_dec(v_a_1516_);
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = lean_usize_add(v_i_1508_, v___x_1518_);
v_i_1508_ = v___x_1519_;
v_b_1509_ = v___x_1517_;
goto _start;
}
else
{
lean_dec_ref(v_b_1509_);
return v___x_1515_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1506_ = stack[0].m_obj;
size_t v_sz_1507_ = stack[1].m_num;
size_t v_i_1508_ = stack[2].m_num;
lean_object* v_b_1509_ = stack[3].m_obj;
lean_object* v_res_1521_;
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_as_1506_, v_sz_1507_, v_i_1508_, v_b_1509_);
stack->m_obj
 = v_res_1521_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2___boxed(lean_object* v_as_1522_, lean_object* v_sz_1523_, lean_object* v_i_1524_, lean_object* v_b_1525_, lean_object* v___y_1526_){
_start:
{
size_t v_sz_boxed_1527_; size_t v_i_boxed_1528_; lean_object* v_res_1529_; 
v_sz_boxed_1527_ = lean_unbox_usize(v_sz_1523_);
lean_dec(v_sz_1523_);
v_i_boxed_1528_ = lean_unbox_usize(v_i_1524_);
lean_dec(v_i_1524_);
v_res_1529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_as_1522_, v_sz_boxed_1527_, v_i_boxed_1528_, v_b_1525_);
lean_dec_ref(v_as_1522_);
return v_res_1529_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t v_sz_1530_, size_t v_i_1531_, lean_object* v_bs_1532_){
_start:
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_usize_dec_lt(v_i_1531_, v_sz_1530_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v_bs_1532_);
return v___x_1534_;
}
else
{
lean_object* v_v_1535_; lean_object* v___x_1536_; 
v_v_1535_ = lean_array_uget_borrowed(v_bs_1532_, v_i_1531_);
lean_inc(v_v_1535_);
v___x_1536_ = l_Lean_instFromJsonModuleArtifacts_fromJson(v_v_1535_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec_ref(v_bs_1532_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1546_; lean_object* v_bs_x27_1547_; size_t v___x_1548_; size_t v___x_1549_; lean_object* v___x_1550_; 
v_a_1545_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1546_ = lean_unsigned_to_nat(0u);
v_bs_x27_1547_ = lean_array_uset(v_bs_1532_, v_i_1531_, v___x_1546_);
v___x_1548_ = ((size_t)1ULL);
v___x_1549_ = lean_usize_add(v_i_1531_, v___x_1548_);
v___x_1550_ = lean_array_uset(v_bs_x27_1547_, v_i_1531_, v_a_1545_);
v_i_1531_ = v___x_1549_;
v_bs_1532_ = v___x_1550_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1530_ = stack[0].m_num;
size_t v_i_1531_ = stack[1].m_num;
lean_object* v_bs_1532_ = stack[2].m_obj;
lean_object* v_res_1552_;
v_res_1552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_1530_, v_i_1531_, v_bs_1532_);
stack->m_obj
 = v_res_1552_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object* v_sz_1553_, lean_object* v_i_1554_, lean_object* v_bs_1555_){
_start:
{
size_t v_sz_boxed_1556_; size_t v_i_boxed_1557_; lean_object* v_res_1558_; 
v_sz_boxed_1556_ = lean_unbox_usize(v_sz_1553_);
lean_dec(v_sz_1553_);
v_i_boxed_1557_ = lean_unbox_usize(v_i_1554_);
lean_dec(v_i_1554_);
v_res_1558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_boxed_1556_, v_i_boxed_1557_, v_bs_1555_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object* v_x_1561_){
_start:
{
if (lean_obj_tag(v_x_1561_) == 4)
{
lean_object* v_elems_1562_; size_t v_sz_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
v_elems_1562_ = lean_ctor_get(v_x_1561_, 0);
lean_inc_ref(v_elems_1562_);
lean_dec_ref_known(v_x_1561_, 1);
v_sz_1563_ = lean_array_size(v_elems_1562_);
v___x_1564_ = ((size_t)0ULL);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_1563_, v___x_1564_, v_elems_1562_);
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1566_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0));
v___x_1567_ = lean_unsigned_to_nat(80u);
v___x_1568_ = l_Lean_Json_pretty(v_x_1561_, v___x_1567_);
v___x_1569_ = lean_string_append(v___x_1566_, v___x_1568_);
lean_dec_ref(v___x_1568_);
v___x_1570_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1));
v___x_1571_ = lean_string_append(v___x_1569_, v___x_1570_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
}
}
static uint32_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3(void){
_start:
{
lean_object* v___x_1576_; uint32_t v___x_1577_; 
v___x_1576_ = lean_box(0);
v___x_1577_ = lean_internal_get_hardware_concurrency(v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4(void){
_start:
{
uint32_t v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_uint32_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3);
v___x_1579_ = lean_uint32_to_nat(v___x_1578_);
return v___x_1579_;
}
}
static uint8_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1581_ = lean_unsigned_to_nat(4u);
v___x_1582_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1583_ = lean_nat_dec_le(v___x_1582_, v___x_1581_);
return v___x_1583_;
}
}
lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(lean_object* v_fname_1584_){
_start:
{
lean_object* v___x_1586_; lean_object* v_depsFile_1587_; lean_object* v___x_1588_; 
v___x_1586_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
lean_inc_ref(v_fname_1584_);
v_depsFile_1587_ = l_System_FilePath_addExtension(v_fname_1584_, v___x_1586_);
v___x_1588_ = l_IO_FS_readFile(v_depsFile_1587_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1675_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1675_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1675_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v_a_1594_; lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_Json_parse(v_a_1589_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; 
lean_dec_ref(v_fname_1584_);
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v_a_1594_ = v_a_1605_;
goto v___jp_1593_;
}
else
{
lean_object* v_a_1606_; lean_object* v___x_1607_; 
v_a_1606_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1604_, 1);
v___x_1607_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(v_a_1606_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; 
lean_dec_ref(v_fname_1584_);
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v_a_1594_ = v_a_1608_;
goto v___jp_1593_;
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___y_1613_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1664_; uint8_t v___x_1674_; 
lean_del_object(v___x_1591_);
lean_dec_ref(v_depsFile_1587_);
v_a_1609_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1607_, 1);
v___x_1610_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1611_ = lean_unsigned_to_nat(4u);
v___x_1674_ = lean_uint8_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6);
if (v___x_1674_ == 0)
{
v___y_1664_ = v___x_1611_;
goto v___jp_1663_;
}
else
{
v___y_1664_ = v___x_1610_;
goto v___jp_1663_;
}
v___jp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1614_ = lean_mk_empty_array_with_capacity(v___y_1613_);
v___x_1615_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_1609_);
lean_inc(v___y_1613_);
v___x_1616_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v___y_1613_, v_a_1609_, v___y_1613_, v___x_1615_, v___x_1614_);
lean_dec(v___y_1613_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; size_t v_sz_1621_; size_t v___x_1622_; lean_object* v___x_1623_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v___x_1618_ = lean_array_get_size(v_a_1609_);
lean_dec(v_a_1609_);
v___x_1619_ = lean_nat_mul(v___x_1618_, v___x_1611_);
v___x_1620_ = lean_mk_empty_array_with_capacity(v___x_1619_);
lean_dec(v___x_1619_);
v_sz_1621_ = lean_array_size(v_a_1617_);
v___x_1622_ = ((size_t)0ULL);
v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_a_1617_, v_sz_1621_, v___x_1622_, v___x_1620_);
lean_dec(v_a_1617_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1625_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1625_ = lean_compacted_region_read(v_fname_1584_, v_a_1624_);
lean_dec(v_a_1624_);
lean_dec_ref(v_fname_1584_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1634_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1634_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1634_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v_fst_1630_; lean_object* v___x_1632_; 
v_fst_1630_ = lean_ctor_get(v_a_1626_, 0);
lean_inc(v_fst_1630_);
lean_dec(v_a_1626_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v_fst_1630_);
v___x_1632_ = v___x_1628_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_fst_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
v_a_1635_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1625_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1625_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v_fname_1584_);
v_a_1643_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1623_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1623_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_a_1609_);
lean_dec_ref(v_fname_1584_);
v_a_1651_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1616_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1616_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
v___jp_1659_:
{
uint8_t v___x_1662_; 
v___x_1662_ = lean_nat_dec_le(v___y_1660_, v___y_1661_);
if (v___x_1662_ == 0)
{
lean_dec(v___y_1661_);
v___y_1613_ = v___y_1660_;
goto v___jp_1612_;
}
else
{
lean_dec(v___y_1660_);
v___y_1613_ = v___y_1661_;
goto v___jp_1612_;
}
}
v___jp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5));
v___x_1666_ = lean_io_getenv(v___x_1665_);
v___x_1667_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v___x_1666_) == 0)
{
v___y_1660_ = v___x_1667_;
v___y_1661_ = v___y_1664_;
goto v___jp_1659_;
}
else
{
lean_object* v_val_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_val_1668_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_val_1668_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = lean_string_utf8_byte_size(v_val_1668_);
v___x_1671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1671_, 0, v_val_1668_);
lean_ctor_set(v___x_1671_, 1, v___x_1669_);
lean_ctor_set(v___x_1671_, 2, v___x_1670_);
v___x_1672_ = l_String_Slice_toNat_x3f(v___x_1671_);
lean_dec_ref_known(v___x_1671_, 3);
if (lean_obj_tag(v___x_1672_) == 0)
{
v___y_1660_ = v___x_1667_;
v___y_1661_ = v___y_1664_;
goto v___jp_1659_;
}
else
{
lean_object* v_val_1673_; 
lean_dec(v___y_1664_);
v_val_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_val_1673_);
lean_dec_ref_known(v___x_1672_, 1);
v___y_1660_ = v___x_1667_;
v___y_1661_ = v_val_1673_;
goto v___jp_1659_;
}
}
}
}
}
v___jp_1593_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1595_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1));
v___x_1596_ = lean_string_append(v___x_1595_, v_depsFile_1587_);
lean_dec_ref(v_depsFile_1587_);
v___x_1597_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2));
v___x_1598_ = lean_string_append(v___x_1596_, v___x_1597_);
v___x_1599_ = lean_string_append(v___x_1598_, v_a_1594_);
lean_dec_ref(v_a_1594_);
v___x_1600_ = lean_mk_io_user_error(v___x_1599_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set_tag(v___x_1591_, 1);
lean_ctor_set(v___x_1591_, 0, v___x_1600_);
v___x_1602_ = v___x_1591_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
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
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec_ref(v_depsFile_1587_);
lean_dec_ref(v_fname_1584_);
v_a_1676_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1588_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1588_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_0interp(lean_interpreter_value* stack)
{
lean_object* v_fname_1584_ = stack[0].m_obj;
lean_object* v_res_1684_;
v_res_1684_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_fname_1584_);
stack->m_obj
 = v_res_1684_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___boxed(lean_object* v_fname_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_fname_1685_);
return v_res_1687_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object* v_a_1688_, lean_object* v___y_1689_, lean_object* v_inst_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1688_, v___y_1689_, v_a_1691_);
return v___x_1693_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1688_ = stack[0].m_obj;
lean_object* v___y_1689_ = stack[1].m_obj;
lean_object* v_a_1691_ = stack[3].m_obj;
lean_object* v_res_1694_;
v_res_1694_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(v_a_1688_, v___y_1689_, lean_box(0), v_a_1691_);
stack->m_obj
 = v_res_1694_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object* v_a_1695_, lean_object* v___y_1696_, lean_object* v_inst_1697_, lean_object* v_a_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(v_a_1695_, v___y_1696_, v_inst_1697_, v_a_1698_);
lean_dec(v___y_1696_);
lean_dec_ref(v_a_1695_);
return v_res_1700_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object* v_upperBound_1701_, lean_object* v_a_1702_, lean_object* v___y_1703_, lean_object* v_inst_1704_, lean_object* v_R_1705_, lean_object* v_a_1706_, lean_object* v_b_1707_, lean_object* v_c_1708_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1701_, v_a_1702_, v___y_1703_, v_a_1706_, v_b_1707_);
return v___x_1710_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1701_ = stack[0].m_obj;
lean_object* v_a_1702_ = stack[1].m_obj;
lean_object* v___y_1703_ = stack[2].m_obj;
lean_object* v_a_1706_ = stack[5].m_obj;
lean_object* v_b_1707_ = stack[6].m_obj;
lean_object* v_res_1711_;
v_res_1711_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(v_upperBound_1701_, v_a_1702_, v___y_1703_, lean_box(0), lean_box(0), v_a_1706_, v_b_1707_, lean_box(0));
stack->m_obj
 = v_res_1711_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object* v_upperBound_1712_, lean_object* v_a_1713_, lean_object* v___y_1714_, lean_object* v_inst_1715_, lean_object* v_R_1716_, lean_object* v_a_1717_, lean_object* v_b_1718_, lean_object* v_c_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(v_upperBound_1712_, v_a_1713_, v___y_1714_, v_inst_1715_, v_R_1716_, v_a_1717_, v_b_1718_, v_c_1719_);
lean_dec(v_upperBound_1712_);
return v_res_1721_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object* v_as_1722_, size_t v_sz_1723_, size_t v_i_1724_, lean_object* v_b_1725_){
_start:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_usize_dec_lt(v_i_1724_, v_sz_1723_);
if (v___x_1727_ == 0)
{
return v_b_1725_;
}
else
{
lean_object* v_a_1728_; lean_object* v_cancelTk_x3f_1729_; lean_object* v___x_1730_; 
v_a_1728_ = lean_array_uget_borrowed(v_as_1722_, v_i_1724_);
v_cancelTk_x3f_1729_ = lean_ctor_get(v_a_1728_, 2);
v___x_1730_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_1729_) == 1)
{
lean_object* v_val_1737_; lean_object* v___x_1738_; 
v_val_1737_ = lean_ctor_get(v_cancelTk_x3f_1729_, 0);
v___x_1738_ = l_IO_CancelToken_set(v_val_1737_);
goto v___jp_1731_;
}
else
{
goto v___jp_1731_;
}
v___jp_1731_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; size_t v___x_1734_; size_t v___x_1735_; 
lean_inc(v_a_1728_);
v___x_1732_ = l_Lean_Language_SnapshotTask_get___redArg(v_a_1728_);
v___x_1733_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___x_1732_);
lean_dec(v___x_1732_);
v___x_1734_ = ((size_t)1ULL);
v___x_1735_ = lean_usize_add(v_i_1724_, v___x_1734_);
v_i_1724_ = v___x_1735_;
v_b_1725_ = v___x_1730_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1722_ = stack[0].m_obj;
size_t v_sz_1723_ = stack[1].m_num;
size_t v_i_1724_ = stack[2].m_num;
lean_object* v_b_1725_ = stack[3].m_obj;
lean_object* v_res_1739_;
v_res_1739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_as_1722_, v_sz_1723_, v_i_1724_, v_b_1725_);
stack->m_obj
 = v_res_1739_;
}
lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object* v_s_1740_){
_start:
{
lean_object* v_children_1742_; lean_object* v___x_1743_; size_t v_sz_1744_; size_t v___x_1745_; lean_object* v___x_1746_; 
v_children_1742_ = lean_ctor_get(v_s_1740_, 1);
v___x_1743_ = lean_box(0);
v_sz_1744_ = lean_array_size(v_children_1742_);
v___x_1745_ = ((size_t)0ULL);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_children_1742_, v_sz_1744_, v___x_1745_, v___x_1743_);
return v___x_1743_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1740_ = stack[0].m_obj;
lean_object* v_res_1747_;
v_res_1747_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v_s_1740_);
stack->m_obj
 = v_res_1747_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object* v_s_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v_s_1748_);
lean_dec_ref(v_s_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object* v_as_1751_, lean_object* v_sz_1752_, lean_object* v_i_1753_, lean_object* v_b_1754_, lean_object* v___y_1755_){
_start:
{
size_t v_sz_boxed_1756_; size_t v_i_boxed_1757_; lean_object* v_res_1758_; 
v_sz_boxed_1756_ = lean_unbox_usize(v_sz_1752_);
lean_dec(v_sz_1752_);
v_i_boxed_1757_ = lean_unbox_usize(v_i_1753_);
lean_dec(v_i_1753_);
v_res_1758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_as_1751_, v_sz_boxed_1756_, v_i_boxed_1757_, v_b_1754_);
lean_dec_ref(v_as_1751_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(lean_object* v_snap_1759_, lean_object* v_m_1760_){
_start:
{
lean_object* v_result_x3f_1761_; 
v_result_x3f_1761_ = lean_ctor_get(v_snap_1759_, 4);
lean_inc(v_result_x3f_1761_);
if (lean_obj_tag(v_result_x3f_1761_) == 1)
{
lean_object* v_val_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1862_; 
v_val_1762_ = lean_ctor_get(v_result_x3f_1761_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_result_x3f_1761_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1764_ = v_result_x3f_1761_;
v_isShared_1765_ = v_isSharedCheck_1862_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_val_1762_);
lean_dec(v_result_x3f_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1862_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v_toSnapshot_1766_; lean_object* v_metaSnap_1767_; lean_object* v_ictx_1768_; lean_object* v_stx_1769_; lean_object* v_parserState_1770_; lean_object* v_processedSnap_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1861_; 
v_toSnapshot_1766_ = lean_ctor_get(v_snap_1759_, 0);
v_metaSnap_1767_ = lean_ctor_get(v_snap_1759_, 1);
v_ictx_1768_ = lean_ctor_get(v_snap_1759_, 2);
v_stx_1769_ = lean_ctor_get(v_snap_1759_, 3);
v_parserState_1770_ = lean_ctor_get(v_val_1762_, 0);
v_processedSnap_1771_ = lean_ctor_get(v_val_1762_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_val_1762_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1773_ = v_val_1762_;
v_isShared_1774_ = v_isSharedCheck_1861_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_processedSnap_1771_);
lean_inc(v_parserState_1770_);
lean_dec(v_val_1762_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1861_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v_processed_1775_; lean_object* v_result_x3f_1776_; 
v_processed_1775_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_1771_);
v_result_x3f_1776_ = lean_ctor_get(v_processed_1775_, 2);
lean_inc(v_result_x3f_1776_);
if (lean_obj_tag(v_result_x3f_1776_) == 1)
{
lean_object* v_val_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1860_; 
v_val_1777_ = lean_ctor_get(v_result_x3f_1776_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_result_x3f_1776_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1779_ = v_result_x3f_1776_;
v_isShared_1780_ = v_isSharedCheck_1860_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_val_1777_);
lean_dec(v_result_x3f_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1860_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_cmdState_1781_; lean_object* v_toSnapshot_1782_; lean_object* v_metaSnap_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1858_; 
v_cmdState_1781_ = lean_ctor_get(v_val_1777_, 0);
lean_inc_ref(v_cmdState_1781_);
v_toSnapshot_1782_ = lean_ctor_get(v_processed_1775_, 0);
v_metaSnap_1783_ = lean_ctor_get(v_processed_1775_, 1);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_processed_1775_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v_processed_1775_, 2);
lean_dec(v_unused_1859_);
v___x_1785_ = v_processed_1775_;
v_isShared_1786_ = v_isSharedCheck_1858_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_metaSnap_1783_);
lean_inc(v_toSnapshot_1782_);
lean_dec(v_processed_1775_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1858_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v_firstCmdSnap_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1856_; 
v_firstCmdSnap_1787_ = lean_ctor_get(v_val_1777_, 1);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_val_1777_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v_val_1777_, 0);
lean_dec(v_unused_1857_);
v___x_1789_ = v_val_1777_;
v_isShared_1790_ = v_isSharedCheck_1856_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_firstCmdSnap_1787_);
lean_dec(v_val_1777_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1856_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_env_1791_; lean_object* v_messages_1792_; lean_object* v_scopes_1793_; lean_object* v_usedQuotCtxts_1794_; lean_object* v_nextMacroScope_1795_; lean_object* v_maxRecDepth_1796_; lean_object* v_ngen_1797_; lean_object* v_auxDeclNGen_1798_; lean_object* v_infoState_1799_; lean_object* v_traceState_1800_; lean_object* v_snapshotTasks_1801_; lean_object* v_prevLinterStates_1802_; lean_object* v_codeQualityEntryTasks_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1855_; 
v_env_1791_ = lean_ctor_get(v_cmdState_1781_, 0);
v_messages_1792_ = lean_ctor_get(v_cmdState_1781_, 1);
v_scopes_1793_ = lean_ctor_get(v_cmdState_1781_, 2);
v_usedQuotCtxts_1794_ = lean_ctor_get(v_cmdState_1781_, 3);
v_nextMacroScope_1795_ = lean_ctor_get(v_cmdState_1781_, 4);
v_maxRecDepth_1796_ = lean_ctor_get(v_cmdState_1781_, 5);
v_ngen_1797_ = lean_ctor_get(v_cmdState_1781_, 6);
v_auxDeclNGen_1798_ = lean_ctor_get(v_cmdState_1781_, 7);
v_infoState_1799_ = lean_ctor_get(v_cmdState_1781_, 8);
v_traceState_1800_ = lean_ctor_get(v_cmdState_1781_, 9);
v_snapshotTasks_1801_ = lean_ctor_get(v_cmdState_1781_, 10);
v_prevLinterStates_1802_ = lean_ctor_get(v_cmdState_1781_, 11);
v_codeQualityEntryTasks_1803_ = lean_ctor_get(v_cmdState_1781_, 12);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_cmdState_1781_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1805_ = v_cmdState_1781_;
v_isShared_1806_ = v_isSharedCheck_1855_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1803_);
lean_inc(v_prevLinterStates_1802_);
lean_inc(v_snapshotTasks_1801_);
lean_inc(v_traceState_1800_);
lean_inc(v_infoState_1799_);
lean_inc(v_auxDeclNGen_1798_);
lean_inc(v_ngen_1797_);
lean_inc(v_maxRecDepth_1796_);
lean_inc(v_nextMacroScope_1795_);
lean_inc(v_usedQuotCtxts_1794_);
lean_inc(v_scopes_1793_);
lean_inc(v_messages_1792_);
lean_inc(v_env_1791_);
lean_dec(v_cmdState_1781_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1855_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v_mainModule_1808_; uint8_t v___x_1809_; 
v___x_1807_ = l_Lean_Environment_header(v_env_1791_);
v_mainModule_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_mainModule_1808_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = lean_name_eq(v_mainModule_1808_, v_m_1760_);
lean_dec(v_mainModule_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1849_; 
lean_inc(v_stx_1769_);
lean_inc_ref(v_ictx_1768_);
lean_inc_ref(v_metaSnap_1767_);
lean_inc_ref(v_toSnapshot_1766_);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_snap_1759_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; lean_object* v_unused_1851_; lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; 
v_unused_1850_ = lean_ctor_get(v_snap_1759_, 4);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_snap_1759_, 3);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_snap_1759_, 2);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v_snap_1759_, 1);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_snap_1759_, 0);
lean_dec(v_unused_1854_);
v___x_1811_ = v_snap_1759_;
v_isShared_1812_ = v_isSharedCheck_1849_;
goto v_resetjp_1810_;
}
else
{
lean_dec(v_snap_1759_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1849_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_idx_1813_; lean_object* v_parentIdxs_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1847_; 
v_idx_1813_ = lean_ctor_get(v_auxDeclNGen_1798_, 1);
v_parentIdxs_1814_ = lean_ctor_get(v_auxDeclNGen_1798_, 2);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_auxDeclNGen_1798_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v_auxDeclNGen_1798_, 0);
lean_dec(v_unused_1848_);
v___x_1816_ = v_auxDeclNGen_1798_;
v_isShared_1817_ = v_isSharedCheck_1847_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_parentIdxs_1814_);
lean_inc(v_idx_1813_);
lean_dec(v_auxDeclNGen_1798_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1847_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v_newEnv_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v_newEnv_1818_ = l_Lean_Environment_setMainModule(v_env_1791_, v_m_1760_);
v___x_1819_ = lean_box(0);
v___x_1820_ = l_Lean_mkPrivateName(v_newEnv_1818_, v___x_1819_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1820_);
v___x_1822_ = v___x_1816_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_idx_1813_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_parentIdxs_1814_);
v___x_1822_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v_newCmdState_1824_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 7, v___x_1822_);
lean_ctor_set(v___x_1805_, 0, v_newEnv_1818_);
v_newCmdState_1824_ = v___x_1805_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_newEnv_1818_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_messages_1792_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v_scopes_1793_);
lean_ctor_set(v_reuseFailAlloc_1845_, 3, v_usedQuotCtxts_1794_);
lean_ctor_set(v_reuseFailAlloc_1845_, 4, v_nextMacroScope_1795_);
lean_ctor_set(v_reuseFailAlloc_1845_, 5, v_maxRecDepth_1796_);
lean_ctor_set(v_reuseFailAlloc_1845_, 6, v_ngen_1797_);
lean_ctor_set(v_reuseFailAlloc_1845_, 7, v___x_1822_);
lean_ctor_set(v_reuseFailAlloc_1845_, 8, v_infoState_1799_);
lean_ctor_set(v_reuseFailAlloc_1845_, 9, v_traceState_1800_);
lean_ctor_set(v_reuseFailAlloc_1845_, 10, v_snapshotTasks_1801_);
lean_ctor_set(v_reuseFailAlloc_1845_, 11, v_prevLinterStates_1802_);
lean_ctor_set(v_reuseFailAlloc_1845_, 12, v_codeQualityEntryTasks_1803_);
v_newCmdState_1824_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v_newCmdState_1824_);
v___x_1826_ = v___x_1789_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_newCmdState_1824_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_firstCmdSnap_1787_);
v___x_1826_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1828_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1826_);
v___x_1828_ = v___x_1779_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v_newProcessed_1830_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 2, v___x_1828_);
v_newProcessed_1830_ = v___x_1785_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_toSnapshot_1782_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_metaSnap_1783_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v___x_1828_);
v_newProcessed_1830_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1831_ = lean_box(0);
v___x_1832_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1831_, v_newProcessed_1830_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v___x_1832_);
v___x_1834_ = v___x_1773_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_parserState_1770_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1836_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1834_);
v___x_1836_ = v___x_1764_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1838_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 4, v___x_1836_);
v___x_1838_ = v___x_1811_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_toSnapshot_1766_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_metaSnap_1767_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v_ictx_1768_);
lean_ctor_set(v_reuseFailAlloc_1839_, 3, v_stx_1769_);
lean_ctor_set(v_reuseFailAlloc_1839_, 4, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
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
lean_del_object(v___x_1805_);
lean_dec_ref(v_codeQualityEntryTasks_1803_);
lean_dec(v_prevLinterStates_1802_);
lean_dec_ref(v_snapshotTasks_1801_);
lean_dec_ref(v_traceState_1800_);
lean_dec_ref(v_infoState_1799_);
lean_dec_ref(v_auxDeclNGen_1798_);
lean_dec_ref(v_ngen_1797_);
lean_dec(v_maxRecDepth_1796_);
lean_dec(v_nextMacroScope_1795_);
lean_dec(v_usedQuotCtxts_1794_);
lean_dec(v_scopes_1793_);
lean_dec_ref(v_messages_1792_);
lean_dec_ref(v_env_1791_);
lean_del_object(v___x_1789_);
lean_dec_ref(v_firstCmdSnap_1787_);
lean_del_object(v___x_1785_);
lean_dec_ref(v_metaSnap_1783_);
lean_dec_ref(v_toSnapshot_1782_);
lean_del_object(v___x_1779_);
lean_del_object(v___x_1773_);
lean_dec_ref(v_parserState_1770_);
lean_del_object(v___x_1764_);
lean_dec(v_m_1760_);
return v_snap_1759_;
}
}
}
}
}
}
else
{
lean_dec(v_result_x3f_1776_);
lean_dec(v_processed_1775_);
lean_del_object(v___x_1773_);
lean_dec_ref(v_parserState_1770_);
lean_del_object(v___x_1764_);
lean_dec(v_m_1760_);
return v_snap_1759_;
}
}
}
}
else
{
lean_dec(v_result_x3f_1761_);
lean_dec(v_m_1760_);
return v_snap_1759_;
}
}
}
lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object* v_incrFile_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_incrFile_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_incrFile_1863_ = stack[0].m_obj;
lean_object* v_res_1866_;
v_res_1866_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(v_incrFile_1863_);
stack->m_obj
 = v_res_1866_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object* v_incrFile_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(v_incrFile_1867_);
return v_res_1869_;
}
}
lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object* v_opts_1870_, lean_object* v_incr_1871_, lean_object* v_res_1872_){
_start:
{
lean_object* v_cmdState_1874_; lean_object* v_env_1875_; lean_object* v_initModIdxs_1876_; lean_object* v___x_1877_; 
v_cmdState_1874_ = lean_ctor_get(v_res_1872_, 0);
lean_inc_ref(v_cmdState_1874_);
lean_dec_ref(v_res_1872_);
v_env_1875_ = lean_ctor_get(v_cmdState_1874_, 0);
lean_inc_ref(v_env_1875_);
lean_dec_ref(v_cmdState_1874_);
v_initModIdxs_1876_ = lean_ctor_get(v_incr_1871_, 1);
v___x_1877_ = l_Lean_runInitAttrsForModules(v_env_1875_, v_initModIdxs_1876_, v_opts_1870_);
return v___x_1877_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1870_ = stack[0].m_obj;
lean_object* v_incr_1871_ = stack[1].m_obj;
lean_object* v_res_1872_ = stack[2].m_obj;
lean_object* v_res_1878_;
v_res_1878_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(v_opts_1870_, v_incr_1871_, v_res_1872_);
stack->m_obj
 = v_res_1878_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object* v_opts_1879_, lean_object* v_incr_1880_, lean_object* v_res_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(v_opts_1879_, v_incr_1880_, v_res_1881_);
lean_dec_ref(v_incr_1880_);
return v_res_1883_;
}
}
lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7(){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_enable_initializer_execution();
return v___x_1885_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1886_;
v_res_1886_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
stack->m_obj
 = v_res_1886_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object* v_a_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
return v_res_1888_;
}
}
lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(lean_object* v_env_1892_, lean_object* v_incrFile_1893_, lean_object* v_toSave_1894_){
_start:
{
lean_object* v___x_1896_; lean_object* v_regions_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; lean_object* v___x_1901_; 
v___x_1896_ = l_Lean_Environment_header(v_env_1892_);
v_regions_1897_ = lean_ctor_get(v___x_1896_, 2);
lean_inc_ref(v_regions_1897_);
lean_dec_ref(v___x_1896_);
v___x_1898_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1899_ = lean_box(0);
v___x_1900_ = 1;
v___x_1901_ = lean_compacted_region_save(v_incrFile_1893_, v___x_1898_, v_toSave_1894_, v_regions_1897_, v___x_1899_, v___x_1900_);
lean_dec_ref(v_regions_1897_);
return v___x_1901_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1892_ = stack[0].m_obj;
lean_object* v_incrFile_1893_ = stack[1].m_obj;
lean_object* v_toSave_1894_ = stack[2].m_obj;
lean_object* v_res_1902_;
v_res_1902_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(v_env_1892_, v_incrFile_1893_, v_toSave_1894_);
stack->m_obj
 = v_res_1902_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___boxed(lean_object* v_env_1903_, lean_object* v_incrFile_1904_, lean_object* v_toSave_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(v_env_1903_, v_incrFile_1904_, v_toSave_1905_);
lean_dec_ref(v_toSave_1905_);
lean_dec_ref(v_incrFile_1904_);
lean_dec_ref(v_env_1903_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_opts_1908_, lean_object* v_opt_1909_){
_start:
{
lean_object* v_name_1910_; lean_object* v_map_1911_; lean_object* v___x_1912_; 
v_name_1910_ = lean_ctor_get(v_opt_1909_, 0);
v_map_1911_ = lean_ctor_get(v_opts_1908_, 0);
v___x_1912_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1911_, v_name_1910_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_box(0);
return v___x_1913_;
}
else
{
lean_object* v_val_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1923_; 
v_val_1914_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1916_ = v___x_1912_;
v_isShared_1917_ = v_isSharedCheck_1923_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_val_1914_);
lean_dec(v___x_1912_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1923_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
if (lean_obj_tag(v_val_1914_) == 0)
{
lean_object* v_v_1918_; lean_object* v___x_1920_; 
v_v_1918_ = lean_ctor_get(v_val_1914_, 0);
lean_inc_ref(v_v_1918_);
lean_dec_ref_known(v_val_1914_, 1);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v_v_1918_);
v___x_1920_ = v___x_1916_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_v_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
else
{
lean_object* v___x_1922_; 
lean_del_object(v___x_1916_);
lean_dec(v_val_1914_);
v___x_1922_ = lean_box(0);
return v___x_1922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_opts_1924_, lean_object* v_opt_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v_opts_1924_, v_opt_1925_);
lean_dec_ref(v_opt_1925_);
lean_dec_ref(v_opts_1924_);
return v_res_1926_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_opts_1927_, lean_object* v_opt_1928_){
_start:
{
lean_object* v_name_1929_; lean_object* v_defValue_1930_; lean_object* v_map_1931_; lean_object* v___x_1932_; 
v_name_1929_ = lean_ctor_get(v_opt_1928_, 0);
v_defValue_1930_ = lean_ctor_get(v_opt_1928_, 1);
v_map_1931_ = lean_ctor_get(v_opts_1927_, 0);
v___x_1932_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1931_, v_name_1929_);
if (lean_obj_tag(v___x_1932_) == 0)
{
uint8_t v___x_1933_; 
v___x_1933_ = lean_unbox(v_defValue_1930_);
return v___x_1933_;
}
else
{
lean_object* v_val_1934_; 
v_val_1934_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_val_1934_);
lean_dec_ref_known(v___x_1932_, 1);
if (lean_obj_tag(v_val_1934_) == 1)
{
uint8_t v_v_1935_; 
v_v_1935_ = lean_ctor_get_uint8(v_val_1934_, 0);
lean_dec_ref_known(v_val_1934_, 0);
return v_v_1935_;
}
else
{
uint8_t v___x_1936_; 
lean_dec(v_val_1934_);
v___x_1936_ = lean_unbox(v_defValue_1930_);
return v___x_1936_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1927_ = stack[0].m_obj;
lean_object* v_opt_1928_ = stack[1].m_obj;
uint8_t v_res_1937_;
v_res_1937_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1927_, v_opt_1928_);
stack->m_num = v_res_1937_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_opts_1938_, lean_object* v_opt_1939_){
_start:
{
uint8_t v_res_1940_; lean_object* v_r_1941_; 
v_res_1940_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1938_, v_opt_1939_);
lean_dec_ref(v_opt_1939_);
lean_dec_ref(v_opts_1938_);
v_r_1941_ = lean_box(v_res_1940_);
return v_r_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_1942_, lean_object* v_x_1943_, lean_object* v_hOpt_1944_){
_start:
{
lean_inc_ref(v_hOpt_1944_);
return v_hOpt_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_1945_, lean_object* v_x_1946_, lean_object* v_hOpt_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_Elab_runFrontend___lam__0(v_x_1945_, v_x_1946_, v_hOpt_1947_);
lean_dec_ref(v_hOpt_1947_);
lean_dec_ref(v_x_1946_);
lean_dec(v_x_1945_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_x1_1949_, lean_object* v_x2_1950_){
_start:
{
lean_object* v_elabSnap_1951_; lean_object* v_resultSnap_1952_; lean_object* v___x_1953_; lean_object* v_codeQualityEntryTasks_1954_; lean_object* v___x_1955_; 
v_elabSnap_1951_ = lean_ctor_get(v_x2_1950_, 3);
lean_inc_ref(v_elabSnap_1951_);
lean_dec_ref(v_x2_1950_);
v_resultSnap_1952_ = lean_ctor_get(v_elabSnap_1951_, 2);
lean_inc_ref(v_resultSnap_1952_);
lean_dec_ref(v_elabSnap_1951_);
v___x_1953_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_1952_);
v_codeQualityEntryTasks_1954_ = lean_ctor_get(v___x_1953_, 2);
lean_inc_ref(v_codeQualityEntryTasks_1954_);
lean_dec(v___x_1953_);
v___x_1955_ = l_Array_append___redArg(v_x1_1949_, v_codeQualityEntryTasks_1954_);
lean_dec_ref(v_codeQualityEntryTasks_1954_);
return v___x_1955_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(size_t v_sz_1956_, size_t v_i_1957_, lean_object* v_bs_1958_){
_start:
{
uint8_t v___x_1959_; 
v___x_1959_ = lean_usize_dec_lt(v_i_1957_, v_sz_1956_);
if (v___x_1959_ == 0)
{
return v_bs_1958_;
}
else
{
lean_object* v_v_1960_; lean_object* v___x_1961_; lean_object* v_bs_x27_1962_; lean_object* v___x_1963_; size_t v___x_1964_; size_t v___x_1965_; lean_object* v___x_1966_; 
v_v_1960_ = lean_array_uget(v_bs_1958_, v_i_1957_);
v___x_1961_ = lean_unsigned_to_nat(0u);
v_bs_x27_1962_ = lean_array_uset(v_bs_1958_, v_i_1957_, v___x_1961_);
v___x_1963_ = l_Lean_instToJsonModuleArtifacts_toJson(v_v_1960_);
v___x_1964_ = ((size_t)1ULL);
v___x_1965_ = lean_usize_add(v_i_1957_, v___x_1964_);
v___x_1966_ = lean_array_uset(v_bs_x27_1962_, v_i_1957_, v___x_1963_);
v_i_1957_ = v___x_1965_;
v_bs_1958_ = v___x_1966_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1956_ = stack[0].m_num;
size_t v_i_1957_ = stack[1].m_num;
lean_object* v_bs_1958_ = stack[2].m_obj;
lean_object* v_res_1968_;
v_res_1968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(v_sz_1956_, v_i_1957_, v_bs_1958_);
stack->m_obj
 = v_res_1968_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11___boxed(lean_object* v_sz_1969_, lean_object* v_i_1970_, lean_object* v_bs_1971_){
_start:
{
size_t v_sz_boxed_1972_; size_t v_i_boxed_1973_; lean_object* v_res_1974_; 
v_sz_boxed_1972_ = lean_unbox_usize(v_sz_1969_);
lean_dec(v_sz_1969_);
v_i_boxed_1973_ = lean_unbox_usize(v_i_1970_);
lean_dec(v_i_1970_);
v_res_1974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(v_sz_boxed_1972_, v_i_boxed_1973_, v_bs_1971_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8(lean_object* v_a_1975_){
_start:
{
size_t v_sz_1976_; size_t v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_sz_1976_ = lean_array_size(v_a_1975_);
v___x_1977_ = ((size_t)0ULL);
v___x_1978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(v_sz_1976_, v___x_1977_, v_a_1975_);
v___x_1979_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
return v___x_1979_;
}
}
lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_a_1980_, uint8_t v___x_1981_, lean_object* v_incrFile_1982_, lean_object* v_snapToSave_1983_){
_start:
{
lean_object* v___x_1985_; lean_object* v_regions_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1985_ = l_Lean_Environment_header(v_a_1980_);
v_regions_1986_ = lean_ctor_get(v___x_1985_, 2);
lean_inc_ref(v_regions_1986_);
lean_dec_ref(v___x_1985_);
v___x_1987_ = l_Lean_getRegularInitAttrModIdxs(v_a_1980_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v_snapToSave_1983_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1990_ = lean_box(0);
v___x_1991_ = lean_compacted_region_save(v_incrFile_1982_, v___x_1989_, v___x_1988_, v_regions_1986_, v___x_1990_, v___x_1981_);
lean_dec_ref_known(v___x_1988_, 2);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___x_1993_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1986_);
lean_dec_ref(v_regions_1986_);
v___x_1994_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
v___x_1995_ = l_System_FilePath_addExtension(v_incrFile_1982_, v___x_1994_);
v___x_1996_ = l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8(v___x_1993_);
v___x_1997_ = l_Lean_Json_compress(v___x_1996_);
v___x_1998_ = l_IO_FS_writeFile(v___x_1995_, v___x_1997_);
lean_dec_ref(v___x_1997_);
lean_dec_ref(v___x_1995_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2006_; 
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; 
v_unused_2007_ = lean_ctor_get(v___x_1998_, 0);
lean_dec(v_unused_2007_);
v___x_2000_ = v___x_1998_;
v_isShared_2001_ = v_isSharedCheck_2006_;
goto v_resetjp_1999_;
}
else
{
lean_dec(v___x_1998_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2006_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2002_ = lean_runtime_forget(v_a_1992_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2002_);
v___x_2004_ = v___x_2000_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
else
{
lean_dec(v_a_1992_);
return v___x_1998_;
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref(v_regions_1986_);
lean_dec_ref(v_incrFile_1982_);
v_a_2008_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1991_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1991_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_runFrontend___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1980_ = stack[0].m_obj;
uint8_t v___x_1981_ = stack[1].m_num;
lean_object* v_incrFile_1982_ = stack[2].m_obj;
lean_object* v_snapToSave_1983_ = stack[3].m_obj;
lean_object* v_res_2016_;
v_res_2016_ = l_Lean_Elab_runFrontend___lam__2(v_a_1980_, v___x_1981_, v_incrFile_1982_, v_snapToSave_1983_);
stack->m_obj
 = v_res_2016_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object* v_a_2017_, lean_object* v___x_2018_, lean_object* v_incrFile_2019_, lean_object* v_snapToSave_2020_, lean_object* v___y_2021_){
_start:
{
uint8_t v___x_6141__boxed_2022_; lean_object* v_res_2023_; 
v___x_6141__boxed_2022_ = lean_unbox(v___x_2018_);
v_res_2023_ = l_Lean_Elab_runFrontend___lam__2(v_a_2017_, v___x_6141__boxed_2022_, v_incrFile_2019_, v_snapToSave_2020_);
lean_dec_ref(v_a_2017_);
return v_res_2023_;
}
}
lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_fileMap_2024_, lean_object* v_a_2025_, lean_object* v___x_2026_, lean_object* v_opts_2027_, lean_object* v_val_2028_, uint8_t v___x_2029_, uint8_t v_a_2030_){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2032_ = l_Lean_Linter_recordLints(v_fileMap_2024_, v_a_2025_, v___x_2026_);
v___x_2033_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2034_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_2027_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_writeModule(v___x_2032_, v_val_2028_, v___x_2029_);
return v___x_2035_;
}
else
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_writeModule(v___x_2032_, v_val_2028_, v_a_2030_);
return v___x_2036_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_runFrontend___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fileMap_2024_ = stack[0].m_obj;
lean_object* v_a_2025_ = stack[1].m_obj;
lean_object* v___x_2026_ = stack[2].m_obj;
lean_object* v_opts_2027_ = stack[3].m_obj;
lean_object* v_val_2028_ = stack[4].m_obj;
uint8_t v___x_2029_ = stack[5].m_num;
uint8_t v_a_2030_ = stack[6].m_num;
lean_object* v_res_2037_;
v_res_2037_ = l_Lean_Elab_runFrontend___lam__3(v_fileMap_2024_, v_a_2025_, v___x_2026_, v_opts_2027_, v_val_2028_, v___x_2029_, v_a_2030_);
stack->m_obj
 = v_res_2037_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_fileMap_2038_, lean_object* v_a_2039_, lean_object* v___x_2040_, lean_object* v_opts_2041_, lean_object* v_val_2042_, lean_object* v___x_2043_, lean_object* v_a_2044_, lean_object* v___y_2045_){
_start:
{
uint8_t v___x_6251__boxed_2046_; uint8_t v_a_6252__boxed_2047_; lean_object* v_res_2048_; 
v___x_6251__boxed_2046_ = lean_unbox(v___x_2043_);
v_a_6252__boxed_2047_ = lean_unbox(v_a_2044_);
v_res_2048_ = l_Lean_Elab_runFrontend___lam__3(v_fileMap_2038_, v_a_2039_, v___x_2040_, v_opts_2041_, v_val_2042_, v___x_6251__boxed_2046_, v_a_6252__boxed_2047_);
lean_dec_ref(v_opts_2041_);
lean_dec_ref(v___x_2040_);
lean_dec_ref(v_fileMap_2038_);
return v_res_2048_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_2049_, size_t v_i_2050_, size_t v_stop_2051_, lean_object* v_b_2052_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2049_ = stack[0].m_obj;
size_t v_i_2050_ = stack[1].m_num;
size_t v_stop_2051_ = stack[2].m_num;
lean_object* v_b_2052_ = stack[3].m_obj;
lean_object* v_res_2062_;
v_res_2062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_2049_, v_i_2050_, v_stop_2051_, v_b_2052_);
stack->m_obj
 = v_res_2062_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_2063_, lean_object* v_i_2064_, lean_object* v_stop_2065_, lean_object* v_b_2066_, lean_object* v___y_2067_){
_start:
{
size_t v_i_boxed_2068_; size_t v_stop_boxed_2069_; lean_object* v_res_2070_; 
v_i_boxed_2068_ = lean_unbox_usize(v_i_2064_);
lean_dec(v_i_2064_);
v_stop_boxed_2069_ = lean_unbox_usize(v_stop_2065_);
lean_dec(v_stop_2065_);
v_res_2070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_2063_, v_i_boxed_2068_, v_stop_boxed_2069_, v_b_2066_);
lean_dec_ref(v_as_2063_);
return v_res_2070_;
}
}
lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* v_setup_x3f_2071_, lean_object* v___f_2072_, lean_object* v___x_2073_, lean_object* v_plugins_2074_, uint32_t v_trustLevel_2075_, uint8_t v___x_2076_, lean_object* v_mainModuleName_2077_, lean_object* v_stx_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; uint8_t v___y_2087_; lean_object* v___y_2088_; 
if (lean_obj_tag(v_setup_x3f_2071_) == 1)
{
lean_object* v_val_2095_; lean_object* v_name_2096_; lean_object* v_package_x3f_2097_; uint8_t v_isModule_2098_; lean_object* v_imports_x3f_2099_; lean_object* v_importArts_2100_; lean_object* v_dynlibs_2101_; lean_object* v_plugins_2102_; lean_object* v_options_2103_; lean_object* v___y_2110_; lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
lean_dec(v_mainModuleName_2077_);
v_val_2095_ = lean_ctor_get(v_setup_x3f_2071_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v_setup_x3f_2071_, 1);
v_name_2096_ = lean_ctor_get(v_val_2095_, 0);
lean_inc(v_name_2096_);
v_package_x3f_2097_ = lean_ctor_get(v_val_2095_, 1);
lean_inc(v_package_x3f_2097_);
v_isModule_2098_ = lean_ctor_get_uint8(v_val_2095_, sizeof(void*)*7);
v_imports_x3f_2099_ = lean_ctor_get(v_val_2095_, 2);
lean_inc(v_imports_x3f_2099_);
v_importArts_2100_ = lean_ctor_get(v_val_2095_, 3);
lean_inc(v_importArts_2100_);
v_dynlibs_2101_ = lean_ctor_get(v_val_2095_, 4);
lean_inc_ref(v_dynlibs_2101_);
v_plugins_2102_ = lean_ctor_get(v_val_2095_, 5);
lean_inc_ref(v_plugins_2102_);
v_options_2103_ = lean_ctor_get(v_val_2095_, 6);
lean_inc(v_options_2103_);
lean_dec(v_val_2095_);
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = lean_array_get_size(v_dynlibs_2101_);
v___x_2121_ = lean_nat_dec_lt(v___x_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_dec_ref(v_dynlibs_2101_);
goto v___jp_2104_;
}
else
{
lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = lean_box(0);
v___x_2123_ = lean_nat_dec_le(v___x_2120_, v___x_2120_);
if (v___x_2123_ == 0)
{
if (v___x_2121_ == 0)
{
lean_dec_ref(v_dynlibs_2101_);
goto v___jp_2104_;
}
else
{
size_t v___x_2124_; size_t v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = ((size_t)0ULL);
v___x_2125_ = lean_usize_of_nat(v___x_2120_);
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2101_, v___x_2124_, v___x_2125_, v___x_2122_);
lean_dec_ref(v_dynlibs_2101_);
v___y_2110_ = v___x_2126_;
goto v___jp_2109_;
}
}
else
{
size_t v___x_2127_; size_t v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = ((size_t)0ULL);
v___x_2128_ = lean_usize_of_nat(v___x_2120_);
v___x_2129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2101_, v___x_2127_, v___x_2128_, v___x_2122_);
lean_dec_ref(v_dynlibs_2101_);
v___y_2110_ = v___x_2129_;
goto v___jp_2109_;
}
}
v___jp_2104_:
{
uint8_t v___x_2105_; uint8_t v___x_2106_; 
v___x_2105_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2078_);
v___x_2106_ = lean_strict_or(v_isModule_2098_, v___x_2105_);
if (lean_obj_tag(v_imports_x3f_2099_) == 0)
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2078_, v___x_2076_);
v___y_2082_ = v_options_2103_;
v___y_2083_ = v_package_x3f_2097_;
v___y_2084_ = v_importArts_2100_;
v___y_2085_ = v_name_2096_;
v___y_2086_ = v_plugins_2102_;
v___y_2087_ = v___x_2106_;
v___y_2088_ = v___x_2107_;
goto v___jp_2081_;
}
else
{
lean_object* v_val_2108_; 
lean_dec(v_stx_2078_);
v_val_2108_ = lean_ctor_get(v_imports_x3f_2099_, 0);
lean_inc(v_val_2108_);
lean_dec_ref_known(v_imports_x3f_2099_, 1);
v___y_2082_ = v_options_2103_;
v___y_2083_ = v_package_x3f_2097_;
v___y_2084_ = v_importArts_2100_;
v___y_2085_ = v_name_2096_;
v___y_2086_ = v_plugins_2102_;
v___y_2087_ = v___x_2106_;
v___y_2088_ = v_val_2108_;
goto v___jp_2081_;
}
}
v___jp_2109_:
{
if (lean_obj_tag(v___y_2110_) == 0)
{
lean_dec_ref_known(v___y_2110_, 1);
goto v___jp_2104_;
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v_options_2103_);
lean_dec_ref(v_plugins_2102_);
lean_dec(v_importArts_2100_);
lean_dec(v_imports_x3f_2099_);
lean_dec(v_package_x3f_2097_);
lean_dec(v_name_2096_);
lean_dec(v_stx_2078_);
lean_dec_ref(v_plugins_2074_);
lean_dec_ref(v___x_2073_);
lean_dec_ref(v___f_2072_);
v_a_2111_ = lean_ctor_get(v___y_2110_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___y_2110_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___y_2110_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___y_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
else
{
lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec_ref(v___f_2072_);
lean_dec(v_setup_x3f_2071_);
v___x_2130_ = lean_box(0);
v___x_2131_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2078_);
v___x_2132_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2078_, v___x_2076_);
v___x_2133_ = lean_box(1);
v___x_2134_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2134_, 0, v_mainModuleName_2077_);
lean_ctor_set(v___x_2134_, 1, v___x_2130_);
lean_ctor_set(v___x_2134_, 2, v___x_2132_);
lean_ctor_set(v___x_2134_, 3, v___x_2073_);
lean_ctor_set(v___x_2134_, 4, v___x_2133_);
lean_ctor_set(v___x_2134_, 5, v_plugins_2074_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*6 + 4, v___x_2131_);
lean_ctor_set_uint32(v___x_2134_, sizeof(void*)*6, v_trustLevel_2075_);
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
return v___x_2136_;
}
v___jp_2081_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2089_ = l_Lean_LeanOptions_toOptions(v___y_2082_);
v___x_2090_ = l_Lean_Options_mergeBy(v___f_2072_, v___x_2073_, v___x_2089_);
v___x_2091_ = l_Array_append___redArg(v_plugins_2074_, v___y_2086_);
lean_dec_ref(v___y_2086_);
v___x_2092_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2092_, 0, v___y_2085_);
lean_ctor_set(v___x_2092_, 1, v___y_2083_);
lean_ctor_set(v___x_2092_, 2, v___y_2088_);
lean_ctor_set(v___x_2092_, 3, v___x_2090_);
lean_ctor_set(v___x_2092_, 4, v___y_2084_);
lean_ctor_set(v___x_2092_, 5, v___x_2091_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*6 + 4, v___y_2087_);
lean_ctor_set_uint32(v___x_2092_, sizeof(void*)*6, v_trustLevel_2075_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
return v___x_2094_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_runFrontend___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_setup_x3f_2071_ = stack[0].m_obj;
lean_object* v___f_2072_ = stack[1].m_obj;
lean_object* v___x_2073_ = stack[2].m_obj;
lean_object* v_plugins_2074_ = stack[3].m_obj;
uint32_t v_trustLevel_2075_ = stack[4].m_num;
uint8_t v___x_2076_ = stack[5].m_num;
lean_object* v_mainModuleName_2077_ = stack[6].m_obj;
lean_object* v_stx_2078_ = stack[7].m_obj;
lean_object* v___y_2079_ = stack[8].m_obj;
lean_object* v_res_2137_;
v_res_2137_ = l_Lean_Elab_runFrontend___lam__4(v_setup_x3f_2071_, v___f_2072_, v___x_2073_, v_plugins_2074_, v_trustLevel_2075_, v___x_2076_, v_mainModuleName_2077_, v_stx_2078_, v___y_2079_);
stack->m_obj
 = v_res_2137_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object* v_setup_x3f_2138_, lean_object* v___f_2139_, lean_object* v___x_2140_, lean_object* v_plugins_2141_, lean_object* v_trustLevel_2142_, lean_object* v___x_2143_, lean_object* v_mainModuleName_2144_, lean_object* v_stx_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
uint32_t v_trustLevel_boxed_2148_; uint8_t v___x_6325__boxed_2149_; lean_object* v_res_2150_; 
v_trustLevel_boxed_2148_ = lean_unbox_uint32(v_trustLevel_2142_);
lean_dec(v_trustLevel_2142_);
v___x_6325__boxed_2149_ = lean_unbox(v___x_2143_);
v_res_2150_ = l_Lean_Elab_runFrontend___lam__4(v_setup_x3f_2138_, v___f_2139_, v___x_2140_, v_plugins_2141_, v_trustLevel_boxed_2148_, v___x_6325__boxed_2149_, v_mainModuleName_2144_, v_stx_2145_, v___y_2146_);
lean_dec_ref(v___y_2146_);
return v_res_2150_;
}
}
lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object* v_val_2151_, lean_object* v_initModIdxs_2152_, lean_object* v___x_2153_){
_start:
{
lean_object* v_cmdState_2155_; lean_object* v_env_2156_; lean_object* v___x_2157_; 
v_cmdState_2155_ = lean_ctor_get(v_val_2151_, 0);
lean_inc_ref(v_cmdState_2155_);
lean_dec_ref(v_val_2151_);
v_env_2156_ = lean_ctor_get(v_cmdState_2155_, 0);
lean_inc_ref(v_env_2156_);
lean_dec_ref(v_cmdState_2155_);
v___x_2157_ = l_Lean_runInitAttrsForModules(v_env_2156_, v_initModIdxs_2152_, v___x_2153_);
return v___x_2157_;
}
}
LEAN_EXPORT void l_Lean_Elab_runFrontend___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2151_ = stack[0].m_obj;
lean_object* v_initModIdxs_2152_ = stack[1].m_obj;
lean_object* v___x_2153_ = stack[2].m_obj;
lean_object* v_res_2158_;
v_res_2158_ = l_Lean_Elab_runFrontend___lam__5(v_val_2151_, v_initModIdxs_2152_, v___x_2153_);
stack->m_obj
 = v_res_2158_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5___boxed(lean_object* v_val_2159_, lean_object* v_initModIdxs_2160_, lean_object* v___x_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_Elab_runFrontend___lam__5(v_val_2159_, v_initModIdxs_2160_, v___x_2161_);
lean_dec_ref(v_initModIdxs_2160_);
return v_res_2163_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(size_t v_sz_2164_, size_t v_i_2165_, lean_object* v_bs_2166_){
_start:
{
uint8_t v___x_2167_; 
v___x_2167_ = lean_usize_dec_lt(v_i_2165_, v_sz_2164_);
if (v___x_2167_ == 0)
{
return v_bs_2166_;
}
else
{
lean_object* v_v_2168_; lean_object* v_traces_2169_; lean_object* v___x_2170_; lean_object* v_bs_x27_2171_; size_t v___x_2172_; size_t v___x_2173_; lean_object* v___x_2174_; 
v_v_2168_ = lean_array_uget_borrowed(v_bs_2166_, v_i_2165_);
v_traces_2169_ = lean_ctor_get(v_v_2168_, 3);
lean_inc_ref(v_traces_2169_);
v___x_2170_ = lean_unsigned_to_nat(0u);
v_bs_x27_2171_ = lean_array_uset(v_bs_2166_, v_i_2165_, v___x_2170_);
v___x_2172_ = ((size_t)1ULL);
v___x_2173_ = lean_usize_add(v_i_2165_, v___x_2172_);
v___x_2174_ = lean_array_uset(v_bs_x27_2171_, v_i_2165_, v_traces_2169_);
v_i_2165_ = v___x_2173_;
v_bs_2166_ = v___x_2174_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2164_ = stack[0].m_num;
size_t v_i_2165_ = stack[1].m_num;
lean_object* v_bs_2166_ = stack[2].m_obj;
lean_object* v_res_2176_;
v_res_2176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2164_, v_i_2165_, v_bs_2166_);
stack->m_obj
 = v_res_2176_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_sz_2177_, lean_object* v_i_2178_, lean_object* v_bs_2179_){
_start:
{
size_t v_sz_boxed_2180_; size_t v_i_boxed_2181_; lean_object* v_res_2182_; 
v_sz_boxed_2180_ = lean_unbox_usize(v_sz_2177_);
lean_dec(v_sz_2177_);
v_i_boxed_2181_ = lean_unbox_usize(v_i_2178_);
lean_dec(v_i_2178_);
v_res_2182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_boxed_2180_, v_i_boxed_2181_, v_bs_2179_);
return v_res_2182_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_2183_, size_t v_i_2184_, size_t v_stop_2185_, lean_object* v_b_2186_){
_start:
{
lean_object* v___y_2188_; uint8_t v___x_2192_; 
v___x_2192_ = lean_usize_dec_eq(v_i_2184_, v_stop_2185_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; lean_object* v_infoTree_x3f_2194_; 
v___x_2193_ = lean_array_uget_borrowed(v_as_2183_, v_i_2184_);
v_infoTree_x3f_2194_ = lean_ctor_get(v___x_2193_, 2);
if (lean_obj_tag(v_infoTree_x3f_2194_) == 1)
{
lean_object* v_val_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_val_2195_ = lean_ctor_get(v_infoTree_x3f_2194_, 0);
v___x_2196_ = lean_unsigned_to_nat(1u);
v___x_2197_ = lean_mk_empty_array_with_capacity(v___x_2196_);
lean_inc(v_val_2195_);
v___x_2198_ = lean_array_push(v___x_2197_, v_val_2195_);
v___x_2199_ = l_Array_append___redArg(v_b_2186_, v___x_2198_);
lean_dec_ref(v___x_2198_);
v___y_2188_ = v___x_2199_;
goto v___jp_2187_;
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_2201_ = l_Array_append___redArg(v_b_2186_, v___x_2200_);
v___y_2188_ = v___x_2201_;
goto v___jp_2187_;
}
}
else
{
return v_b_2186_;
}
v___jp_2187_:
{
size_t v___x_2189_; size_t v___x_2190_; 
v___x_2189_ = ((size_t)1ULL);
v___x_2190_ = lean_usize_add(v_i_2184_, v___x_2189_);
v_i_2184_ = v___x_2190_;
v_b_2186_ = v___y_2188_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2183_ = stack[0].m_obj;
size_t v_i_2184_ = stack[1].m_num;
size_t v_stop_2185_ = stack[2].m_num;
lean_object* v_b_2186_ = stack[3].m_obj;
lean_object* v_res_2202_;
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_2183_, v_i_2184_, v_stop_2185_, v_b_2186_);
stack->m_obj
 = v_res_2202_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_2203_, lean_object* v_i_2204_, lean_object* v_stop_2205_, lean_object* v_b_2206_){
_start:
{
size_t v_i_boxed_2207_; size_t v_stop_boxed_2208_; lean_object* v_res_2209_; 
v_i_boxed_2207_ = lean_unbox_usize(v_i_2204_);
lean_dec(v_i_2204_);
v_stop_boxed_2208_ = lean_unbox_usize(v_stop_2205_);
lean_dec(v_stop_2205_);
v_res_2209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_2203_, v_i_boxed_2207_, v_stop_boxed_2208_, v_b_2206_);
lean_dec_ref(v_as_2203_);
return v_res_2209_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(lean_object* v_as_2210_, size_t v_i_2211_, size_t v_stop_2212_, lean_object* v_b_2213_){
_start:
{
uint8_t v___x_2214_; 
v___x_2214_ = lean_usize_dec_eq(v_i_2211_, v_stop_2212_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; size_t v___x_2219_; size_t v___x_2220_; 
v___x_2215_ = lean_array_uget_borrowed(v_as_2210_, v_i_2211_);
v___x_2216_ = 2;
v___x_2217_ = lean_box(v___x_2216_);
lean_inc(v___x_2215_);
v___x_2218_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2215_, v___x_2217_, v_b_2213_);
v___x_2219_ = ((size_t)1ULL);
v___x_2220_ = lean_usize_add(v_i_2211_, v___x_2219_);
v_i_2211_ = v___x_2220_;
v_b_2213_ = v___x_2218_;
goto _start;
}
else
{
return v_b_2213_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2210_ = stack[0].m_obj;
size_t v_i_2211_ = stack[1].m_num;
size_t v_stop_2212_ = stack[2].m_num;
lean_object* v_b_2213_ = stack[3].m_obj;
lean_object* v_res_2222_;
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_as_2210_, v_i_2211_, v_stop_2212_, v_b_2213_);
stack->m_obj
 = v_res_2222_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9___boxed(lean_object* v_as_2223_, lean_object* v_i_2224_, lean_object* v_stop_2225_, lean_object* v_b_2226_){
_start:
{
size_t v_i_boxed_2227_; size_t v_stop_boxed_2228_; lean_object* v_res_2229_; 
v_i_boxed_2227_ = lean_unbox_usize(v_i_2224_);
lean_dec(v_i_2224_);
v_stop_boxed_2228_ = lean_unbox_usize(v_stop_2225_);
lean_dec(v_stop_2225_);
v_res_2229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_as_2223_, v_i_boxed_2227_, v_stop_boxed_2228_, v_b_2226_);
lean_dec_ref(v_as_2223_);
return v_res_2229_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_2233_, lean_object* v_k_2234_, uint8_t v_v_2235_){
_start:
{
lean_object* v_map_2236_; uint8_t v_hasTrace_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2251_; 
v_map_2236_ = lean_ctor_get(v_o_2233_, 0);
v_hasTrace_2237_ = lean_ctor_get_uint8(v_o_2233_, sizeof(void*)*1);
v_isSharedCheck_2251_ = !lean_is_exclusive(v_o_2233_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2239_ = v_o_2233_;
v_isShared_2240_ = v_isSharedCheck_2251_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_map_2236_);
lean_dec(v_o_2233_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2251_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2241_, 0, v_v_2235_);
lean_inc(v_k_2234_);
v___x_2242_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2234_, v___x_2241_, v_map_2236_);
if (v_hasTrace_2237_ == 0)
{
lean_object* v___x_2243_; uint8_t v___x_2244_; lean_object* v___x_2246_; 
v___x_2243_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_2244_ = l_Lean_Name_isPrefixOf(v___x_2243_, v_k_2234_);
lean_dec(v_k_2234_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2242_);
v___x_2246_ = v___x_2239_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2242_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
lean_ctor_set_uint8(v___x_2246_, sizeof(void*)*1, v___x_2244_);
return v___x_2246_;
}
}
else
{
lean_object* v___x_2249_; 
lean_dec(v_k_2234_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2242_);
v___x_2249_ = v___x_2239_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2242_);
lean_ctor_set_uint8(v_reuseFailAlloc_2250_, sizeof(void*)*1, v_hasTrace_2237_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_2233_ = stack[0].m_obj;
lean_object* v_k_2234_ = stack[1].m_obj;
uint8_t v_v_2235_ = stack[2].m_num;
lean_object* v_res_2252_;
v_res_2252_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2233_, v_k_2234_, v_v_2235_);
stack->m_obj
 = v_res_2252_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_2253_, lean_object* v_k_2254_, lean_object* v_v_2255_){
_start:
{
uint8_t v_v_boxed_2256_; lean_object* v_res_2257_; 
v_v_boxed_2256_ = lean_unbox(v_v_2255_);
v_res_2257_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2253_, v_k_2254_, v_v_boxed_2256_);
return v_res_2257_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_2258_, lean_object* v_opt_2259_, uint8_t v_val_2260_){
_start:
{
lean_object* v_name_2261_; lean_object* v___x_2262_; 
v_name_2261_ = lean_ctor_get(v_opt_2259_, 0);
lean_inc(v_name_2261_);
lean_dec_ref(v_opt_2259_);
v___x_2262_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_2258_, v_name_2261_, v_val_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2258_ = stack[0].m_obj;
lean_object* v_opt_2259_ = stack[1].m_obj;
uint8_t v_val_2260_ = stack[2].m_num;
lean_object* v_res_2263_;
v_res_2263_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2258_, v_opt_2259_, v_val_2260_);
stack->m_obj
 = v_res_2263_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_2264_, lean_object* v_opt_2265_, lean_object* v_val_2266_){
_start:
{
uint8_t v_val_boxed_2267_; lean_object* v_res_2268_; 
v_val_boxed_2267_ = lean_unbox(v_val_2266_);
v_res_2268_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2264_, v_opt_2265_, v_val_boxed_2267_);
return v_res_2268_;
}
}
lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_2269_, lean_object* v_opt_2270_, uint8_t v_val_2271_){
_start:
{
lean_object* v_name_2272_; lean_object* v_map_2273_; uint8_t v___x_2274_; 
v_name_2272_ = lean_ctor_get(v_opt_2270_, 0);
v_map_2273_ = lean_ctor_get(v_opts_2269_, 0);
v___x_2274_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_2272_, v_map_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2269_, v_opt_2270_, v_val_2271_);
return v___x_2275_;
}
else
{
lean_dec_ref(v_opt_2270_);
return v_opts_2269_;
}
}
}
LEAN_EXPORT void l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2269_ = stack[0].m_obj;
lean_object* v_opt_2270_ = stack[1].m_obj;
uint8_t v_val_2271_ = stack[2].m_num;
lean_object* v_res_2276_;
v_res_2276_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2269_, v_opt_2270_, v_val_2271_);
stack->m_obj
 = v_res_2276_;
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_2277_, lean_object* v_opt_2278_, lean_object* v_val_2279_){
_start:
{
uint8_t v_val_boxed_2280_; lean_object* v_res_2281_; 
v_val_boxed_2280_ = lean_unbox(v_val_2279_);
v_res_2281_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2277_, v_opt_2278_, v_val_boxed_2280_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0(lean_object* v_a_2282_, lean_object* v_ps_2283_){
_start:
{
lean_object* v_importedEntries_2284_; lean_object* v_state_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2294_; 
v_importedEntries_2284_ = lean_ctor_get(v_ps_2283_, 0);
v_state_2285_ = lean_ctor_get(v_ps_2283_, 1);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_ps_2283_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2287_ = v_ps_2283_;
v_isShared_2288_ = v_isSharedCheck_2294_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_state_2285_);
lean_inc(v_importedEntries_2284_);
lean_dec(v_ps_2283_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2294_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2289_ = lean_task_get_own(v_a_2282_);
v___x_2290_ = l_Array_append___redArg(v_state_2285_, v___x_2289_);
lean_dec(v___x_2289_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 1, v___x_2290_);
v___x_2292_ = v___x_2287_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_importedEntries_2284_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(lean_object* v_as_2295_, size_t v_sz_2296_, size_t v_i_2297_, lean_object* v_b_2298_){
_start:
{
lean_object* v_a_2301_; uint8_t v___x_2305_; 
v___x_2305_ = lean_usize_dec_lt(v_i_2297_, v_sz_2296_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v_b_2298_);
return v___x_2306_;
}
else
{
lean_object* v___x_2307_; lean_object* v_toEnvExtension_2308_; lean_object* v_asyncMode_2309_; uint8_t v_logWrites_2310_; lean_object* v_a_2311_; lean_object* v___f_2312_; lean_object* v___x_2313_; 
v___x_2307_ = l_Lean_Linter_codeQualityLogExt;
v_toEnvExtension_2308_ = lean_ctor_get(v___x_2307_, 0);
v_asyncMode_2309_ = lean_ctor_get(v_toEnvExtension_2308_, 2);
v_logWrites_2310_ = lean_ctor_get_uint8(v_toEnvExtension_2308_, sizeof(void*)*6);
v_a_2311_ = lean_array_uget_borrowed(v_as_2295_, v_i_2297_);
lean_inc(v_a_2311_);
v___f_2312_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2312_, 0, v_a_2311_);
v___x_2313_ = lean_box(0);
if (v_logWrites_2310_ == 0)
{
lean_object* v___x_2314_; 
lean_inc_ref(v_toEnvExtension_2308_);
v___x_2314_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2308_, v_b_2298_, v___f_2312_, v_asyncMode_2309_, v___x_2313_, v___x_2305_);
v_a_2301_ = v___x_2314_;
goto v___jp_2300_;
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
lean_inc_ref_n(v_toEnvExtension_2308_, 2);
v___x_2315_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2308_, v_b_2298_);
lean_dec_ref(v_b_2298_);
v___x_2316_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2308_, v___x_2315_, v___f_2312_, v_asyncMode_2309_, v___x_2313_, v___x_2305_);
v_a_2301_ = v___x_2316_;
goto v___jp_2300_;
}
}
v___jp_2300_:
{
size_t v___x_2302_; size_t v___x_2303_; 
v___x_2302_ = ((size_t)1ULL);
v___x_2303_ = lean_usize_add(v_i_2297_, v___x_2302_);
v_i_2297_ = v___x_2303_;
v_b_2298_ = v_a_2301_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2295_ = stack[0].m_obj;
size_t v_sz_2296_ = stack[1].m_num;
size_t v_i_2297_ = stack[2].m_num;
lean_object* v_b_2298_ = stack[3].m_obj;
lean_object* v_res_2317_;
v_res_2317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v_as_2295_, v_sz_2296_, v_i_2297_, v_b_2298_);
stack->m_obj
 = v_res_2317_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object* v_as_2318_, lean_object* v_sz_2319_, lean_object* v_i_2320_, lean_object* v_b_2321_, lean_object* v___y_2322_){
_start:
{
size_t v_sz_boxed_2323_; size_t v_i_boxed_2324_; lean_object* v_res_2325_; 
v_sz_boxed_2323_ = lean_unbox_usize(v_sz_2319_);
lean_dec(v_sz_2319_);
v_i_boxed_2324_ = lean_unbox_usize(v_i_2320_);
lean_dec(v_i_2320_);
v_res_2325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v_as_2318_, v_sz_boxed_2323_, v_i_boxed_2324_, v_b_2321_);
lean_dec_ref(v_as_2318_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(lean_object* v_s_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = l_Lean_Language_Snapshot_transform(v_s_2328_, v___y_2329_);
v___x_2331_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___closed__0));
v___x_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___boxed(lean_object* v_s_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(v_s_2333_, v___y_2334_);
lean_dec_ref(v___y_2334_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(lean_object* v_t_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v___f_2339_; lean_object* v___x_2340_; 
v___f_2339_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___closed__0));
v___x_2340_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2337_, v___f_2339_, v_a_2338_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object* v_t_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_t_2341_, v_a_2342_);
lean_dec_ref(v_a_2342_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(lean_object* v_t_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___closed__0));
v___x_2348_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2345_, v___x_2347_, v_a_2346_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___boxed(lean_object* v_t_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_t_2349_, v_a_2350_);
lean_dec_ref(v_a_2350_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(lean_object* v_s_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_toSnapshot_2354_; lean_object* v_metaSnap_2355_; lean_object* v_result_x3f_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___y_2360_; 
v_toSnapshot_2354_ = lean_ctor_get(v_s_2352_, 0);
lean_inc_ref(v_toSnapshot_2354_);
v_metaSnap_2355_ = lean_ctor_get(v_s_2352_, 1);
lean_inc_ref(v_metaSnap_2355_);
v_result_x3f_2356_ = lean_ctor_get(v_s_2352_, 2);
lean_inc(v_result_x3f_2356_);
lean_dec_ref(v_s_2352_);
v___x_2357_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2354_, v___y_2353_);
v___x_2358_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2355_, v___y_2353_);
if (lean_obj_tag(v_result_x3f_2356_) == 0)
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_box(0);
v___y_2360_ = v___x_2366_;
goto v___jp_2359_;
}
else
{
lean_object* v_val_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2376_; 
v_val_2367_ = lean_ctor_get(v_result_x3f_2356_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_result_x3f_2356_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2369_ = v_result_x3f_2356_;
v_isShared_2370_ = v_isSharedCheck_2376_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_val_2367_);
lean_dec(v_result_x3f_2356_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2376_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v_firstCmdSnap_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
v_firstCmdSnap_2371_ = lean_ctor_get(v_val_2367_, 1);
lean_inc_ref(v_firstCmdSnap_2371_);
lean_dec(v_val_2367_);
v___x_2372_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_firstCmdSnap_2371_, v___y_2353_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2372_);
v___x_2374_ = v___x_2369_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
v___y_2360_ = v___x_2374_;
goto v___jp_2359_;
}
}
}
v___jp_2359_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2361_ = lean_unsigned_to_nat(1u);
v___x_2362_ = lean_mk_empty_array_with_capacity(v___x_2361_);
v___x_2363_ = lean_array_push(v___x_2362_, v___x_2358_);
v___x_2364_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2360_, v___x_2363_);
v___x_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2357_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
return v___x_2365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0___boxed(lean_object* v_s_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(v_s_2377_, v___y_2378_);
lean_dec_ref(v___y_2378_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(lean_object* v_t_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v___f_2383_; lean_object* v___x_2384_; 
v___f_2383_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___closed__0));
v___x_2384_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2381_, v___f_2383_, v_a_2382_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___boxed(lean_object* v_t_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_t_2385_, v_a_2386_);
lean_dec_ref(v_a_2386_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_a_2388_){
_start:
{
lean_object* v_toSnapshot_2389_; lean_object* v_metaSnap_2390_; lean_object* v_result_x3f_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___y_2396_; 
v_toSnapshot_2389_ = lean_ctor_get(v_a_2388_, 0);
lean_inc_ref(v_toSnapshot_2389_);
v_metaSnap_2390_ = lean_ctor_get(v_a_2388_, 1);
lean_inc_ref(v_metaSnap_2390_);
v_result_x3f_2391_ = lean_ctor_get(v_a_2388_, 4);
lean_inc(v_result_x3f_2391_);
lean_dec_ref(v_a_2388_);
v___x_2392_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_2393_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2389_, v___x_2392_);
v___x_2394_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2390_, v___x_2392_);
if (lean_obj_tag(v_result_x3f_2391_) == 0)
{
lean_object* v___x_2402_; 
v___x_2402_ = lean_box(0);
v___y_2396_ = v___x_2402_;
goto v___jp_2395_;
}
else
{
lean_object* v_val_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2412_; 
v_val_2403_ = lean_ctor_get(v_result_x3f_2391_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_result_x3f_2391_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2405_ = v_result_x3f_2391_;
v_isShared_2406_ = v_isSharedCheck_2412_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_val_2403_);
lean_dec(v_result_x3f_2391_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2412_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v_processedSnap_2407_; lean_object* v___x_2408_; lean_object* v___x_2410_; 
v_processedSnap_2407_ = lean_ctor_get(v_val_2403_, 1);
lean_inc_ref(v_processedSnap_2407_);
lean_dec(v_val_2403_);
v___x_2408_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_processedSnap_2407_, v___x_2392_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2408_);
v___x_2410_ = v___x_2405_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
v___y_2396_ = v___x_2410_;
goto v___jp_2395_;
}
}
}
v___jp_2395_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_mk_empty_array_with_capacity(v___x_2397_);
v___x_2399_ = lean_array_push(v___x_2398_, v___x_2394_);
v___x_2400_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2396_, v___x_2399_);
v___x_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2393_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
return v___x_2401_;
}
}
}
static double _init_l_Lean_Elab_runFrontend___closed__2(void){
_start:
{
lean_object* v___x_2415_; double v___x_2416_; 
v___x_2415_ = lean_unsigned_to_nat(1000000000u);
v___x_2416_ = lean_float_of_nat(v___x_2415_);
return v___x_2416_;
}
}
lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_2418_, lean_object* v_opts_2419_, lean_object* v_fileName_2420_, lean_object* v_mainModuleName_2421_, uint32_t v_trustLevel_2422_, lean_object* v_oleanFileName_x3f_2423_, lean_object* v_ileanFileName_x3f_2424_, uint8_t v_jsonOutput_2425_, lean_object* v_errorOnKinds_2426_, lean_object* v_plugins_2427_, uint8_t v_printStats_2428_, lean_object* v_setup_x3f_2429_, lean_object* v_incrSaveFileName_x3f_2430_, lean_object* v_incrLoadFileName_x3f_2431_, lean_object* v_incrHeaderSaveFileName_x3f_2432_){
_start:
{
lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___f_2440_; lean_object* v___f_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; double v___x_2444_; double v___x_2445_; double v___x_2446_; uint8_t v___x_2447_; size_t v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___x_2509_; lean_object* v___x_2510_; size_t v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; uint8_t v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; size_t v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; uint8_t v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; uint8_t v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; size_t v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; uint8_t v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; uint8_t v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; size_t v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; uint8_t v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; uint8_t v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; size_t v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; uint8_t v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; uint8_t v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v___y_2650_; uint8_t v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v_a_2719_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v___y_2740_; 
v___f_2440_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___f_2441_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__1));
v___x_2442_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2443_ = lean_io_mono_nanos_now();
v___x_2444_ = lean_float_of_nat(v___x_2443_);
v___x_2445_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__2, &l_Lean_Elab_runFrontend___closed__2_once, _init_l_Lean_Elab_runFrontend___closed__2);
v___x_2446_ = lean_float_div(v___x_2444_, v___x_2445_);
v___x_2447_ = 1;
v___x_2509_ = lean_string_utf8_byte_size(v_input_2418_);
v___x_2510_ = l_Lean_Parser_mkInputContext___redArg(v_input_2418_, v_fileName_2420_, v___x_2447_, v___x_2509_);
v___x_2738_ = l_Lean_internal_cmdlineSnapshots;
if (lean_obj_tag(v_incrSaveFileName_x3f_2430_) == 0)
{
v___y_2740_ = v___x_2447_;
goto v___jp_2739_;
}
else
{
uint8_t v___x_2776_; 
v___x_2776_ = 0;
v___y_2740_ = v___x_2776_;
goto v___jp_2739_;
}
v___jp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = lean_runtime_forget(v___y_2435_);
v___x_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___y_2436_);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
return v___x_2439_;
}
v___jp_2448_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = l_Lean_trace_profiler_output;
v___x_2455_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v___y_2450_, v___x_2454_);
if (lean_obj_tag(v___x_2455_) == 1)
{
lean_object* v_val_2456_; lean_object* v___x_2457_; size_t v_sz_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
lean_dec_ref(v___y_2452_);
v_val_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_val_2456_);
lean_dec_ref_known(v___x_2455_, 1);
lean_inc_ref(v___y_2451_);
v___x_2457_ = l_Lean_Language_SnapshotTree_getAll(v___y_2451_);
v_sz_2458_ = lean_array_size(v___x_2457_);
v___x_2459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2458_, v___y_2449_, v___x_2457_);
v___x_2460_ = l_Lean_Name_toString(v_mainModuleName_2421_, v___x_2447_);
v___x_2461_ = l_Lean_Firefox_Profile_export(v___x_2460_, v___x_2446_, v___x_2459_, v___y_2450_);
lean_dec_ref(v___y_2450_);
lean_dec_ref(v___x_2459_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref_known(v___x_2461_, 1);
v___x_2463_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2462_);
v___x_2464_ = l_Lean_Json_compress(v___x_2463_);
v___x_2465_ = l_IO_FS_writeFile(v_val_2456_, v___x_2464_);
lean_dec_ref(v___x_2464_);
lean_dec(v_val_2456_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_dec_ref_known(v___x_2465_, 1);
v___y_2435_ = v___y_2451_;
v___y_2436_ = v___y_2453_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v___y_2453_);
lean_dec_ref(v___y_2451_);
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2465_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2465_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v_val_2456_);
lean_dec_ref(v___y_2453_);
lean_dec_ref(v___y_2451_);
v_a_2474_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2461_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2461_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
lean_dec(v___x_2455_);
v___x_2482_ = l_Lean_trace_profiler_serve;
v___x_2483_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v___y_2452_, v___x_2482_);
lean_dec_ref(v___y_2452_);
if (v___x_2483_ == 0)
{
lean_dec_ref(v___y_2450_);
lean_dec(v_mainModuleName_2421_);
v___y_2435_ = v___y_2451_;
v___y_2436_ = v___y_2453_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2484_; size_t v_sz_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
lean_inc_ref(v___y_2451_);
v___x_2484_ = l_Lean_Language_SnapshotTree_getAll(v___y_2451_);
v_sz_2485_ = lean_array_size(v___x_2484_);
v___x_2486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2485_, v___y_2449_, v___x_2484_);
v___x_2487_ = l_Lean_Name_toString(v_mainModuleName_2421_, v___x_2447_);
v___x_2488_ = l_Lean_Firefox_Profile_export(v___x_2487_, v___x_2446_, v___x_2486_, v___y_2450_);
lean_dec_ref(v___y_2450_);
lean_dec_ref(v___x_2486_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v___x_2490_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2489_);
v___x_2491_ = l_Lean_Json_compress(v___x_2490_);
v___x_2492_ = l_Lean_Firefox_Profile_serve(v___x_2491_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_dec_ref_known(v___x_2492_, 1);
v___y_2435_ = v___y_2451_;
v___y_2436_ = v___y_2453_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec_ref(v___y_2453_);
lean_dec_ref(v___y_2451_);
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec_ref(v___y_2453_);
lean_dec_ref(v___y_2451_);
v_a_2501_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2488_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2488_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
}
v___jp_2511_:
{
lean_object* v_fileMap_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v_fst_2524_; lean_object* v_snd_2525_; lean_object* v_stx_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2546_; 
v_fileMap_2521_ = lean_ctor_get(v___x_2510_, 2);
lean_inc_ref(v_fileMap_2521_);
lean_dec_ref(v___x_2510_);
v___x_2522_ = l_Lean_Server_findModuleRefs(v_fileMap_2521_, v___y_2520_, v___y_2516_, v___y_2516_);
lean_dec_ref(v___y_2520_);
v___x_2523_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_2522_);
v_fst_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_fst_2524_);
v_snd_2525_ = lean_ctor_get(v___x_2523_, 1);
lean_inc(v_snd_2525_);
lean_dec_ref(v___x_2523_);
v_stx_2526_ = lean_ctor_get(v___y_2517_, 3);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___y_2517_);
if (v_isSharedCheck_2546_ == 0)
{
lean_object* v_unused_2547_; lean_object* v_unused_2548_; lean_object* v_unused_2549_; lean_object* v_unused_2550_; 
v_unused_2547_ = lean_ctor_get(v___y_2517_, 4);
lean_dec(v_unused_2547_);
v_unused_2548_ = lean_ctor_get(v___y_2517_, 2);
lean_dec(v_unused_2548_);
v_unused_2549_ = lean_ctor_get(v___y_2517_, 1);
lean_dec(v_unused_2549_);
v_unused_2550_ = lean_ctor_get(v___y_2517_, 0);
lean_dec(v_unused_2550_);
v___x_2528_ = v___y_2517_;
v_isShared_2529_ = v_isSharedCheck_2546_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_stx_2526_);
lean_dec(v___y_2517_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2546_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2530_ = lean_unsigned_to_nat(5u);
v___x_2531_ = l_Lean_Server_collectImports(v_stx_2526_);
lean_inc(v_mainModuleName_2421_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 4, v_snd_2525_);
lean_ctor_set(v___x_2528_, 3, v_fst_2524_);
lean_ctor_set(v___x_2528_, 2, v___x_2531_);
lean_ctor_set(v___x_2528_, 1, v_mainModuleName_2421_);
lean_ctor_set(v___x_2528_, 0, v___x_2530_);
v___x_2533_ = v___x_2528_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_mainModuleName_2421_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v___x_2531_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v_fst_2524_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v_snd_2525_);
v___x_2533_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = l_Lean_Server_instToJsonIlean_toJson(v___x_2533_);
v___x_2535_ = l_Lean_Json_compress(v___x_2534_);
v___x_2536_ = l_IO_FS_writeFile(v___y_2514_, v___x_2535_);
lean_dec_ref(v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_dec_ref_known(v___x_2536_, 1);
v___y_2449_ = v___y_2512_;
v___y_2450_ = v___y_2513_;
v___y_2451_ = v___y_2515_;
v___y_2452_ = v___y_2519_;
v___y_2453_ = v___y_2518_;
goto v___jp_2448_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec_ref(v___y_2515_);
lean_dec_ref(v___y_2513_);
lean_dec(v_mainModuleName_2421_);
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
}
}
v___jp_2551_:
{
if (lean_obj_tag(v_ileanFileName_x3f_2424_) == 1)
{
lean_object* v_val_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v_val_2560_ = lean_ctor_get(v_ileanFileName_x3f_2424_, 0);
lean_inc_ref(v___y_2555_);
v___x_2561_ = l_Lean_Language_SnapshotTree_getAll(v___y_2555_);
v___x_2562_ = lean_mk_empty_array_with_capacity(v___y_2553_);
v___x_2563_ = lean_array_get_size(v___x_2561_);
v___x_2564_ = lean_nat_dec_lt(v___y_2553_, v___x_2563_);
lean_dec(v___y_2553_);
if (v___x_2564_ == 0)
{
lean_dec_ref(v___x_2561_);
v___y_2512_ = v___y_2552_;
v___y_2513_ = v___y_2554_;
v___y_2514_ = v_val_2560_;
v___y_2515_ = v___y_2555_;
v___y_2516_ = v___y_2556_;
v___y_2517_ = v___y_2557_;
v___y_2518_ = v___y_2559_;
v___y_2519_ = v___y_2558_;
v___y_2520_ = v___x_2562_;
goto v___jp_2511_;
}
else
{
size_t v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_usize_of_nat(v___x_2563_);
v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v___x_2561_, v___y_2552_, v___x_2565_, v___x_2562_);
lean_dec_ref(v___x_2561_);
v___y_2512_ = v___y_2552_;
v___y_2513_ = v___y_2554_;
v___y_2514_ = v_val_2560_;
v___y_2515_ = v___y_2555_;
v___y_2516_ = v___y_2556_;
v___y_2517_ = v___y_2557_;
v___y_2518_ = v___y_2559_;
v___y_2519_ = v___y_2558_;
v___y_2520_ = v___x_2566_;
goto v___jp_2511_;
}
}
else
{
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2553_);
lean_dec_ref(v___x_2510_);
v___y_2449_ = v___y_2552_;
v___y_2450_ = v___y_2554_;
v___y_2451_ = v___y_2555_;
v___y_2452_ = v___y_2558_;
v___y_2453_ = v___y_2559_;
goto v___jp_2448_;
}
}
v___jp_2567_:
{
if (v___y_2575_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_2423_) == 1)
{
lean_object* v_val_2579_; lean_object* v_fileMap_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___f_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v_val_2579_ = lean_ctor_get(v_oleanFileName_x3f_2423_, 0);
lean_inc(v_val_2579_);
lean_dec_ref_known(v_oleanFileName_x3f_2423_, 1);
v_fileMap_2580_ = lean_ctor_get(v___x_2510_, 2);
v___x_2581_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__3));
v___x_2582_ = lean_box(0);
v___x_2583_ = lean_mk_empty_array_with_capacity(v___y_2573_);
lean_inc_ref(v___y_2574_);
v___x_2584_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___y_2574_, v___x_2582_, v___x_2583_);
v___x_2585_ = lean_box(v___x_2447_);
v___x_2586_ = lean_box(v___y_2568_);
lean_inc_ref(v_fileMap_2580_);
v___f_2587_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2587_, 0, v_fileMap_2580_);
lean_closure_set(v___f_2587_, 1, v___y_2570_);
lean_closure_set(v___f_2587_, 2, v___x_2584_);
lean_closure_set(v___f_2587_, 3, v___y_2569_);
lean_closure_set(v___f_2587_, 4, v_val_2579_);
lean_closure_set(v___f_2587_, 5, v___x_2585_);
lean_closure_set(v___f_2587_, 6, v___x_2586_);
v___x_2588_ = lean_box(0);
v___x_2589_ = l_Lean_profileitIOUnsafe___redArg(v___x_2581_, v___y_2578_, v___f_2587_, v___x_2588_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_dec_ref_known(v___x_2589_, 1);
v___y_2552_ = v___y_2571_;
v___y_2553_ = v___y_2573_;
v___y_2554_ = v___y_2572_;
v___y_2555_ = v___y_2574_;
v___y_2556_ = v___y_2575_;
v___y_2557_ = v___y_2576_;
v___y_2558_ = v___y_2578_;
v___y_2559_ = v___y_2577_;
goto v___jp_2551_;
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec_ref(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___x_2510_);
lean_dec(v_mainModuleName_2421_);
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
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
else
{
lean_dec_ref(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v_oleanFileName_x3f_2423_);
v___y_2552_ = v___y_2571_;
v___y_2553_ = v___y_2573_;
v___y_2554_ = v___y_2572_;
v___y_2555_ = v___y_2574_;
v___y_2556_ = v___y_2575_;
v___y_2557_ = v___y_2576_;
v___y_2558_ = v___y_2578_;
v___y_2559_ = v___y_2577_;
goto v___jp_2551_;
}
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_dec_ref(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v___x_2510_);
lean_dec(v_oleanFileName_x3f_2423_);
lean_dec(v_mainModuleName_2421_);
v___x_2598_ = lean_box(0);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
return v___x_2599_;
}
}
v___jp_2600_:
{
if (v_printStats_2428_ == 0)
{
v___y_2568_ = v___y_2601_;
v___y_2569_ = v___y_2603_;
v___y_2570_ = v___y_2602_;
v___y_2571_ = v___y_2604_;
v___y_2572_ = v___y_2606_;
v___y_2573_ = v___y_2605_;
v___y_2574_ = v___y_2607_;
v___y_2575_ = v___y_2608_;
v___y_2576_ = v___y_2609_;
v___y_2577_ = v___y_2611_;
v___y_2578_ = v___y_2610_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2612_; 
lean_inc_ref(v___y_2611_);
v___x_2612_ = l_Lean_Environment_displayStats(v___y_2611_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_dec_ref_known(v___x_2612_, 1);
v___y_2568_ = v___y_2601_;
v___y_2569_ = v___y_2603_;
v___y_2570_ = v___y_2602_;
v___y_2571_ = v___y_2604_;
v___y_2572_ = v___y_2606_;
v___y_2573_ = v___y_2605_;
v___y_2574_ = v___y_2607_;
v___y_2575_ = v___y_2608_;
v___y_2576_ = v___y_2609_;
v___y_2577_ = v___y_2611_;
v___y_2578_ = v___y_2610_;
goto v___jp_2567_;
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec_ref(v___x_2510_);
lean_dec(v_oleanFileName_x3f_2423_);
lean_dec(v_mainModuleName_2421_);
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
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
}
v___jp_2621_:
{
if (lean_obj_tag(v_incrHeaderSaveFileName_x3f_2432_) == 1)
{
lean_object* v_val_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v_val_2633_ = lean_ctor_get(v_incrHeaderSaveFileName_x3f_2432_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v_incrHeaderSaveFileName_x3f_2432_, 1);
lean_inc_ref(v___y_2631_);
v___x_2634_ = l_Lean_Language_Lean_truncateToHeader(v___y_2631_);
v___x_2635_ = lean_apply_3(v___y_2623_, v_val_2633_, v___x_2634_, lean_box(0));
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_dec_ref_known(v___x_2635_, 1);
lean_inc_ref(v___y_2625_);
v___y_2601_ = v___y_2622_;
v___y_2602_ = v___y_2625_;
v___y_2603_ = v___y_2624_;
v___y_2604_ = v___y_2626_;
v___y_2605_ = v___y_2628_;
v___y_2606_ = v___y_2627_;
v___y_2607_ = v___y_2629_;
v___y_2608_ = v___y_2630_;
v___y_2609_ = v___y_2631_;
v___y_2610_ = v___y_2632_;
v___y_2611_ = v___y_2625_;
goto v___jp_2600_;
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec_ref(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec_ref(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec_ref(v___x_2510_);
lean_dec(v_oleanFileName_x3f_2423_);
lean_dec(v_mainModuleName_2421_);
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
else
{
lean_dec_ref(v___y_2623_);
lean_dec(v_incrHeaderSaveFileName_x3f_2432_);
lean_inc_ref(v___y_2625_);
v___y_2601_ = v___y_2622_;
v___y_2602_ = v___y_2625_;
v___y_2603_ = v___y_2624_;
v___y_2604_ = v___y_2626_;
v___y_2605_ = v___y_2628_;
v___y_2606_ = v___y_2627_;
v___y_2607_ = v___y_2629_;
v___y_2608_ = v___y_2630_;
v___y_2609_ = v___y_2631_;
v___y_2610_ = v___y_2632_;
v___y_2611_ = v___y_2625_;
goto v___jp_2600_;
}
}
v___jp_2644_:
{
size_t v_sz_2654_; size_t v___x_2655_; lean_object* v___x_2656_; 
v_sz_2654_ = lean_array_size(v___y_2653_);
v___x_2655_ = ((size_t)0ULL);
v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v___y_2653_, v_sz_2654_, v___x_2655_, v___y_2649_);
lean_dec_ref(v___y_2653_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; lean_object* v___f_2659_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc_n(v_a_2657_, 2);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = lean_box(v___x_2447_);
v___f_2659_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2659_, 0, v_a_2657_);
lean_closure_set(v___f_2659_, 1, v___x_2658_);
if (lean_obj_tag(v_incrSaveFileName_x3f_2430_) == 1)
{
lean_object* v_val_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v_val_2660_ = lean_ctor_get(v_incrSaveFileName_x3f_2430_, 0);
lean_inc(v_val_2660_);
lean_dec_ref_known(v_incrSaveFileName_x3f_2430_, 1);
v___x_2661_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___y_2650_);
lean_inc_ref(v___y_2652_);
v___x_2662_ = l_Lean_Elab_runFrontend___lam__2(v_a_2657_, v___x_2447_, v_val_2660_, v___y_2652_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_dec_ref_known(v___x_2662_, 1);
lean_inc_ref(v___y_2646_);
v___y_2622_ = v___y_2645_;
v___y_2623_ = v___f_2659_;
v___y_2624_ = v___y_2646_;
v___y_2625_ = v_a_2657_;
v___y_2626_ = v___x_2655_;
v___y_2627_ = v___y_2648_;
v___y_2628_ = v___y_2647_;
v___y_2629_ = v___y_2650_;
v___y_2630_ = v___y_2651_;
v___y_2631_ = v___y_2652_;
v___y_2632_ = v___y_2646_;
goto v___jp_2621_;
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec_ref(v___f_2659_);
lean_dec(v_a_2657_);
lean_dec_ref(v___y_2652_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v___x_2510_);
lean_dec(v_incrHeaderSaveFileName_x3f_2432_);
lean_dec(v_oleanFileName_x3f_2423_);
lean_dec(v_mainModuleName_2421_);
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
else
{
lean_dec(v_incrSaveFileName_x3f_2430_);
lean_inc_ref(v___y_2646_);
v___y_2622_ = v___y_2645_;
v___y_2623_ = v___f_2659_;
v___y_2624_ = v___y_2646_;
v___y_2625_ = v_a_2657_;
v___y_2626_ = v___x_2655_;
v___y_2627_ = v___y_2648_;
v___y_2628_ = v___y_2647_;
v___y_2629_ = v___y_2650_;
v___y_2630_ = v___y_2651_;
v___y_2631_ = v___y_2652_;
v___y_2632_ = v___y_2646_;
goto v___jp_2621_;
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec_ref(v___y_2652_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec_ref(v___x_2510_);
lean_dec(v_incrHeaderSaveFileName_x3f_2432_);
lean_dec(v_incrSaveFileName_x3f_2430_);
lean_dec(v_oleanFileName_x3f_2423_);
lean_dec(v_mainModuleName_2421_);
v_a_2671_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2656_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2656_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
v___jp_2679_:
{
lean_object* v___x_2685_; 
lean_inc_ref(v___y_2682_);
v___x_2685_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_2682_, v___y_2681_, v_jsonOutput_2425_, v___y_2684_);
lean_dec(v___y_2684_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2707_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2707_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2707_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; 
lean_inc_ref(v___y_2683_);
v___x_2690_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___y_2683_);
if (lean_obj_tag(v___x_2690_) == 1)
{
lean_object* v_val_2691_; lean_object* v_env_2692_; lean_object* v_scopes_2693_; lean_object* v___x_2694_; lean_object* v_opts_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_del_object(v___x_2688_);
v_val_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_val_2691_);
lean_dec_ref_known(v___x_2690_, 1);
v_env_2692_ = lean_ctor_get(v_val_2691_, 0);
lean_inc_ref(v_env_2692_);
v_scopes_2693_ = lean_ctor_get(v_val_2691_, 2);
lean_inc(v_scopes_2693_);
lean_dec(v_val_2691_);
lean_inc(v___y_2680_);
v___x_2694_ = l_List_get_x21Internal___redArg(v___x_2442_, v_scopes_2693_, v___y_2680_);
lean_dec(v_scopes_2693_);
v_opts_2695_ = lean_ctor_get(v___x_2694_, 1);
lean_inc_ref(v_opts_2695_);
lean_dec(v___x_2694_);
v___x_2696_ = lean_mk_empty_array_with_capacity(v___y_2680_);
lean_inc_ref(v___x_2696_);
lean_inc_ref(v___y_2683_);
v___x_2697_ = l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(v___y_2683_, v___x_2696_, v___f_2441_);
if (lean_obj_tag(v___x_2697_) == 0)
{
uint8_t v___x_2698_; uint8_t v___x_2699_; 
v___x_2698_ = lean_unbox(v_a_2686_);
v___x_2699_ = lean_unbox(v_a_2686_);
lean_dec(v_a_2686_);
v___y_2645_ = v___x_2698_;
v___y_2646_ = v_opts_2695_;
v___y_2647_ = v___y_2680_;
v___y_2648_ = v___y_2681_;
v___y_2649_ = v_env_2692_;
v___y_2650_ = v___y_2682_;
v___y_2651_ = v___x_2699_;
v___y_2652_ = v___y_2683_;
v___y_2653_ = v___x_2696_;
goto v___jp_2644_;
}
else
{
lean_object* v_val_2700_; uint8_t v___x_2701_; uint8_t v___x_2702_; 
lean_dec_ref(v___x_2696_);
v_val_2700_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_val_2700_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2701_ = lean_unbox(v_a_2686_);
v___x_2702_ = lean_unbox(v_a_2686_);
lean_dec(v_a_2686_);
v___y_2645_ = v___x_2701_;
v___y_2646_ = v_opts_2695_;
v___y_2647_ = v___y_2680_;
v___y_2648_ = v___y_2681_;
v___y_2649_ = v_env_2692_;
v___y_2650_ = v___y_2682_;
v___y_2651_ = v___x_2702_;
v___y_2652_ = v___y_2683_;
v___y_2653_ = v_val_2700_;
goto v___jp_2644_;
}
}
else
{
lean_object* v___x_2703_; lean_object* v___x_2705_; 
lean_dec(v___x_2690_);
lean_dec(v_a_2686_);
lean_dec_ref(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___x_2510_);
lean_dec(v_incrHeaderSaveFileName_x3f_2432_);
lean_dec(v_incrSaveFileName_x3f_2430_);
lean_dec(v_oleanFileName_x3f_2423_);
lean_dec(v_mainModuleName_2421_);
v___x_2703_ = lean_box(0);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2703_);
v___x_2705_ = v___x_2688_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec_ref(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___x_2510_);
lean_dec(v_incrHeaderSaveFileName_x3f_2432_);
lean_dec(v_incrSaveFileName_x3f_2430_);
lean_dec(v_oleanFileName_x3f_2423_);
lean_dec(v_mainModuleName_2421_);
v_a_2708_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2685_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2685_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
v___jp_2716_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2720_ = l_Lean_Language_Lean_process(v___y_2718_, v_a_2719_, v___x_2510_);
lean_inc_ref(v___x_2720_);
v___x_2721_ = l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(v___x_2720_);
v___x_2722_ = lean_box(1);
v___x_2723_ = lean_unsigned_to_nat(0u);
v___x_2724_ = lean_array_get_size(v_errorOnKinds_2426_);
v___x_2725_ = lean_nat_dec_lt(v___x_2723_, v___x_2724_);
if (v___x_2725_ == 0)
{
v___y_2680_ = v___x_2723_;
v___y_2681_ = v___y_2717_;
v___y_2682_ = v___x_2721_;
v___y_2683_ = v___x_2720_;
v___y_2684_ = v___x_2722_;
goto v___jp_2679_;
}
else
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_nat_dec_le(v___x_2724_, v___x_2724_);
if (v___x_2726_ == 0)
{
if (v___x_2725_ == 0)
{
v___y_2680_ = v___x_2723_;
v___y_2681_ = v___y_2717_;
v___y_2682_ = v___x_2721_;
v___y_2683_ = v___x_2720_;
v___y_2684_ = v___x_2722_;
goto v___jp_2679_;
}
else
{
size_t v___x_2727_; size_t v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = ((size_t)0ULL);
v___x_2728_ = lean_usize_of_nat(v___x_2724_);
v___x_2729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_errorOnKinds_2426_, v___x_2727_, v___x_2728_, v___x_2722_);
v___y_2680_ = v___x_2723_;
v___y_2681_ = v___y_2717_;
v___y_2682_ = v___x_2721_;
v___y_2683_ = v___x_2720_;
v___y_2684_ = v___x_2729_;
goto v___jp_2679_;
}
}
else
{
size_t v___x_2730_; size_t v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = ((size_t)0ULL);
v___x_2731_ = lean_usize_of_nat(v___x_2724_);
v___x_2732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_errorOnKinds_2426_, v___x_2730_, v___x_2731_, v___x_2722_);
v___y_2680_ = v___x_2723_;
v___y_2681_ = v___y_2717_;
v___y_2682_ = v___x_2721_;
v___y_2683_ = v___x_2720_;
v___y_2684_ = v___x_2732_;
goto v___jp_2679_;
}
}
}
v___jp_2733_:
{
lean_object* v___x_2737_; 
v___x_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2737_, 0, v_a_2736_);
v___y_2717_ = v___y_2734_;
v___y_2718_ = v___y_2735_;
v_a_2719_ = v___x_2737_;
goto v___jp_2716_;
}
v___jp_2739_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___f_2746_; 
v___x_2741_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2419_, v___x_2738_, v___y_2740_);
v___x_2742_ = l_Lean_Elab_async;
v___x_2743_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_2741_, v___x_2742_, v___x_2447_);
v___x_2744_ = lean_box_uint32(v_trustLevel_2422_);
v___x_2745_ = lean_box(v___x_2447_);
lean_inc(v_mainModuleName_2421_);
lean_inc_ref(v___x_2743_);
v___f_2746_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4___boxed), 10, 7);
lean_closure_set(v___f_2746_, 0, v_setup_x3f_2429_);
lean_closure_set(v___f_2746_, 1, v___f_2440_);
lean_closure_set(v___f_2746_, 2, v___x_2743_);
lean_closure_set(v___f_2746_, 3, v_plugins_2427_);
lean_closure_set(v___f_2746_, 4, v___x_2744_);
lean_closure_set(v___f_2746_, 5, v___x_2745_);
lean_closure_set(v___f_2746_, 6, v_mainModuleName_2421_);
if (lean_obj_tag(v_incrLoadFileName_x3f_2431_) == 0)
{
lean_object* v___x_2747_; 
v___x_2747_ = lean_box(0);
v___y_2717_ = v___x_2743_;
v___y_2718_ = v___f_2746_;
v_a_2719_ = v___x_2747_;
goto v___jp_2716_;
}
else
{
lean_object* v_val_2748_; lean_object* v___x_2749_; 
v_val_2748_ = lean_ctor_get(v_incrLoadFileName_x3f_2431_, 0);
lean_inc(v_val_2748_);
lean_dec_ref_known(v_incrLoadFileName_x3f_2431_, 1);
v___x_2749_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_val_2748_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v_snap_2751_; lean_object* v_initModIdxs_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v_snap_2751_ = lean_ctor_get(v_a_2750_, 0);
lean_inc_ref(v_snap_2751_);
v_initModIdxs_2752_ = lean_ctor_get(v_a_2750_, 1);
lean_inc_ref(v_initModIdxs_2752_);
lean_dec(v_a_2750_);
lean_inc(v_mainModuleName_2421_);
v___x_2753_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(v_snap_2751_, v_mainModuleName_2421_);
lean_inc_ref(v___x_2753_);
v___x_2754_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v___x_2753_);
v___x_2755_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_2754_);
if (lean_obj_tag(v___x_2755_) == 1)
{
lean_object* v_val_2756_; lean_object* v___f_2757_; lean_object* v___x_2758_; 
v_val_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_val_2756_);
lean_dec_ref_known(v___x_2755_, 1);
lean_inc_ref(v___x_2743_);
v___f_2757_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__5___boxed), 4, 3);
lean_closure_set(v___f_2757_, 0, v_val_2756_);
lean_closure_set(v___f_2757_, 1, v_initModIdxs_2752_);
lean_closure_set(v___f_2757_, 2, v___x_2743_);
v___x_2758_ = l_Lean_withImporting___redArg(v___f_2757_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v___x_2759_; 
lean_dec_ref_known(v___x_2758_, 1);
v___x_2759_ = lean_enable_initializer_execution();
v___y_2734_ = v___x_2743_;
v___y_2735_ = v___f_2746_;
v_a_2736_ = v___x_2753_;
goto v___jp_2733_;
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec_ref(v___x_2753_);
lean_dec_ref(v___f_2746_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v___x_2510_);
lean_dec(v_incrHeaderSaveFileName_x3f_2432_);
lean_dec(v_incrSaveFileName_x3f_2430_);
lean_dec(v_oleanFileName_x3f_2423_);
lean_dec(v_mainModuleName_2421_);
v_a_2760_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2758_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2758_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_dec(v___x_2755_);
lean_dec_ref(v_initModIdxs_2752_);
v___y_2734_ = v___x_2743_;
v___y_2735_ = v___f_2746_;
v_a_2736_ = v___x_2753_;
goto v___jp_2733_;
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref(v___f_2746_);
lean_dec_ref(v___x_2743_);
lean_dec_ref(v___x_2510_);
lean_dec(v_incrHeaderSaveFileName_x3f_2432_);
lean_dec(v_incrSaveFileName_x3f_2430_);
lean_dec(v_oleanFileName_x3f_2423_);
lean_dec(v_mainModuleName_2421_);
v_a_2768_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2749_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2749_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_runFrontend_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_2418_ = stack[0].m_obj;
lean_object* v_opts_2419_ = stack[1].m_obj;
lean_object* v_fileName_2420_ = stack[2].m_obj;
lean_object* v_mainModuleName_2421_ = stack[3].m_obj;
uint32_t v_trustLevel_2422_ = stack[4].m_num;
lean_object* v_oleanFileName_x3f_2423_ = stack[5].m_obj;
lean_object* v_ileanFileName_x3f_2424_ = stack[6].m_obj;
uint8_t v_jsonOutput_2425_ = stack[7].m_num;
lean_object* v_errorOnKinds_2426_ = stack[8].m_obj;
lean_object* v_plugins_2427_ = stack[9].m_obj;
uint8_t v_printStats_2428_ = stack[10].m_num;
lean_object* v_setup_x3f_2429_ = stack[11].m_obj;
lean_object* v_incrSaveFileName_x3f_2430_ = stack[12].m_obj;
lean_object* v_incrLoadFileName_x3f_2431_ = stack[13].m_obj;
lean_object* v_incrHeaderSaveFileName_x3f_2432_ = stack[14].m_obj;
lean_object* v_res_2777_;
v_res_2777_ = l_Lean_Elab_runFrontend(v_input_2418_, v_opts_2419_, v_fileName_2420_, v_mainModuleName_2421_, v_trustLevel_2422_, v_oleanFileName_x3f_2423_, v_ileanFileName_x3f_2424_, v_jsonOutput_2425_, v_errorOnKinds_2426_, v_plugins_2427_, v_printStats_2428_, v_setup_x3f_2429_, v_incrSaveFileName_x3f_2430_, v_incrLoadFileName_x3f_2431_, v_incrHeaderSaveFileName_x3f_2432_);
stack->m_obj
 = v_res_2777_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_2778_, lean_object* v_opts_2779_, lean_object* v_fileName_2780_, lean_object* v_mainModuleName_2781_, lean_object* v_trustLevel_2782_, lean_object* v_oleanFileName_x3f_2783_, lean_object* v_ileanFileName_x3f_2784_, lean_object* v_jsonOutput_2785_, lean_object* v_errorOnKinds_2786_, lean_object* v_plugins_2787_, lean_object* v_printStats_2788_, lean_object* v_setup_x3f_2789_, lean_object* v_incrSaveFileName_x3f_2790_, lean_object* v_incrLoadFileName_x3f_2791_, lean_object* v_incrHeaderSaveFileName_x3f_2792_, lean_object* v_a_2793_){
_start:
{
uint32_t v_trustLevel_boxed_2794_; uint8_t v_jsonOutput_boxed_2795_; uint8_t v_printStats_boxed_2796_; lean_object* v_res_2797_; 
v_trustLevel_boxed_2794_ = lean_unbox_uint32(v_trustLevel_2782_);
lean_dec(v_trustLevel_2782_);
v_jsonOutput_boxed_2795_ = lean_unbox(v_jsonOutput_2785_);
v_printStats_boxed_2796_ = lean_unbox(v_printStats_2788_);
v_res_2797_ = l_Lean_Elab_runFrontend(v_input_2778_, v_opts_2779_, v_fileName_2780_, v_mainModuleName_2781_, v_trustLevel_boxed_2794_, v_oleanFileName_x3f_2783_, v_ileanFileName_x3f_2784_, v_jsonOutput_boxed_2795_, v_errorOnKinds_2786_, v_plugins_2787_, v_printStats_boxed_2796_, v_setup_x3f_2789_, v_incrSaveFileName_x3f_2790_, v_incrLoadFileName_x3f_2791_, v_incrHeaderSaveFileName_x3f_2792_);
lean_dec_ref(v_errorOnKinds_2786_);
lean_dec(v_ileanFileName_x3f_2784_);
return v_res_2797_;
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
