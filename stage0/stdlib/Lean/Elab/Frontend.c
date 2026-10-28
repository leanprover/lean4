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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_38_; lean_object* v_fileName_39_; lean_object* v_fileMap_40_; lean_object* v_commandState_41_; lean_object* v_cmdPos_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; uint8_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
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
v___x_49_ = 0;
lean_inc_ref(v_fileMap_40_);
lean_inc_ref(v_fileName_39_);
v___x_50_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_50_, 0, v_fileName_39_);
lean_ctor_set(v___x_50_, 1, v_fileMap_40_);
lean_ctor_set(v___x_50_, 2, v___x_43_);
lean_ctor_set(v___x_50_, 3, v_cmdPos_42_);
lean_ctor_set(v___x_50_, 4, v___x_44_);
lean_ctor_set(v___x_50_, 5, v___x_45_);
lean_ctor_set(v___x_50_, 6, v___x_46_);
lean_ctor_set(v___x_50_, 7, v___x_47_);
lean_ctor_set(v___x_50_, 8, v___x_45_);
lean_ctor_set(v___x_50_, 9, v___x_45_);
lean_ctor_set_uint8(v___x_50_, sizeof(void*)*10, v___x_48_);
lean_ctor_set_uint8(v___x_50_, sizeof(void*)*10 + 1, v___x_49_);
v___x_51_ = lean_st_mk_ref(v_commandState_41_);
lean_inc(v___x_51_);
v___x_52_ = lean_apply_3(v_x_34_, v___x_50_, v___x_51_, lean_box(0));
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_62_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
lean_dec_ref_known(v___x_52_, 1);
v___x_54_ = lean_st_ref_get(v___x_51_);
lean_dec(v___x_51_);
v___x_55_ = l_Lean_Elab_Frontend_setCommandState___redArg(v___x_54_, v_a_36_);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_62_ == 0)
{
lean_object* v_unused_63_; 
v_unused_63_ = lean_ctor_get(v___x_55_, 0);
lean_dec(v_unused_63_);
v___x_57_ = v___x_55_;
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
else
{
lean_dec(v___x_55_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_60_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v_a_53_);
v___x_60_ = v___x_57_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_a_53_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
else
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_76_; 
lean_dec(v___x_51_);
v_a_64_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_76_ == 0)
{
v___x_66_ = v___x_52_;
v_isShared_67_ = v_isSharedCheck_76_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_52_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_76_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_68_ = l_Lean_Exception_toMessageData(v_a_64_);
v___x_69_ = l_Lean_MessageData_toString(v___x_68_);
v___x_70_ = ((lean_object*)(l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0));
v___x_71_ = lean_string_append(v___x_70_, v___x_69_);
lean_dec_ref(v___x_69_);
v___x_72_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v___x_72_);
v___x_74_ = v___x_66_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg___boxed(lean_object* v_x_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Elab_Frontend_runCommandElabM___redArg(v_x_77_, v_a_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object* v_00_u03b1_82_, lean_object* v_x_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v___x_87_; lean_object* v_fileName_88_; lean_object* v_fileMap_89_; lean_object* v_commandState_90_; lean_object* v_cmdPos_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_87_ = lean_st_ref_get(v_a_85_);
v_fileName_88_ = lean_ctor_get(v_a_84_, 1);
v_fileMap_89_ = lean_ctor_get(v_a_84_, 2);
v_commandState_90_ = lean_ctor_get(v___x_87_, 0);
lean_inc_ref(v_commandState_90_);
v_cmdPos_91_ = lean_ctor_get(v___x_87_, 2);
lean_inc(v_cmdPos_91_);
lean_dec(v___x_87_);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_box(0);
v___x_94_ = lean_box(0);
v___x_95_ = l_Lean_firstFrontendMacroScope;
v___x_96_ = lean_box(0);
v___x_97_ = 0;
v___x_98_ = 0;
lean_inc_ref(v_fileMap_89_);
lean_inc_ref(v_fileName_88_);
v___x_99_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_99_, 0, v_fileName_88_);
lean_ctor_set(v___x_99_, 1, v_fileMap_89_);
lean_ctor_set(v___x_99_, 2, v___x_92_);
lean_ctor_set(v___x_99_, 3, v_cmdPos_91_);
lean_ctor_set(v___x_99_, 4, v___x_93_);
lean_ctor_set(v___x_99_, 5, v___x_94_);
lean_ctor_set(v___x_99_, 6, v___x_95_);
lean_ctor_set(v___x_99_, 7, v___x_96_);
lean_ctor_set(v___x_99_, 8, v___x_94_);
lean_ctor_set(v___x_99_, 9, v___x_94_);
lean_ctor_set_uint8(v___x_99_, sizeof(void*)*10, v___x_97_);
lean_ctor_set_uint8(v___x_99_, sizeof(void*)*10 + 1, v___x_98_);
v___x_100_ = lean_st_mk_ref(v_commandState_90_);
lean_inc(v___x_100_);
v___x_101_ = lean_apply_3(v_x_83_, v___x_99_, v___x_100_, lean_box(0));
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_101_, 1);
v___x_103_ = lean_st_ref_get(v___x_100_);
lean_dec(v___x_100_);
v___x_104_ = l_Lean_Elab_Frontend_setCommandState___redArg(v___x_103_, v_a_85_);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v___x_104_, 0);
lean_dec(v_unused_112_);
v___x_106_ = v___x_104_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_dec(v___x_104_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v_a_102_);
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_102_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_125_; 
lean_dec(v___x_100_);
v_a_113_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_125_ == 0)
{
v___x_115_ = v___x_101_;
v_isShared_116_ = v_isSharedCheck_125_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_101_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_125_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_117_ = l_Lean_Exception_toMessageData(v_a_113_);
v___x_118_ = l_Lean_MessageData_toString(v___x_117_);
v___x_119_ = ((lean_object*)(l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0));
v___x_120_ = lean_string_append(v___x_119_, v___x_118_);
lean_dec_ref(v___x_118_);
v___x_121_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v___x_121_);
v___x_123_ = v___x_115_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___boxed(lean_object* v_00_u03b1_126_, lean_object* v_x_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Elab_Frontend_runCommandElabM(v_00_u03b1_126_, v_x_127_, v_a_128_, v_a_129_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object* v_stx_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v___x_136_; lean_object* v_fileName_137_; lean_object* v_fileMap_138_; lean_object* v_commandState_139_; lean_object* v_cmdPos_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_136_ = lean_st_ref_get(v_a_134_);
v_fileName_137_ = lean_ctor_get(v_a_133_, 1);
v_fileMap_138_ = lean_ctor_get(v_a_133_, 2);
v_commandState_139_ = lean_ctor_get(v___x_136_, 0);
lean_inc_ref(v_commandState_139_);
v_cmdPos_140_ = lean_ctor_get(v___x_136_, 2);
lean_inc(v_cmdPos_140_);
lean_dec(v___x_136_);
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_box(0);
v___x_143_ = lean_box(0);
v___x_144_ = l_Lean_firstFrontendMacroScope;
v___x_145_ = lean_box(0);
v___x_146_ = 0;
v___x_147_ = 0;
lean_inc_ref(v_fileMap_138_);
lean_inc_ref(v_fileName_137_);
v___x_148_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_148_, 0, v_fileName_137_);
lean_ctor_set(v___x_148_, 1, v_fileMap_138_);
lean_ctor_set(v___x_148_, 2, v___x_141_);
lean_ctor_set(v___x_148_, 3, v_cmdPos_140_);
lean_ctor_set(v___x_148_, 4, v___x_142_);
lean_ctor_set(v___x_148_, 5, v___x_143_);
lean_ctor_set(v___x_148_, 6, v___x_144_);
lean_ctor_set(v___x_148_, 7, v___x_145_);
lean_ctor_set(v___x_148_, 8, v___x_143_);
lean_ctor_set(v___x_148_, 9, v___x_143_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*10, v___x_146_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*10 + 1, v___x_147_);
v___x_149_ = lean_st_mk_ref(v_commandState_139_);
v___x_150_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_132_, v___x_148_, v___x_149_);
lean_dec_ref_known(v___x_148_, 10);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v___x_150_, 1);
v___x_152_ = lean_st_ref_get(v___x_149_);
lean_dec(v___x_149_);
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
lean_dec(v___x_149_);
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
lean_object* v_pos_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v_pos_189_ = lean_ctor_get(v_parserState_183_, 0);
lean_inc(v_pos_189_);
v___x_190_ = lean_box(0);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 2, v_pos_189_);
v___x_192_ = v___x_187_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_commandState_184_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_parserState_183_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_pos_189_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v_commands_185_);
v___x_192_ = v_reuseFailAlloc_195_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_st_ref_put(v_a_180_, v___x_192_);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_190_);
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
lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_251_ = lean_box(0);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v_ps_241_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_commandState_245_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_ps_241_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_cmdPos_246_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_commands_247_);
v___x_253_ = v_reuseFailAlloc_256_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_st_ref_put(v_a_242_, v___x_253_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_251_);
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
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = lean_box(0);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v_msgs_273_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
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
v___x_301_ = v_reuseFailAlloc_307_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_303_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_301_);
v___x_303_ = v___x_282_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_parserState_278_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_cmdPos_279_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v_commands_280_);
v___x_303_ = v_reuseFailAlloc_306_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_st_ref_put(v_a_274_, v___x_303_);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_299_);
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
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v___x_359_; lean_object* v_a_360_; lean_object* v_env_361_; lean_object* v_messages_362_; lean_object* v_scopes_363_; lean_object* v___x_364_; lean_object* v_opts_365_; lean_object* v_currNamespace_366_; lean_object* v_openDecls_367_; lean_object* v___x_368_; lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_snd_373_; lean_object* v_fst_374_; lean_object* v_fst_375_; lean_object* v_snd_376_; lean_object* v___x_377_; lean_object* v_commandState_378_; lean_object* v_parserState_379_; lean_object* v_cmdPos_380_; lean_object* v_commands_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_411_; 
v___x_355_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_356_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_353_);
lean_dec_ref(v___x_356_);
v___x_357_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_353_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
v___x_359_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_353_);
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref(v___x_359_);
v_env_361_ = lean_ctor_get(v_a_358_, 0);
lean_inc_ref(v_env_361_);
v_messages_362_ = lean_ctor_get(v_a_358_, 1);
lean_inc_ref(v_messages_362_);
v_scopes_363_ = lean_ctor_get(v_a_358_, 2);
lean_inc(v_scopes_363_);
lean_dec(v_a_358_);
v___x_364_ = l_List_head_x21___redArg(v___x_355_, v_scopes_363_);
lean_dec(v_scopes_363_);
v_opts_365_ = lean_ctor_get(v___x_364_, 1);
lean_inc_ref_n(v_opts_365_, 2);
v_currNamespace_366_ = lean_ctor_get(v___x_364_, 2);
lean_inc(v_currNamespace_366_);
v_openDecls_367_ = lean_ctor_get(v___x_364_, 3);
lean_inc(v_openDecls_367_);
lean_dec(v___x_364_);
v___x_368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_368_, 0, v_env_361_);
lean_ctor_set(v___x_368_, 1, v_opts_365_);
lean_ctor_set(v___x_368_, 2, v_currNamespace_366_);
lean_ctor_set(v___x_368_, 3, v_openDecls_367_);
lean_inc_ref(v_a_352_);
v___f_369_ = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommand___lam__0___boxed), 5, 4);
lean_closure_set(v___f_369_, 0, v_a_352_);
lean_closure_set(v___f_369_, 1, v___x_368_);
lean_closure_set(v___f_369_, 2, v_a_360_);
lean_closure_set(v___f_369_, 3, v_messages_362_);
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
lean_object* v___x_586_; lean_object* v___y_588_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; size_t v_sz_644_; size_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
lean_dec(v_nextCmdSnap_x3f_581_);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
lean_inc_ref(v_initialSnap_574_);
v___x_642_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_initialSnap_574_);
v___x_643_ = l_Lean_Language_SnapshotTree_getAll(v___x_642_);
v_sz_644_ = lean_array_size(v___x_643_);
v___x_645_ = ((size_t)0ULL);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_644_, v___x_645_, v___x_643_);
v___x_647_ = lean_array_get_size(v___x_646_);
v___x_648_ = lean_nat_dec_lt(v___x_586_, v___x_647_);
if (v___x_648_ == 0)
{
lean_dec_ref(v___x_646_);
v___y_588_ = v___x_641_;
goto v___jp_587_;
}
else
{
size_t v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_usize_of_nat(v___x_647_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v___x_646_, v___x_645_, v___x_649_, v___x_641_);
lean_dec_ref(v___x_646_);
v___y_588_ = v___x_650_;
goto v___jp_587_;
}
v___jp_587_:
{
size_t v_sz_589_; lean_object* v_resultSnap_590_; lean_object* v___x_591_; lean_object* v_cmdState_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_638_; 
v_sz_589_ = lean_array_size(v_commands_582_);
v_resultSnap_590_ = lean_ctor_get(v_elabSnap_580_, 2);
lean_inc_ref(v_resultSnap_590_);
lean_dec_ref(v_elabSnap_580_);
v___x_591_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_590_);
v_cmdState_592_ = lean_ctor_get(v___x_591_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; lean_object* v_unused_640_; 
v_unused_639_ = lean_ctor_get(v___x_591_, 2);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_640_);
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_638_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_cmdState_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_638_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_infoState_596_; lean_object* v_env_597_; lean_object* v_scopes_598_; lean_object* v_usedQuotCtxts_599_; lean_object* v_nextMacroScope_600_; lean_object* v_maxRecDepth_601_; lean_object* v_ngen_602_; lean_object* v_auxDeclNGen_603_; lean_object* v_traceState_604_; lean_object* v_snapshotTasks_605_; lean_object* v_prevLinterStates_606_; lean_object* v_codeQualityEntryTasks_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_636_; 
v_infoState_596_ = lean_ctor_get(v_cmdState_592_, 8);
v_env_597_ = lean_ctor_get(v_cmdState_592_, 0);
v_scopes_598_ = lean_ctor_get(v_cmdState_592_, 2);
v_usedQuotCtxts_599_ = lean_ctor_get(v_cmdState_592_, 3);
v_nextMacroScope_600_ = lean_ctor_get(v_cmdState_592_, 4);
v_maxRecDepth_601_ = lean_ctor_get(v_cmdState_592_, 5);
v_ngen_602_ = lean_ctor_get(v_cmdState_592_, 6);
v_auxDeclNGen_603_ = lean_ctor_get(v_cmdState_592_, 7);
v_traceState_604_ = lean_ctor_get(v_cmdState_592_, 9);
v_snapshotTasks_605_ = lean_ctor_get(v_cmdState_592_, 10);
v_prevLinterStates_606_ = lean_ctor_get(v_cmdState_592_, 11);
v_codeQualityEntryTasks_607_ = lean_ctor_get(v_cmdState_592_, 12);
v_isSharedCheck_636_ = !lean_is_exclusive(v_cmdState_592_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; 
v_unused_637_ = lean_ctor_get(v_cmdState_592_, 1);
lean_dec(v_unused_637_);
v___x_609_ = v_cmdState_592_;
v_isShared_610_ = v_isSharedCheck_636_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_codeQualityEntryTasks_607_);
lean_inc(v_prevLinterStates_606_);
lean_inc(v_snapshotTasks_605_);
lean_inc(v_traceState_604_);
lean_inc(v_infoState_596_);
lean_inc(v_auxDeclNGen_603_);
lean_inc(v_ngen_602_);
lean_inc(v_maxRecDepth_601_);
lean_inc(v_nextMacroScope_600_);
lean_inc(v_usedQuotCtxts_599_);
lean_inc(v_scopes_598_);
lean_inc(v_env_597_);
lean_dec(v_cmdState_592_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_636_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
uint8_t v_enabled_611_; lean_object* v_assignment_612_; lean_object* v_lazyAssignment_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_634_; 
v_enabled_611_ = lean_ctor_get_uint8(v_infoState_596_, sizeof(void*)*3);
v_assignment_612_ = lean_ctor_get(v_infoState_596_, 0);
v_lazyAssignment_613_ = lean_ctor_get(v_infoState_596_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_infoState_596_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; 
v_unused_635_ = lean_ctor_get(v_infoState_596_, 2);
lean_dec(v_unused_635_);
v___x_615_ = v_infoState_596_;
v_isShared_616_ = v_isSharedCheck_634_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_lazyAssignment_613_);
lean_inc(v_assignment_612_);
lean_dec(v_infoState_596_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_634_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v_pos_617_; size_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_trees_622_; lean_object* v___x_624_; 
v_pos_617_ = lean_ctor_get(v_parserState_579_, 0);
lean_inc(v_pos_617_);
v___x_618_ = ((size_t)0ULL);
lean_inc_ref(v_commands_582_);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_589_, v___x_618_, v_commands_582_);
v___x_620_ = lean_array_get_size(v___x_619_);
v___x_621_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v___x_619_, v___x_586_, v___x_620_);
lean_dec_ref(v___x_619_);
v_trees_622_ = l_Lean_Array_toPArray_x27___redArg(v___x_621_);
lean_dec_ref(v___x_621_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 2, v_trees_622_);
v___x_624_ = v___x_615_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_assignment_612_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_lazyAssignment_613_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_trees_622_);
lean_ctor_set_uint8(v_reuseFailAlloc_633_, sizeof(void*)*3, v_enabled_611_);
v___x_624_ = v_reuseFailAlloc_633_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 8, v___x_624_);
lean_ctor_set(v___x_609_, 1, v___y_588_);
v___x_626_ = v___x_609_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_env_597_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___y_588_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_scopes_598_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_usedQuotCtxts_599_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_nextMacroScope_600_);
lean_ctor_set(v_reuseFailAlloc_632_, 5, v_maxRecDepth_601_);
lean_ctor_set(v_reuseFailAlloc_632_, 6, v_ngen_602_);
lean_ctor_set(v_reuseFailAlloc_632_, 7, v_auxDeclNGen_603_);
lean_ctor_set(v_reuseFailAlloc_632_, 8, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_632_, 9, v_traceState_604_);
lean_ctor_set(v_reuseFailAlloc_632_, 10, v_snapshotTasks_605_);
lean_ctor_set(v_reuseFailAlloc_632_, 11, v_prevLinterStates_606_);
lean_ctor_set(v_reuseFailAlloc_632_, 12, v_codeQualityEntryTasks_607_);
v___x_626_ = v_reuseFailAlloc_632_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_589_, v___x_618_, v_commands_582_);
v___x_628_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v_parserState_579_);
lean_ctor_set(v___x_628_, 2, v_pos_617_);
lean_ctor_set(v___x_628_, 3, v___x_627_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 2, v_initialSnap_574_);
lean_ctor_set(v___x_594_, 1, v_inputCtx_573_);
lean_ctor_set(v___x_594_, 0, v___x_628_);
v___x_630_ = v___x_594_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_inputCtx_573_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_initialSnap_574_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(lean_object* v_cmdStx_x3f_740_, lean_object* v_as_741_, size_t v_i_742_, size_t v_stop_743_, lean_object* v_b_744_){
_start:
{
lean_object* v___y_746_; uint8_t v___x_750_; 
v___x_750_ = lean_usize_dec_eq(v_i_742_, v_stop_743_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v_stx_x3f_752_; lean_object* v___x_753_; 
v___x_751_ = lean_array_uget_borrowed(v_as_741_, v_i_742_);
v_stx_x3f_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v___x_751_);
v___x_753_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_751_);
if (lean_obj_tag(v_stx_x3f_752_) == 0)
{
lean_object* v___x_754_; 
lean_inc(v_cmdStx_x3f_740_);
v___x_754_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_753_, v_cmdStx_x3f_740_, v_b_744_);
v___y_746_ = v___x_754_;
goto v___jp_745_;
}
else
{
lean_object* v___x_755_; 
lean_inc_ref(v_stx_x3f_752_);
v___x_755_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_753_, v_stx_x3f_752_, v_b_744_);
v___y_746_ = v___x_755_;
goto v___jp_745_;
}
}
else
{
lean_dec(v_cmdStx_x3f_740_);
return v_b_744_;
}
v___jp_745_:
{
size_t v___x_747_; size_t v___x_748_; 
v___x_747_ = ((size_t)1ULL);
v___x_748_ = lean_usize_add(v_i_742_, v___x_747_);
v_i_742_ = v___x_748_;
v_b_744_ = v___y_746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(lean_object* v_t_756_, lean_object* v_cmdStx_x3f_757_, lean_object* v_acc_758_){
_start:
{
lean_object* v_element_759_; lean_object* v_diagnostics_760_; lean_object* v_children_761_; lean_object* v_msgLog_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_776_; 
v_element_759_ = lean_ctor_get(v_t_756_, 0);
v_diagnostics_760_ = lean_ctor_get(v_element_759_, 1);
lean_inc_ref(v_diagnostics_760_);
v_children_761_ = lean_ctor_get(v_t_756_, 1);
lean_inc_ref(v_children_761_);
lean_dec_ref(v_t_756_);
v_msgLog_762_ = lean_ctor_get(v_diagnostics_760_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v_diagnostics_760_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v_diagnostics_760_, 1);
lean_dec(v_unused_777_);
v___x_764_ = v_diagnostics_760_;
v_isShared_765_ = v_isSharedCheck_776_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_msgLog_762_);
lean_dec(v_diagnostics_760_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_776_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
lean_inc(v_cmdStx_x3f_757_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 1, v_msgLog_762_);
lean_ctor_set(v___x_764_, 0, v_cmdStx_x3f_757_);
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_cmdStx_x3f_757_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_msgLog_762_);
v___x_767_ = v_reuseFailAlloc_775_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v_acc_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_acc_768_ = lean_array_push(v_acc_758_, v___x_767_);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_array_get_size(v_children_761_);
v___x_771_ = lean_nat_dec_lt(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_dec_ref(v_children_761_);
lean_dec(v_cmdStx_x3f_757_);
return v_acc_768_;
}
else
{
size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((size_t)0ULL);
v___x_773_ = lean_usize_of_nat(v___x_770_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_757_, v_children_761_, v___x_772_, v___x_773_, v_acc_768_);
lean_dec_ref(v_children_761_);
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0___boxed(lean_object* v_cmdStx_x3f_778_, lean_object* v_as_779_, lean_object* v_i_780_, lean_object* v_stop_781_, lean_object* v_b_782_){
_start:
{
size_t v_i_boxed_783_; size_t v_stop_boxed_784_; lean_object* v_res_785_; 
v_i_boxed_783_ = lean_unbox_usize(v_i_780_);
lean_dec(v_i_780_);
v_stop_boxed_784_ = lean_unbox_usize(v_stop_781_);
lean_dec(v_stop_781_);
v_res_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_778_, v_as_779_, v_i_boxed_783_, v_stop_boxed_784_, v_b_782_);
lean_dec_ref(v_as_779_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3(lean_object* v_filePath_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_lean_x3f_788_; lean_object* v_olean_x3f_789_; lean_object* v_oleanServer_x3f_790_; lean_object* v_ilean_x3f_791_; lean_object* v_irSig_x3f_792_; lean_object* v_ir_x3f_793_; lean_object* v_c_x3f_794_; lean_object* v_bc_x3f_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_803_; 
v_lean_x3f_788_ = lean_ctor_get(v_a_787_, 0);
v_olean_x3f_789_ = lean_ctor_get(v_a_787_, 1);
v_oleanServer_x3f_790_ = lean_ctor_get(v_a_787_, 2);
v_ilean_x3f_791_ = lean_ctor_get(v_a_787_, 4);
v_irSig_x3f_792_ = lean_ctor_get(v_a_787_, 5);
v_ir_x3f_793_ = lean_ctor_get(v_a_787_, 6);
v_c_x3f_794_ = lean_ctor_get(v_a_787_, 7);
v_bc_x3f_795_ = lean_ctor_get(v_a_787_, 8);
v_isSharedCheck_803_ = !lean_is_exclusive(v_a_787_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v_a_787_, 3);
lean_dec(v_unused_804_);
v___x_797_ = v_a_787_;
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_bc_x3f_795_);
lean_inc(v_c_x3f_794_);
lean_inc(v_ir_x3f_793_);
lean_inc(v_irSig_x3f_792_);
lean_inc(v_ilean_x3f_791_);
lean_inc(v_oleanServer_x3f_790_);
lean_inc(v_olean_x3f_789_);
lean_inc(v_lean_x3f_788_);
lean_dec(v_a_787_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v_filePath_786_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 3, v___x_799_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_lean_x3f_788_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_olean_x3f_789_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_oleanServer_x3f_790_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_802_, 4, v_ilean_x3f_791_);
lean_ctor_set(v_reuseFailAlloc_802_, 5, v_irSig_x3f_792_);
lean_ctor_set(v_reuseFailAlloc_802_, 6, v_ir_x3f_793_);
lean_ctor_set(v_reuseFailAlloc_802_, 7, v_c_x3f_794_);
lean_ctor_set(v_reuseFailAlloc_802_, 8, v_bc_x3f_795_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1(lean_object* v_filePath_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_lean_x3f_807_; lean_object* v_olean_x3f_808_; lean_object* v_oleanServer_x3f_809_; lean_object* v_oleanPrivate_x3f_810_; lean_object* v_ilean_x3f_811_; lean_object* v_ir_x3f_812_; lean_object* v_c_x3f_813_; lean_object* v_bc_x3f_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_822_; 
v_lean_x3f_807_ = lean_ctor_get(v_a_806_, 0);
v_olean_x3f_808_ = lean_ctor_get(v_a_806_, 1);
v_oleanServer_x3f_809_ = lean_ctor_get(v_a_806_, 2);
v_oleanPrivate_x3f_810_ = lean_ctor_get(v_a_806_, 3);
v_ilean_x3f_811_ = lean_ctor_get(v_a_806_, 4);
v_ir_x3f_812_ = lean_ctor_get(v_a_806_, 6);
v_c_x3f_813_ = lean_ctor_get(v_a_806_, 7);
v_bc_x3f_814_ = lean_ctor_get(v_a_806_, 8);
v_isSharedCheck_822_ = !lean_is_exclusive(v_a_806_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_a_806_, 5);
lean_dec(v_unused_823_);
v___x_816_ = v_a_806_;
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_bc_x3f_814_);
lean_inc(v_c_x3f_813_);
lean_inc(v_ir_x3f_812_);
lean_inc(v_ilean_x3f_811_);
lean_inc(v_oleanPrivate_x3f_810_);
lean_inc(v_oleanServer_x3f_809_);
lean_inc(v_olean_x3f_808_);
lean_inc(v_lean_x3f_807_);
lean_dec(v_a_806_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v_filePath_805_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 5, v___x_818_);
v___x_820_ = v___x_816_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_lean_x3f_807_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_olean_x3f_808_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_oleanServer_x3f_809_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v_oleanPrivate_x3f_810_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_ilean_x3f_811_);
lean_ctor_set(v_reuseFailAlloc_821_, 5, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_821_, 6, v_ir_x3f_812_);
lean_ctor_set(v_reuseFailAlloc_821_, 7, v_c_x3f_813_);
lean_ctor_set(v_reuseFailAlloc_821_, 8, v_bc_x3f_814_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4(lean_object* v_filePath_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_lean_x3f_826_; lean_object* v_olean_x3f_827_; lean_object* v_oleanPrivate_x3f_828_; lean_object* v_ilean_x3f_829_; lean_object* v_irSig_x3f_830_; lean_object* v_ir_x3f_831_; lean_object* v_c_x3f_832_; lean_object* v_bc_x3f_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_841_; 
v_lean_x3f_826_ = lean_ctor_get(v_a_825_, 0);
v_olean_x3f_827_ = lean_ctor_get(v_a_825_, 1);
v_oleanPrivate_x3f_828_ = lean_ctor_get(v_a_825_, 3);
v_ilean_x3f_829_ = lean_ctor_get(v_a_825_, 4);
v_irSig_x3f_830_ = lean_ctor_get(v_a_825_, 5);
v_ir_x3f_831_ = lean_ctor_get(v_a_825_, 6);
v_c_x3f_832_ = lean_ctor_get(v_a_825_, 7);
v_bc_x3f_833_ = lean_ctor_get(v_a_825_, 8);
v_isSharedCheck_841_ = !lean_is_exclusive(v_a_825_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v_a_825_, 2);
lean_dec(v_unused_842_);
v___x_835_ = v_a_825_;
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_bc_x3f_833_);
lean_inc(v_c_x3f_832_);
lean_inc(v_ir_x3f_831_);
lean_inc(v_irSig_x3f_830_);
lean_inc(v_ilean_x3f_829_);
lean_inc(v_oleanPrivate_x3f_828_);
lean_inc(v_olean_x3f_827_);
lean_inc(v_lean_x3f_826_);
lean_dec(v_a_825_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_837_, 0, v_filePath_824_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 2, v___x_837_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_lean_x3f_826_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_olean_x3f_827_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_oleanPrivate_x3f_828_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v_ilean_x3f_829_);
lean_ctor_set(v_reuseFailAlloc_840_, 5, v_irSig_x3f_830_);
lean_ctor_set(v_reuseFailAlloc_840_, 6, v_ir_x3f_831_);
lean_ctor_set(v_reuseFailAlloc_840_, 7, v_c_x3f_832_);
lean_ctor_set(v_reuseFailAlloc_840_, 8, v_bc_x3f_833_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(lean_object* v_a_843_, lean_object* v_x_844_){
_start:
{
if (lean_obj_tag(v_x_844_) == 0)
{
uint8_t v___x_845_; 
v___x_845_ = 0;
return v___x_845_;
}
else
{
lean_object* v_key_846_; lean_object* v_tail_847_; uint8_t v___x_848_; 
v_key_846_ = lean_ctor_get(v_x_844_, 0);
v_tail_847_ = lean_ctor_get(v_x_844_, 2);
v___x_848_ = lean_string_dec_eq(v_key_846_, v_a_843_);
if (v___x_848_ == 0)
{
v_x_844_ = v_tail_847_;
goto _start;
}
else
{
return v___x_848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg___boxed(lean_object* v_a_850_, lean_object* v_x_851_){
_start:
{
uint8_t v_res_852_; lean_object* v_r_853_; 
v_res_852_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_850_, v_x_851_);
lean_dec(v_x_851_);
lean_dec_ref(v_a_850_);
v_r_853_ = lean_box(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(lean_object* v_m_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_buckets_856_; lean_object* v___x_857_; uint64_t v___x_858_; uint64_t v___x_859_; uint64_t v___x_860_; uint64_t v_fold_861_; uint64_t v___x_862_; uint64_t v___x_863_; uint64_t v___x_864_; size_t v___x_865_; size_t v___x_866_; size_t v___x_867_; size_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_buckets_856_ = lean_ctor_get(v_m_854_, 1);
v___x_857_ = lean_array_get_size(v_buckets_856_);
v___x_858_ = lean_string_hash(v_a_855_);
v___x_859_ = 32ULL;
v___x_860_ = lean_uint64_shift_right(v___x_858_, v___x_859_);
v_fold_861_ = lean_uint64_xor(v___x_858_, v___x_860_);
v___x_862_ = 16ULL;
v___x_863_ = lean_uint64_shift_right(v_fold_861_, v___x_862_);
v___x_864_ = lean_uint64_xor(v_fold_861_, v___x_863_);
v___x_865_ = lean_uint64_to_usize(v___x_864_);
v___x_866_ = lean_usize_of_nat(v___x_857_);
v___x_867_ = ((size_t)1ULL);
v___x_868_ = lean_usize_sub(v___x_866_, v___x_867_);
v___x_869_ = lean_usize_land(v___x_865_, v___x_868_);
v___x_870_ = lean_array_uget_borrowed(v_buckets_856_, v___x_869_);
v___x_871_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_855_, v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg___boxed(lean_object* v_m_872_, lean_object* v_a_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_872_, v_a_873_);
lean_dec_ref(v_a_873_);
lean_dec_ref(v_m_872_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(lean_object* v_a_876_, lean_object* v_fallback_877_, lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
lean_inc(v_fallback_877_);
return v_fallback_877_;
}
else
{
lean_object* v_key_879_; lean_object* v_value_880_; lean_object* v_tail_881_; uint8_t v___x_882_; 
v_key_879_ = lean_ctor_get(v_x_878_, 0);
v_value_880_ = lean_ctor_get(v_x_878_, 1);
v_tail_881_ = lean_ctor_get(v_x_878_, 2);
v___x_882_ = lean_string_dec_eq(v_key_879_, v_a_876_);
if (v___x_882_ == 0)
{
v_x_878_ = v_tail_881_;
goto _start;
}
else
{
lean_inc(v_value_880_);
return v_value_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg___boxed(lean_object* v_a_884_, lean_object* v_fallback_885_, lean_object* v_x_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_884_, v_fallback_885_, v_x_886_);
lean_dec(v_x_886_);
lean_dec(v_fallback_885_);
lean_dec_ref(v_a_884_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(lean_object* v_m_888_, lean_object* v_a_889_, lean_object* v_fallback_890_){
_start:
{
lean_object* v_buckets_891_; lean_object* v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v___x_895_; uint64_t v_fold_896_; uint64_t v___x_897_; uint64_t v___x_898_; uint64_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; size_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_buckets_891_ = lean_ctor_get(v_m_888_, 1);
v___x_892_ = lean_array_get_size(v_buckets_891_);
v___x_893_ = lean_string_hash(v_a_889_);
v___x_894_ = 32ULL;
v___x_895_ = lean_uint64_shift_right(v___x_893_, v___x_894_);
v_fold_896_ = lean_uint64_xor(v___x_893_, v___x_895_);
v___x_897_ = 16ULL;
v___x_898_ = lean_uint64_shift_right(v_fold_896_, v___x_897_);
v___x_899_ = lean_uint64_xor(v_fold_896_, v___x_898_);
v___x_900_ = lean_uint64_to_usize(v___x_899_);
v___x_901_ = lean_usize_of_nat(v___x_892_);
v___x_902_ = ((size_t)1ULL);
v___x_903_ = lean_usize_sub(v___x_901_, v___x_902_);
v___x_904_ = lean_usize_land(v___x_900_, v___x_903_);
v___x_905_ = lean_array_uget_borrowed(v_buckets_891_, v___x_904_);
v___x_906_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_889_, v_fallback_890_, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg___boxed(lean_object* v_m_907_, lean_object* v_a_908_, lean_object* v_fallback_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_907_, v_a_908_, v_fallback_909_);
lean_dec(v_fallback_909_);
lean_dec_ref(v_a_908_);
lean_dec_ref(v_m_907_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2(lean_object* v_filePath_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_lean_x3f_913_; lean_object* v_olean_x3f_914_; lean_object* v_oleanServer_x3f_915_; lean_object* v_oleanPrivate_x3f_916_; lean_object* v_ilean_x3f_917_; lean_object* v_irSig_x3f_918_; lean_object* v_c_x3f_919_; lean_object* v_bc_x3f_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_928_; 
v_lean_x3f_913_ = lean_ctor_get(v_a_912_, 0);
v_olean_x3f_914_ = lean_ctor_get(v_a_912_, 1);
v_oleanServer_x3f_915_ = lean_ctor_get(v_a_912_, 2);
v_oleanPrivate_x3f_916_ = lean_ctor_get(v_a_912_, 3);
v_ilean_x3f_917_ = lean_ctor_get(v_a_912_, 4);
v_irSig_x3f_918_ = lean_ctor_get(v_a_912_, 5);
v_c_x3f_919_ = lean_ctor_get(v_a_912_, 7);
v_bc_x3f_920_ = lean_ctor_get(v_a_912_, 8);
v_isSharedCheck_928_ = !lean_is_exclusive(v_a_912_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v_a_912_, 6);
lean_dec(v_unused_929_);
v___x_922_ = v_a_912_;
v_isShared_923_ = v_isSharedCheck_928_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_bc_x3f_920_);
lean_inc(v_c_x3f_919_);
lean_inc(v_irSig_x3f_918_);
lean_inc(v_ilean_x3f_917_);
lean_inc(v_oleanPrivate_x3f_916_);
lean_inc(v_oleanServer_x3f_915_);
lean_inc(v_olean_x3f_914_);
lean_inc(v_lean_x3f_913_);
lean_dec(v_a_912_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_928_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_924_, 0, v_filePath_911_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 6, v___x_924_);
v___x_926_ = v___x_922_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_lean_x3f_913_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_olean_x3f_914_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_oleanServer_x3f_915_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_oleanPrivate_x3f_916_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v_ilean_x3f_917_);
lean_ctor_set(v_reuseFailAlloc_927_, 5, v_irSig_x3f_918_);
lean_ctor_set(v_reuseFailAlloc_927_, 6, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_927_, 7, v_c_x3f_919_);
lean_ctor_set(v_reuseFailAlloc_927_, 8, v_bc_x3f_920_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0(lean_object* v_filePath_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_lean_x3f_932_; lean_object* v_oleanServer_x3f_933_; lean_object* v_oleanPrivate_x3f_934_; lean_object* v_ilean_x3f_935_; lean_object* v_irSig_x3f_936_; lean_object* v_ir_x3f_937_; lean_object* v_c_x3f_938_; lean_object* v_bc_x3f_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_947_; 
v_lean_x3f_932_ = lean_ctor_get(v_a_931_, 0);
v_oleanServer_x3f_933_ = lean_ctor_get(v_a_931_, 2);
v_oleanPrivate_x3f_934_ = lean_ctor_get(v_a_931_, 3);
v_ilean_x3f_935_ = lean_ctor_get(v_a_931_, 4);
v_irSig_x3f_936_ = lean_ctor_get(v_a_931_, 5);
v_ir_x3f_937_ = lean_ctor_get(v_a_931_, 6);
v_c_x3f_938_ = lean_ctor_get(v_a_931_, 7);
v_bc_x3f_939_ = lean_ctor_get(v_a_931_, 8);
v_isSharedCheck_947_ = !lean_is_exclusive(v_a_931_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v_a_931_, 1);
lean_dec(v_unused_948_);
v___x_941_ = v_a_931_;
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_bc_x3f_939_);
lean_inc(v_c_x3f_938_);
lean_inc(v_ir_x3f_937_);
lean_inc(v_irSig_x3f_936_);
lean_inc(v_ilean_x3f_935_);
lean_inc(v_oleanPrivate_x3f_934_);
lean_inc(v_oleanServer_x3f_933_);
lean_inc(v_lean_x3f_932_);
lean_dec(v_a_931_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v_filePath_930_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_lean_x3f_932_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_oleanServer_x3f_933_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_oleanPrivate_x3f_934_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v_ilean_x3f_935_);
lean_ctor_set(v_reuseFailAlloc_946_, 5, v_irSig_x3f_936_);
lean_ctor_set(v_reuseFailAlloc_946_, 6, v_ir_x3f_937_);
lean_ctor_set(v_reuseFailAlloc_946_, 7, v_c_x3f_938_);
lean_ctor_set(v_reuseFailAlloc_946_, 8, v_bc_x3f_939_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(lean_object* v_a_949_, lean_object* v_b_950_, lean_object* v_x_951_){
_start:
{
if (lean_obj_tag(v_x_951_) == 0)
{
lean_dec(v_b_950_);
lean_dec_ref(v_a_949_);
return v_x_951_;
}
else
{
lean_object* v_key_952_; lean_object* v_value_953_; lean_object* v_tail_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_966_; 
v_key_952_ = lean_ctor_get(v_x_951_, 0);
v_value_953_ = lean_ctor_get(v_x_951_, 1);
v_tail_954_ = lean_ctor_get(v_x_951_, 2);
v_isSharedCheck_966_ = !lean_is_exclusive(v_x_951_);
if (v_isSharedCheck_966_ == 0)
{
v___x_956_ = v_x_951_;
v_isShared_957_ = v_isSharedCheck_966_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_tail_954_);
lean_inc(v_value_953_);
lean_inc(v_key_952_);
lean_dec(v_x_951_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_966_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
uint8_t v___x_958_; 
v___x_958_ = lean_string_dec_eq(v_key_952_, v_a_949_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_949_, v_b_950_, v_tail_954_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 2, v___x_959_);
v___x_961_ = v___x_956_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_key_952_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_value_953_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
else
{
lean_object* v___x_964_; 
lean_dec(v_value_953_);
lean_dec(v_key_952_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v_b_950_);
lean_ctor_set(v___x_956_, 0, v_a_949_);
v___x_964_ = v___x_956_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_949_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_b_950_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_tail_954_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(lean_object* v_x_967_, lean_object* v_x_968_){
_start:
{
if (lean_obj_tag(v_x_968_) == 0)
{
return v_x_967_;
}
else
{
lean_object* v_key_969_; lean_object* v_value_970_; lean_object* v_tail_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_994_; 
v_key_969_ = lean_ctor_get(v_x_968_, 0);
v_value_970_ = lean_ctor_get(v_x_968_, 1);
v_tail_971_ = lean_ctor_get(v_x_968_, 2);
v_isSharedCheck_994_ = !lean_is_exclusive(v_x_968_);
if (v_isSharedCheck_994_ == 0)
{
v___x_973_ = v_x_968_;
v_isShared_974_ = v_isSharedCheck_994_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_tail_971_);
lean_inc(v_value_970_);
lean_inc(v_key_969_);
lean_dec(v_x_968_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_994_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_975_; uint64_t v___x_976_; uint64_t v___x_977_; uint64_t v___x_978_; uint64_t v_fold_979_; uint64_t v___x_980_; uint64_t v___x_981_; uint64_t v___x_982_; size_t v___x_983_; size_t v___x_984_; size_t v___x_985_; size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_975_ = lean_array_get_size(v_x_967_);
v___x_976_ = lean_string_hash(v_key_969_);
v___x_977_ = 32ULL;
v___x_978_ = lean_uint64_shift_right(v___x_976_, v___x_977_);
v_fold_979_ = lean_uint64_xor(v___x_976_, v___x_978_);
v___x_980_ = 16ULL;
v___x_981_ = lean_uint64_shift_right(v_fold_979_, v___x_980_);
v___x_982_ = lean_uint64_xor(v_fold_979_, v___x_981_);
v___x_983_ = lean_uint64_to_usize(v___x_982_);
v___x_984_ = lean_usize_of_nat(v___x_975_);
v___x_985_ = ((size_t)1ULL);
v___x_986_ = lean_usize_sub(v___x_984_, v___x_985_);
v___x_987_ = lean_usize_land(v___x_983_, v___x_986_);
v___x_988_ = lean_array_uget_borrowed(v_x_967_, v___x_987_);
lean_inc(v___x_988_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 2, v___x_988_);
v___x_990_ = v___x_973_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_key_969_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_value_970_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v___x_988_);
v___x_990_ = v_reuseFailAlloc_993_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; 
v___x_991_ = lean_array_uset(v_x_967_, v___x_987_, v___x_990_);
v_x_967_ = v___x_991_;
v_x_968_ = v_tail_971_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(lean_object* v_i_995_, lean_object* v_source_996_, lean_object* v_target_997_){
_start:
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = lean_array_get_size(v_source_996_);
v___x_999_ = lean_nat_dec_lt(v_i_995_, v___x_998_);
if (v___x_999_ == 0)
{
lean_dec_ref(v_source_996_);
lean_dec(v_i_995_);
return v_target_997_;
}
else
{
lean_object* v_es_1000_; lean_object* v___x_1001_; lean_object* v_source_1002_; lean_object* v_target_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_es_1000_ = lean_array_fget(v_source_996_, v_i_995_);
v___x_1001_ = lean_box(0);
v_source_1002_ = lean_array_fset(v_source_996_, v_i_995_, v___x_1001_);
v_target_1003_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_target_997_, v_es_1000_);
v___x_1004_ = lean_unsigned_to_nat(1u);
v___x_1005_ = lean_nat_add(v_i_995_, v___x_1004_);
lean_dec(v_i_995_);
v_i_995_ = v___x_1005_;
v_source_996_ = v_source_1002_;
v_target_997_ = v_target_1003_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(lean_object* v_data_1007_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_nbuckets_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1008_ = lean_array_get_size(v_data_1007_);
v___x_1009_ = lean_unsigned_to_nat(2u);
v_nbuckets_1010_ = lean_nat_mul(v___x_1008_, v___x_1009_);
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_mk_array(v_nbuckets_1010_, v___x_1012_);
v___x_1014_ = lean_array_propagate_mark(v_data_1007_, v___x_1013_);
v___x_1015_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v___x_1011_, v_data_1007_, v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object* v_m_1016_, lean_object* v_a_1017_, lean_object* v_b_1018_){
_start:
{
lean_object* v_size_1019_; lean_object* v_buckets_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1063_; 
v_size_1019_ = lean_ctor_get(v_m_1016_, 0);
v_buckets_1020_ = lean_ctor_get(v_m_1016_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_m_1016_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1022_ = v_m_1016_;
v_isShared_1023_ = v_isSharedCheck_1063_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_buckets_1020_);
lean_inc(v_size_1019_);
lean_dec(v_m_1016_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1063_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; uint64_t v___x_1025_; uint64_t v___x_1026_; uint64_t v___x_1027_; uint64_t v_fold_1028_; uint64_t v___x_1029_; uint64_t v___x_1030_; uint64_t v___x_1031_; size_t v___x_1032_; size_t v___x_1033_; size_t v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; lean_object* v_bkt_1037_; uint8_t v___x_1038_; 
v___x_1024_ = lean_array_get_size(v_buckets_1020_);
v___x_1025_ = lean_string_hash(v_a_1017_);
v___x_1026_ = 32ULL;
v___x_1027_ = lean_uint64_shift_right(v___x_1025_, v___x_1026_);
v_fold_1028_ = lean_uint64_xor(v___x_1025_, v___x_1027_);
v___x_1029_ = 16ULL;
v___x_1030_ = lean_uint64_shift_right(v_fold_1028_, v___x_1029_);
v___x_1031_ = lean_uint64_xor(v_fold_1028_, v___x_1030_);
v___x_1032_ = lean_uint64_to_usize(v___x_1031_);
v___x_1033_ = lean_usize_of_nat(v___x_1024_);
v___x_1034_ = ((size_t)1ULL);
v___x_1035_ = lean_usize_sub(v___x_1033_, v___x_1034_);
v___x_1036_ = lean_usize_land(v___x_1032_, v___x_1035_);
v_bkt_1037_ = lean_array_uget_borrowed(v_buckets_1020_, v___x_1036_);
v___x_1038_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1017_, v_bkt_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v_size_x27_1040_; lean_object* v___x_1041_; lean_object* v_buckets_x27_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v___x_1039_ = lean_unsigned_to_nat(1u);
v_size_x27_1040_ = lean_nat_add(v_size_1019_, v___x_1039_);
lean_dec(v_size_1019_);
lean_inc(v_bkt_1037_);
v___x_1041_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1041_, 0, v_a_1017_);
lean_ctor_set(v___x_1041_, 1, v_b_1018_);
lean_ctor_set(v___x_1041_, 2, v_bkt_1037_);
v_buckets_x27_1042_ = lean_array_uset(v_buckets_1020_, v___x_1036_, v___x_1041_);
v___x_1043_ = lean_unsigned_to_nat(4u);
v___x_1044_ = lean_nat_mul(v_size_x27_1040_, v___x_1043_);
v___x_1045_ = lean_unsigned_to_nat(3u);
v___x_1046_ = lean_nat_div(v___x_1044_, v___x_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_array_get_size(v_buckets_x27_1042_);
v___x_1048_ = lean_nat_dec_le(v___x_1046_, v___x_1047_);
lean_dec(v___x_1046_);
if (v___x_1048_ == 0)
{
lean_object* v_val_1049_; lean_object* v___x_1051_; 
v_val_1049_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_buckets_x27_1042_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 1, v_val_1049_);
lean_ctor_set(v___x_1022_, 0, v_size_x27_1040_);
v___x_1051_ = v___x_1022_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_size_x27_1040_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_val_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
else
{
lean_object* v___x_1054_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 1, v_buckets_x27_1042_);
lean_ctor_set(v___x_1022_, 0, v_size_x27_1040_);
v___x_1054_ = v___x_1022_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_size_x27_1040_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_buckets_x27_1042_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
else
{
lean_object* v___x_1056_; lean_object* v_buckets_x27_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_inc(v_bkt_1037_);
v___x_1056_ = lean_box(0);
v_buckets_x27_1057_ = lean_array_uset(v_buckets_1020_, v___x_1036_, v___x_1056_);
v___x_1058_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1017_, v_b_1018_, v_bkt_1037_);
v___x_1059_ = lean_array_uset(v_buckets_x27_1057_, v___x_1036_, v___x_1058_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 1, v___x_1059_);
v___x_1061_ = v___x_1022_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_size_1019_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object* v_as_1072_, size_t v_sz_1073_, size_t v_i_1074_, lean_object* v_b_1075_){
_start:
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_usize_dec_lt(v_i_1074_, v_sz_1073_);
if (v___x_1076_ == 0)
{
return v_b_1075_;
}
else
{
lean_object* v_fst_1077_; lean_object* v_snd_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1128_; 
v_fst_1077_ = lean_ctor_get(v_b_1075_, 0);
v_snd_1078_ = lean_ctor_get(v_b_1075_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_b_1075_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1080_ = v_b_1075_;
v_isShared_1081_ = v_isSharedCheck_1128_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_snd_1078_);
lean_inc(v_fst_1077_);
lean_dec(v_b_1075_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1128_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v_order_1085_; lean_object* v_fst_1097_; lean_object* v_snd_1098_; lean_object* v_a_1101_; lean_object* v_filePath_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; 
v_a_1101_ = lean_array_uget_borrowed(v_as_1072_, v_i_1074_);
v_filePath_1102_ = lean_ctor_get(v_a_1101_, 0);
lean_inc_ref_n(v_filePath_1102_, 2);
v___f_1103_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1103_, 0, v_filePath_1102_);
v___x_1104_ = l_System_FilePath_extension(v_filePath_1102_);
if (lean_obj_tag(v___x_1104_) == 1)
{
lean_object* v_val_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_val_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_val_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1));
v___x_1107_ = lean_string_dec_eq(v_val_1105_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2));
v___x_1109_ = lean_string_dec_eq(v_val_1105_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3));
v___x_1111_ = lean_string_dec_eq(v_val_1105_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4));
v___x_1113_ = lean_string_dec_eq(v_val_1105_, v___x_1112_);
lean_dec(v_val_1105_);
if (v___x_1113_ == 0)
{
lean_inc_ref(v_filePath_1102_);
v_fst_1097_ = v_filePath_1102_;
v_snd_1098_ = v___f_1103_;
goto v___jp_1096_;
}
else
{
lean_object* v___f_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec_ref(v___f_1103_);
lean_inc_ref_n(v_filePath_1102_, 2);
v___f_1114_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1), 2, 1);
lean_closure_set(v___f_1114_, 0, v_filePath_1102_);
v___x_1115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1116_ = l_System_FilePath_withExtension(v_filePath_1102_, v___x_1115_);
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1118_ = l_System_FilePath_withExtension(v___x_1116_, v___x_1117_);
v_fst_1097_ = v___x_1118_;
v_snd_1098_ = v___f_1114_;
goto v___jp_1096_;
}
}
else
{
lean_object* v___f_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec(v_val_1105_);
lean_dec_ref(v___f_1103_);
lean_inc_ref_n(v_filePath_1102_, 2);
v___f_1119_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2), 2, 1);
lean_closure_set(v___f_1119_, 0, v_filePath_1102_);
v___x_1120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1121_ = l_System_FilePath_withExtension(v_filePath_1102_, v___x_1120_);
v_fst_1097_ = v___x_1121_;
v_snd_1098_ = v___f_1119_;
goto v___jp_1096_;
}
}
else
{
lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_dec(v_val_1105_);
lean_dec_ref(v___f_1103_);
lean_inc_ref_n(v_filePath_1102_, 2);
v___f_1122_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3), 2, 1);
lean_closure_set(v___f_1122_, 0, v_filePath_1102_);
v___x_1123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1124_ = l_System_FilePath_withExtension(v_filePath_1102_, v___x_1123_);
v_fst_1097_ = v___x_1124_;
v_snd_1098_ = v___f_1122_;
goto v___jp_1096_;
}
}
else
{
lean_object* v___f_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec(v_val_1105_);
lean_dec_ref(v___f_1103_);
lean_inc_ref_n(v_filePath_1102_, 2);
v___f_1125_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4), 2, 1);
lean_closure_set(v___f_1125_, 0, v_filePath_1102_);
v___x_1126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1127_ = l_System_FilePath_withExtension(v_filePath_1102_, v___x_1126_);
v_fst_1097_ = v___x_1127_;
v_snd_1098_ = v___f_1125_;
goto v___jp_1096_;
}
}
else
{
lean_dec(v___x_1104_);
lean_inc_ref(v_filePath_1102_);
v_fst_1097_ = v_filePath_1102_;
v_snd_1098_ = v___f_1103_;
goto v___jp_1096_;
}
v___jp_1082_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0));
v___x_1087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_snd_1078_, v___y_1084_, v___x_1086_);
v___x_1088_ = lean_apply_1(v___y_1083_, v___x_1087_);
v___x_1089_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_snd_1078_, v___y_1084_, v___x_1088_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___x_1089_);
lean_ctor_set(v___x_1080_, 0, v_order_1085_);
v___x_1091_ = v___x_1080_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_order_1085_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
size_t v___x_1092_; size_t v___x_1093_; 
v___x_1092_ = ((size_t)1ULL);
v___x_1093_ = lean_usize_add(v_i_1074_, v___x_1092_);
v_i_1074_ = v___x_1093_;
v_b_1075_ = v___x_1091_;
goto _start;
}
}
v___jp_1096_:
{
uint8_t v___x_1099_; 
v___x_1099_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1078_, v_fst_1097_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_inc_ref(v_fst_1097_);
v___x_1100_ = lean_array_push(v_fst_1077_, v_fst_1097_);
v___y_1083_ = v_snd_1098_;
v___y_1084_ = v_fst_1097_;
v_order_1085_ = v___x_1100_;
goto v___jp_1082_;
}
else
{
v___y_1083_ = v_snd_1098_;
v___y_1084_ = v_fst_1097_;
v_order_1085_ = v_fst_1077_;
goto v___jp_1082_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object* v_as_1129_, lean_object* v_sz_1130_, lean_object* v_i_1131_, lean_object* v_b_1132_){
_start:
{
size_t v_sz_boxed_1133_; size_t v_i_boxed_1134_; lean_object* v_res_1135_; 
v_sz_boxed_1133_ = lean_unbox_usize(v_sz_1130_);
lean_dec(v_sz_1130_);
v_i_boxed_1134_ = lean_unbox_usize(v_i_1131_);
lean_dec(v_i_1131_);
v_res_1135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_as_1129_, v_sz_boxed_1133_, v_i_boxed_1134_, v_b_1132_);
lean_dec_ref(v_as_1129_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(lean_object* v_msg_1136_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1138_ = lean_panic_fn_borrowed(v___x_1137_, v_msg_1136_);
return v___x_1138_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1142_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2));
v___x_1143_ = lean_unsigned_to_nat(11u);
v___x_1144_ = lean_unsigned_to_nat(163u);
v___x_1145_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1));
v___x_1146_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0));
v___x_1147_ = l_mkPanicMessageWithDecl(v___x_1146_, v___x_1145_, v___x_1144_, v___x_1143_, v___x_1142_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(lean_object* v_a_1148_, lean_object* v_x_1149_){
_start:
{
if (lean_obj_tag(v_x_1149_) == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3);
v___x_1151_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(v___x_1150_);
return v___x_1151_;
}
else
{
lean_object* v_key_1152_; lean_object* v_value_1153_; lean_object* v_tail_1154_; uint8_t v___x_1155_; 
v_key_1152_ = lean_ctor_get(v_x_1149_, 0);
v_value_1153_ = lean_ctor_get(v_x_1149_, 1);
v_tail_1154_ = lean_ctor_get(v_x_1149_, 2);
v___x_1155_ = lean_string_dec_eq(v_key_1152_, v_a_1148_);
if (v___x_1155_ == 0)
{
v_x_1149_ = v_tail_1154_;
goto _start;
}
else
{
lean_inc(v_value_1153_);
return v_value_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___boxed(lean_object* v_a_1157_, lean_object* v_x_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1157_, v_x_1158_);
lean_dec(v_x_1158_);
lean_dec_ref(v_a_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object* v_m_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_buckets_1162_; lean_object* v___x_1163_; uint64_t v___x_1164_; uint64_t v___x_1165_; uint64_t v___x_1166_; uint64_t v_fold_1167_; uint64_t v___x_1168_; uint64_t v___x_1169_; uint64_t v___x_1170_; size_t v___x_1171_; size_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_buckets_1162_ = lean_ctor_get(v_m_1160_, 1);
v___x_1163_ = lean_array_get_size(v_buckets_1162_);
v___x_1164_ = lean_string_hash(v_a_1161_);
v___x_1165_ = 32ULL;
v___x_1166_ = lean_uint64_shift_right(v___x_1164_, v___x_1165_);
v_fold_1167_ = lean_uint64_xor(v___x_1164_, v___x_1166_);
v___x_1168_ = 16ULL;
v___x_1169_ = lean_uint64_shift_right(v_fold_1167_, v___x_1168_);
v___x_1170_ = lean_uint64_xor(v_fold_1167_, v___x_1169_);
v___x_1171_ = lean_uint64_to_usize(v___x_1170_);
v___x_1172_ = lean_usize_of_nat(v___x_1163_);
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_sub(v___x_1172_, v___x_1173_);
v___x_1175_ = lean_usize_land(v___x_1171_, v___x_1174_);
v___x_1176_ = lean_array_uget_borrowed(v_buckets_1162_, v___x_1175_);
v___x_1177_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1161_, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object* v_m_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v_m_1178_, v_a_1179_);
lean_dec_ref(v_a_1179_);
lean_dec_ref(v_m_1178_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object* v___x_1181_, size_t v_sz_1182_, size_t v_i_1183_, lean_object* v_bs_1184_){
_start:
{
uint8_t v___x_1185_; 
v___x_1185_ = lean_usize_dec_lt(v_i_1183_, v_sz_1182_);
if (v___x_1185_ == 0)
{
return v_bs_1184_;
}
else
{
lean_object* v_v_1186_; lean_object* v___x_1187_; lean_object* v_bs_x27_1188_; lean_object* v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
v_v_1186_ = lean_array_uget(v_bs_1184_, v_i_1183_);
v___x_1187_ = lean_unsigned_to_nat(0u);
v_bs_x27_1188_ = lean_array_uset(v_bs_1184_, v_i_1183_, v___x_1187_);
v___x_1189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v___x_1181_, v_v_1186_);
lean_dec(v_v_1186_);
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_add(v_i_1183_, v___x_1190_);
v___x_1192_ = lean_array_uset(v_bs_x27_1188_, v_i_1183_, v___x_1189_);
v_i_1183_ = v___x_1191_;
v_bs_1184_ = v___x_1192_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object* v___x_1194_, lean_object* v_sz_1195_, lean_object* v_i_1196_, lean_object* v_bs_1197_){
_start:
{
size_t v_sz_boxed_1198_; size_t v_i_boxed_1199_; lean_object* v_res_1200_; 
v_sz_boxed_1198_ = lean_unbox_usize(v_sz_1195_);
lean_dec(v_sz_1195_);
v_i_boxed_1199_ = lean_unbox_usize(v_i_1196_);
lean_dec(v_i_1196_);
v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v___x_1194_, v_sz_boxed_1198_, v_i_boxed_1199_, v_bs_1197_);
lean_dec_ref(v___x_1194_);
return v_res_1200_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_unsigned_to_nat(16u);
v___x_1205_ = lean_mk_array(v___x_1204_, v___x_1203_);
return v___x_1205_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_byBase_1208_; 
v___x_1206_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1);
v___x_1207_ = lean_unsigned_to_nat(0u);
v_byBase_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byBase_1208_, 0, v___x_1207_);
lean_ctor_set(v_byBase_1208_, 1, v___x_1206_);
return v_byBase_1208_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3(void){
_start:
{
lean_object* v_byBase_1209_; lean_object* v_order_1210_; lean_object* v___x_1211_; 
v_byBase_1209_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2);
v_order_1210_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0));
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v_order_1210_);
lean_ctor_set(v___x_1211_, 1, v_byBase_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object* v_regions_1212_){
_start:
{
lean_object* v___x_1213_; size_t v_sz_1214_; size_t v___x_1215_; lean_object* v___x_1216_; lean_object* v_fst_1217_; lean_object* v_snd_1218_; size_t v_sz_1219_; lean_object* v___x_1220_; 
v___x_1213_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3);
v_sz_1214_ = lean_array_size(v_regions_1212_);
v___x_1215_ = ((size_t)0ULL);
v___x_1216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_regions_1212_, v_sz_1214_, v___x_1215_, v___x_1213_);
v_fst_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_fst_1217_);
v_snd_1218_ = lean_ctor_get(v___x_1216_, 1);
lean_inc(v_snd_1218_);
lean_dec_ref(v___x_1216_);
v_sz_1219_ = lean_array_size(v_fst_1217_);
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v_snd_1218_, v_sz_1219_, v___x_1215_, v_fst_1217_);
lean_dec(v_snd_1218_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object* v_regions_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1221_);
lean_dec_ref(v_regions_1221_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object* v_00_u03b2_1223_, lean_object* v_m_1224_, lean_object* v_a_1225_, lean_object* v_fallback_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_1224_, v_a_1225_, v_fallback_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object* v_00_u03b2_1228_, lean_object* v_m_1229_, lean_object* v_a_1230_, lean_object* v_fallback_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(v_00_u03b2_1228_, v_m_1229_, v_a_1230_, v_fallback_1231_);
lean_dec(v_fallback_1231_);
lean_dec_ref(v_a_1230_);
lean_dec_ref(v_m_1229_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object* v_00_u03b2_1233_, lean_object* v_m_1234_, lean_object* v_a_1235_, lean_object* v_b_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_1234_, v_a_1235_, v_b_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object* v_00_u03b2_1238_, lean_object* v_m_1239_, lean_object* v_a_1240_){
_start:
{
uint8_t v___x_1241_; 
v___x_1241_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_1239_, v_a_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object* v_00_u03b2_1242_, lean_object* v_m_1243_, lean_object* v_a_1244_){
_start:
{
uint8_t v_res_1245_; lean_object* v_r_1246_; 
v_res_1245_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(v_00_u03b2_1242_, v_m_1243_, v_a_1244_);
lean_dec_ref(v_a_1244_);
lean_dec_ref(v_m_1243_);
v_r_1246_ = lean_box(v_res_1245_);
return v_r_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object* v_00_u03b2_1247_, lean_object* v_a_1248_, lean_object* v_fallback_1249_, lean_object* v_x_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_1248_, v_fallback_1249_, v_x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1252_, lean_object* v_a_1253_, lean_object* v_fallback_1254_, lean_object* v_x_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(v_00_u03b2_1252_, v_a_1253_, v_fallback_1254_, v_x_1255_);
lean_dec(v_x_1255_);
lean_dec(v_fallback_1254_);
lean_dec_ref(v_a_1253_);
return v_res_1256_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object* v_00_u03b2_1257_, lean_object* v_a_1258_, lean_object* v_x_1259_){
_start:
{
uint8_t v___x_1260_; 
v___x_1260_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1258_, v_x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1261_, lean_object* v_a_1262_, lean_object* v_x_1263_){
_start:
{
uint8_t v_res_1264_; lean_object* v_r_1265_; 
v_res_1264_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(v_00_u03b2_1261_, v_a_1262_, v_x_1263_);
lean_dec(v_x_1263_);
lean_dec_ref(v_a_1262_);
v_r_1265_ = lean_box(v_res_1264_);
return v_r_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3(lean_object* v_00_u03b2_1266_, lean_object* v_data_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_data_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4(lean_object* v_00_u03b2_1269_, lean_object* v_a_1270_, lean_object* v_b_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1270_, v_b_1271_, v_x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1274_, lean_object* v_i_1275_, lean_object* v_source_1276_, lean_object* v_target_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v_i_1275_, v_source_1276_, v_target_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_x_1280_, v_x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(lean_object* v_as_1283_, size_t v_sz_1284_, size_t v_i_1285_, lean_object* v_b_1286_){
_start:
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_usize_dec_lt(v_i_1285_, v_sz_1284_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v_b_1286_);
return v___x_1289_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1291_; 
v_a_1290_ = lean_array_uget_borrowed(v_as_1283_, v_i_1285_);
v___x_1291_ = lean_compacted_region_read(v_a_1290_, v_b_1286_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v_snd_1293_; lean_object* v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v_snd_1293_ = lean_ctor_get(v_a_1292_, 1);
lean_inc(v_snd_1293_);
lean_dec(v_a_1292_);
v___x_1294_ = lean_array_push(v_b_1286_, v_snd_1293_);
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_add(v_i_1285_, v___x_1295_);
v_i_1285_ = v___x_1296_;
v_b_1286_ = v___x_1294_;
goto _start;
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec_ref(v_b_1286_);
v_a_1298_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1291_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1291_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0___boxed(lean_object* v_as_1306_, lean_object* v_sz_1307_, lean_object* v_i_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_){
_start:
{
size_t v_sz_boxed_1311_; size_t v_i_boxed_1312_; lean_object* v_res_1313_; 
v_sz_boxed_1311_ = lean_unbox_usize(v_sz_1307_);
lean_dec(v_sz_1307_);
v_i_boxed_1312_ = lean_unbox_usize(v_i_1308_);
lean_dec(v_i_1308_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v_as_1306_, v_sz_boxed_1311_, v_i_boxed_1312_, v_b_1309_);
lean_dec_ref(v_as_1306_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(lean_object* v_arts_1316_){
_start:
{
lean_object* v_oleanRegions_1318_; lean_object* v___x_1319_; size_t v_sz_1320_; size_t v___x_1321_; lean_object* v___x_1322_; 
v_oleanRegions_1318_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc_ref(v_arts_1316_);
v___x_1319_ = l_Lean_ModuleArtifacts_oleanParts(v_arts_1316_);
v_sz_1320_ = lean_array_size(v___x_1319_);
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1319_, v_sz_1320_, v___x_1321_, v_oleanRegions_1318_);
lean_dec_ref(v___x_1319_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1324_; size_t v_sz_1325_; lean_object* v___x_1326_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v___x_1324_ = l_Lean_ModuleArtifacts_irParts(v_arts_1316_);
v_sz_1325_ = lean_array_size(v___x_1324_);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1324_, v_sz_1325_, v___x_1321_, v_oleanRegions_1318_);
lean_dec_ref(v___x_1324_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1335_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = l_Array_append___redArg(v_a_1323_, v_a_1327_);
lean_dec(v_a_1327_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1331_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
else
{
lean_dec(v_a_1323_);
return v___x_1326_;
}
}
else
{
lean_dec_ref(v_arts_1316_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___boxed(lean_object* v_arts_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v_arts_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(lean_object* v_e_1339_){
_start:
{
if (lean_obj_tag(v_e_1339_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1350_; 
v_a_1341_ = lean_ctor_get(v_e_1339_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_e_1339_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1343_ = v_e_1339_;
v_isShared_1344_ = v_isSharedCheck_1350_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v_e_1339_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1350_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1345_ = lean_io_error_to_string(v_a_1341_);
v___x_1346_ = lean_mk_io_user_error(v___x_1345_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set_tag(v___x_1343_, 1);
lean_ctor_set(v___x_1343_, 0, v___x_1346_);
v___x_1348_ = v___x_1343_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
v_a_1351_ = lean_ctor_get(v_e_1339_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_e_1339_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v_e_1339_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v_e_1339_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set_tag(v___x_1353_, 0);
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg___boxed(lean_object* v_e_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_object* v_00_u03b1_1362_, lean_object* v_e_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1363_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___boxed(lean_object* v_00_u03b1_1366_, lean_object* v_e_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(v_00_u03b1_1366_, v_e_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object* v_a_1370_, lean_object* v___y_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_fst_1374_; lean_object* v_snd_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1403_; 
v_fst_1374_ = lean_ctor_get(v_a_1372_, 0);
v_snd_1375_ = lean_ctor_get(v_a_1372_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_a_1372_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1377_ = v_a_1372_;
v_isShared_1378_ = v_isSharedCheck_1403_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_snd_1375_);
lean_inc(v_fst_1374_);
lean_dec(v_a_1372_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1403_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = lean_array_get_size(v_a_1370_);
v___x_1380_ = lean_nat_dec_lt(v_snd_1375_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1382_; 
if (v_isShared_1378_ == 0)
{
v___x_1382_ = v___x_1377_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_fst_1374_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_snd_1375_);
v___x_1382_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1386_ = lean_array_get_borrowed(v___x_1385_, v_a_1370_, v_snd_1375_);
lean_inc(v___x_1386_);
v___x_1387_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v___x_1386_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1387_, 1);
v___x_1389_ = l_Array_append___redArg(v_fst_1374_, v_a_1388_);
lean_dec(v_a_1388_);
v___x_1390_ = lean_nat_add(v_snd_1375_, v___y_1371_);
lean_dec(v_snd_1375_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 1, v___x_1390_);
lean_ctor_set(v___x_1377_, 0, v___x_1389_);
v___x_1392_ = v___x_1377_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
v_a_1372_ = v___x_1392_;
goto _start;
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_del_object(v___x_1377_);
lean_dec(v_snd_1375_);
lean_dec(v_fst_1374_);
v_a_1395_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1387_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1387_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object* v_a_1404_, lean_object* v___y_1405_, lean_object* v_a_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1404_, v___y_1405_, v_a_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v_a_1404_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(lean_object* v_a_1409_, lean_object* v___y_1410_, lean_object* v___x_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1409_, v___y_1410_, v___x_1411_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1422_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_fst_1418_; lean_object* v___x_1420_; 
v_fst_1418_ = lean_ctor_get(v_a_1414_, 0);
lean_inc(v_fst_1418_);
lean_dec(v_a_1414_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 1);
lean_ctor_set(v___x_1416_, 0, v_fst_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_fst_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
v_a_1423_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1413_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1413_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set_tag(v___x_1425_, 0);
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed(lean_object* v_a_1431_, lean_object* v___y_1432_, lean_object* v___x_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(v_a_1431_, v___y_1432_, v___x_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v_a_1431_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(lean_object* v_upperBound_1436_, lean_object* v_a_1437_, lean_object* v___y_1438_, lean_object* v_a_1439_, lean_object* v_b_1440_){
_start:
{
uint8_t v___x_1442_; 
v___x_1442_ = lean_nat_dec_lt(v_a_1439_, v_upperBound_1436_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_dec(v_a_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v_a_1437_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_b_1440_);
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___f_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc(v_a_1439_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v_a_1439_);
lean_inc(v___y_1438_);
lean_inc_ref(v_a_1437_);
v___f_1447_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1447_, 0, v_a_1437_);
lean_closure_set(v___f_1447_, 1, v___y_1438_);
lean_closure_set(v___f_1447_, 2, v___x_1446_);
v___x_1448_ = lean_io_as_task(v___f_1447_, v___x_1444_);
v___x_1449_ = lean_array_push(v_b_1440_, v___x_1448_);
v___x_1450_ = lean_unsigned_to_nat(1u);
v___x_1451_ = lean_nat_add(v_a_1439_, v___x_1450_);
lean_dec(v_a_1439_);
v_a_1439_ = v___x_1451_;
v_b_1440_ = v___x_1449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___boxed(lean_object* v_upperBound_1453_, lean_object* v_a_1454_, lean_object* v___y_1455_, lean_object* v_a_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1453_, v_a_1454_, v___y_1455_, v_a_1456_, v_b_1457_);
lean_dec(v_upperBound_1453_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(lean_object* v_as_1460_, size_t v_sz_1461_, size_t v_i_1462_, lean_object* v_b_1463_){
_start:
{
uint8_t v___x_1465_; 
v___x_1465_ = lean_usize_dec_lt(v_i_1462_, v_sz_1461_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_b_1463_);
return v___x_1466_;
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_a_1467_ = lean_array_uget_borrowed(v_as_1460_, v_i_1462_);
lean_inc(v_a_1467_);
v___x_1468_ = lean_task_get_own(v_a_1467_);
v___x_1469_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v___x_1468_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1471_; size_t v___x_1472_; size_t v___x_1473_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v___x_1471_ = l_Array_append___redArg(v_b_1463_, v_a_1470_);
lean_dec(v_a_1470_);
v___x_1472_ = ((size_t)1ULL);
v___x_1473_ = lean_usize_add(v_i_1462_, v___x_1472_);
v_i_1462_ = v___x_1473_;
v_b_1463_ = v___x_1471_;
goto _start;
}
else
{
lean_dec_ref(v_b_1463_);
return v___x_1469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2___boxed(lean_object* v_as_1475_, lean_object* v_sz_1476_, lean_object* v_i_1477_, lean_object* v_b_1478_, lean_object* v___y_1479_){
_start:
{
size_t v_sz_boxed_1480_; size_t v_i_boxed_1481_; lean_object* v_res_1482_; 
v_sz_boxed_1480_ = lean_unbox_usize(v_sz_1476_);
lean_dec(v_sz_1476_);
v_i_boxed_1481_ = lean_unbox_usize(v_i_1477_);
lean_dec(v_i_1477_);
v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_as_1475_, v_sz_boxed_1480_, v_i_boxed_1481_, v_b_1478_);
lean_dec_ref(v_as_1475_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t v_sz_1483_, size_t v_i_1484_, lean_object* v_bs_1485_){
_start:
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_usize_dec_lt(v_i_1484_, v_sz_1483_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
v___x_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1487_, 0, v_bs_1485_);
return v___x_1487_;
}
else
{
lean_object* v_v_1488_; lean_object* v___x_1489_; 
v_v_1488_ = lean_array_uget_borrowed(v_bs_1485_, v_i_1484_);
lean_inc(v_v_1488_);
v___x_1489_ = l_Lean_instFromJsonModuleArtifacts_fromJson(v_v_1488_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec_ref(v_bs_1485_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v_bs_x27_1500_; size_t v___x_1501_; size_t v___x_1502_; lean_object* v___x_1503_; 
v_a_1498_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1489_, 1);
v___x_1499_ = lean_unsigned_to_nat(0u);
v_bs_x27_1500_ = lean_array_uset(v_bs_1485_, v_i_1484_, v___x_1499_);
v___x_1501_ = ((size_t)1ULL);
v___x_1502_ = lean_usize_add(v_i_1484_, v___x_1501_);
v___x_1503_ = lean_array_uset(v_bs_x27_1500_, v_i_1484_, v_a_1498_);
v_i_1484_ = v___x_1502_;
v_bs_1485_ = v___x_1503_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object* v_sz_1505_, lean_object* v_i_1506_, lean_object* v_bs_1507_){
_start:
{
size_t v_sz_boxed_1508_; size_t v_i_boxed_1509_; lean_object* v_res_1510_; 
v_sz_boxed_1508_ = lean_unbox_usize(v_sz_1505_);
lean_dec(v_sz_1505_);
v_i_boxed_1509_ = lean_unbox_usize(v_i_1506_);
lean_dec(v_i_1506_);
v_res_1510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_boxed_1508_, v_i_boxed_1509_, v_bs_1507_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object* v_x_1513_){
_start:
{
if (lean_obj_tag(v_x_1513_) == 4)
{
lean_object* v_elems_1514_; size_t v_sz_1515_; size_t v___x_1516_; lean_object* v___x_1517_; 
v_elems_1514_ = lean_ctor_get(v_x_1513_, 0);
lean_inc_ref(v_elems_1514_);
lean_dec_ref_known(v_x_1513_, 1);
v_sz_1515_ = lean_array_size(v_elems_1514_);
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_1515_, v___x_1516_, v_elems_1514_);
return v___x_1517_;
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1518_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0));
v___x_1519_ = lean_unsigned_to_nat(80u);
v___x_1520_ = l_Lean_Json_pretty(v_x_1513_, v___x_1519_);
v___x_1521_ = lean_string_append(v___x_1518_, v___x_1520_);
lean_dec_ref(v___x_1520_);
v___x_1522_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1));
v___x_1523_ = lean_string_append(v___x_1521_, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
return v___x_1524_;
}
}
}
static uint32_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3(void){
_start:
{
lean_object* v___x_1528_; uint32_t v___x_1529_; 
v___x_1528_ = lean_box(0);
v___x_1529_ = lean_internal_get_hardware_concurrency(v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4(void){
_start:
{
uint32_t v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_uint32_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3);
v___x_1531_ = lean_uint32_to_nat(v___x_1530_);
return v___x_1531_;
}
}
static uint8_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v___x_1533_ = lean_unsigned_to_nat(4u);
v___x_1534_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1535_ = lean_nat_dec_le(v___x_1534_, v___x_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(lean_object* v_fname_1536_){
_start:
{
lean_object* v___x_1538_; lean_object* v_depsFile_1539_; lean_object* v___x_1540_; 
v___x_1538_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
lean_inc_ref(v_fname_1536_);
v_depsFile_1539_ = l_System_FilePath_addExtension(v_fname_1536_, v___x_1538_);
v___x_1540_ = l_IO_FS_readFile(v_depsFile_1539_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1627_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1627_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1627_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_a_1546_; lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Json_parse(v_a_1541_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; 
lean_dec_ref(v_fname_1536_);
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v_a_1546_ = v_a_1557_;
goto v___jp_1545_;
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1559_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(v_a_1558_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; 
lean_dec_ref(v_fname_1536_);
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1559_, 1);
v_a_1546_ = v_a_1560_;
goto v___jp_1545_;
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___y_1565_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1616_; uint8_t v___x_1626_; 
lean_del_object(v___x_1543_);
lean_dec_ref(v_depsFile_1539_);
v_a_1561_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1559_, 1);
v___x_1562_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1563_ = lean_unsigned_to_nat(4u);
v___x_1626_ = lean_uint8_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6);
if (v___x_1626_ == 0)
{
v___y_1616_ = v___x_1563_;
goto v___jp_1615_;
}
else
{
v___y_1616_ = v___x_1562_;
goto v___jp_1615_;
}
v___jp_1564_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1566_ = lean_mk_empty_array_with_capacity(v___y_1565_);
v___x_1567_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_1561_);
lean_inc(v___y_1565_);
v___x_1568_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v___y_1565_, v_a_1561_, v___y_1565_, v___x_1567_, v___x_1566_);
lean_dec(v___y_1565_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; size_t v_sz_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
v___x_1570_ = lean_array_get_size(v_a_1561_);
lean_dec(v_a_1561_);
v___x_1571_ = lean_nat_mul(v___x_1570_, v___x_1563_);
v___x_1572_ = lean_mk_empty_array_with_capacity(v___x_1571_);
lean_dec(v___x_1571_);
v_sz_1573_ = lean_array_size(v_a_1569_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_a_1569_, v_sz_1573_, v___x_1574_, v___x_1572_);
lean_dec(v_a_1569_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1577_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v___x_1577_ = lean_compacted_region_read(v_fname_1536_, v_a_1576_);
lean_dec(v_a_1576_);
lean_dec_ref(v_fname_1536_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1586_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1586_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1586_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v_fst_1582_; lean_object* v___x_1584_; 
v_fst_1582_ = lean_ctor_get(v_a_1578_, 0);
lean_inc(v_fst_1582_);
lean_dec(v_a_1578_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v_fst_1582_);
v___x_1584_ = v___x_1580_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_fst_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
v_a_1587_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1577_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1577_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v_fname_1536_);
v_a_1595_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1575_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1575_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v_a_1561_);
lean_dec_ref(v_fname_1536_);
v_a_1603_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1568_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1568_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
v___jp_1611_:
{
uint8_t v___x_1614_; 
v___x_1614_ = lean_nat_dec_le(v___y_1612_, v___y_1613_);
if (v___x_1614_ == 0)
{
lean_dec(v___y_1613_);
v___y_1565_ = v___y_1612_;
goto v___jp_1564_;
}
else
{
lean_dec(v___y_1612_);
v___y_1565_ = v___y_1613_;
goto v___jp_1564_;
}
}
v___jp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5));
v___x_1618_ = lean_io_getenv(v___x_1617_);
v___x_1619_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v___x_1618_) == 0)
{
v___y_1612_ = v___x_1619_;
v___y_1613_ = v___y_1616_;
goto v___jp_1611_;
}
else
{
lean_object* v_val_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v_val_1620_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_val_1620_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = lean_string_utf8_byte_size(v_val_1620_);
v___x_1623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1623_, 0, v_val_1620_);
lean_ctor_set(v___x_1623_, 1, v___x_1621_);
lean_ctor_set(v___x_1623_, 2, v___x_1622_);
v___x_1624_ = l_String_Slice_toNat_x3f(v___x_1623_);
lean_dec_ref_known(v___x_1623_, 3);
if (lean_obj_tag(v___x_1624_) == 0)
{
v___y_1612_ = v___x_1619_;
v___y_1613_ = v___y_1616_;
goto v___jp_1611_;
}
else
{
lean_object* v_val_1625_; 
lean_dec(v___y_1616_);
v_val_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_val_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v___y_1612_ = v___x_1619_;
v___y_1613_ = v_val_1625_;
goto v___jp_1611_;
}
}
}
}
}
v___jp_1545_:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1547_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1));
v___x_1548_ = lean_string_append(v___x_1547_, v_depsFile_1539_);
lean_dec_ref(v_depsFile_1539_);
v___x_1549_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2));
v___x_1550_ = lean_string_append(v___x_1548_, v___x_1549_);
v___x_1551_ = lean_string_append(v___x_1550_, v_a_1546_);
lean_dec_ref(v_a_1546_);
v___x_1552_ = lean_mk_io_user_error(v___x_1551_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set_tag(v___x_1543_, 1);
lean_ctor_set(v___x_1543_, 0, v___x_1552_);
v___x_1554_ = v___x_1543_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec_ref(v_depsFile_1539_);
lean_dec_ref(v_fname_1536_);
v_a_1628_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1540_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1540_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___boxed(lean_object* v_fname_1636_, lean_object* v_a_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_fname_1636_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object* v_a_1639_, lean_object* v___y_1640_, lean_object* v_inst_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1639_, v___y_1640_, v_a_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object* v_a_1645_, lean_object* v___y_1646_, lean_object* v_inst_1647_, lean_object* v_a_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(v_a_1645_, v___y_1646_, v_inst_1647_, v_a_1648_);
lean_dec(v___y_1646_);
lean_dec_ref(v_a_1645_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object* v_upperBound_1651_, lean_object* v_a_1652_, lean_object* v___y_1653_, lean_object* v_inst_1654_, lean_object* v_R_1655_, lean_object* v_a_1656_, lean_object* v_b_1657_, lean_object* v_c_1658_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1651_, v_a_1652_, v___y_1653_, v_a_1656_, v_b_1657_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object* v_upperBound_1661_, lean_object* v_a_1662_, lean_object* v___y_1663_, lean_object* v_inst_1664_, lean_object* v_R_1665_, lean_object* v_a_1666_, lean_object* v_b_1667_, lean_object* v_c_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(v_upperBound_1661_, v_a_1662_, v___y_1663_, v_inst_1664_, v_R_1665_, v_a_1666_, v_b_1667_, v_c_1668_);
lean_dec(v_upperBound_1661_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object* v_as_1671_, size_t v_sz_1672_, size_t v_i_1673_, lean_object* v_b_1674_){
_start:
{
uint8_t v___x_1676_; 
v___x_1676_ = lean_usize_dec_lt(v_i_1673_, v_sz_1672_);
if (v___x_1676_ == 0)
{
return v_b_1674_;
}
else
{
lean_object* v_a_1677_; lean_object* v_cancelTk_x3f_1678_; lean_object* v___x_1679_; 
v_a_1677_ = lean_array_uget_borrowed(v_as_1671_, v_i_1673_);
v_cancelTk_x3f_1678_ = lean_ctor_get(v_a_1677_, 2);
v___x_1679_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_1678_) == 1)
{
lean_object* v_val_1686_; lean_object* v___x_1687_; 
v_val_1686_ = lean_ctor_get(v_cancelTk_x3f_1678_, 0);
v___x_1687_ = l_IO_CancelToken_set(v_val_1686_);
goto v___jp_1680_;
}
else
{
goto v___jp_1680_;
}
v___jp_1680_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; size_t v___x_1683_; size_t v___x_1684_; 
lean_inc(v_a_1677_);
v___x_1681_ = l_Lean_Language_SnapshotTask_get___redArg(v_a_1677_);
v___x_1682_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___x_1681_);
lean_dec(v___x_1681_);
v___x_1683_ = ((size_t)1ULL);
v___x_1684_ = lean_usize_add(v_i_1673_, v___x_1683_);
v_i_1673_ = v___x_1684_;
v_b_1674_ = v___x_1679_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object* v_s_1688_){
_start:
{
lean_object* v_children_1690_; lean_object* v___x_1691_; size_t v_sz_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
v_children_1690_ = lean_ctor_get(v_s_1688_, 1);
v___x_1691_ = lean_box(0);
v_sz_1692_ = lean_array_size(v_children_1690_);
v___x_1693_ = ((size_t)0ULL);
v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_children_1690_, v_sz_1692_, v___x_1693_, v___x_1691_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object* v_s_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v_s_1695_);
lean_dec_ref(v_s_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object* v_as_1698_, lean_object* v_sz_1699_, lean_object* v_i_1700_, lean_object* v_b_1701_, lean_object* v___y_1702_){
_start:
{
size_t v_sz_boxed_1703_; size_t v_i_boxed_1704_; lean_object* v_res_1705_; 
v_sz_boxed_1703_ = lean_unbox_usize(v_sz_1699_);
lean_dec(v_sz_1699_);
v_i_boxed_1704_ = lean_unbox_usize(v_i_1700_);
lean_dec(v_i_1700_);
v_res_1705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_as_1698_, v_sz_boxed_1703_, v_i_boxed_1704_, v_b_1701_);
lean_dec_ref(v_as_1698_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(lean_object* v_snap_1706_, lean_object* v_m_1707_){
_start:
{
lean_object* v_result_x3f_1708_; 
v_result_x3f_1708_ = lean_ctor_get(v_snap_1706_, 4);
lean_inc(v_result_x3f_1708_);
if (lean_obj_tag(v_result_x3f_1708_) == 1)
{
lean_object* v_val_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1809_; 
v_val_1709_ = lean_ctor_get(v_result_x3f_1708_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_result_x3f_1708_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1711_ = v_result_x3f_1708_;
v_isShared_1712_ = v_isSharedCheck_1809_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_val_1709_);
lean_dec(v_result_x3f_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1809_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_toSnapshot_1713_; lean_object* v_metaSnap_1714_; lean_object* v_ictx_1715_; lean_object* v_stx_1716_; lean_object* v_parserState_1717_; lean_object* v_processedSnap_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1808_; 
v_toSnapshot_1713_ = lean_ctor_get(v_snap_1706_, 0);
v_metaSnap_1714_ = lean_ctor_get(v_snap_1706_, 1);
v_ictx_1715_ = lean_ctor_get(v_snap_1706_, 2);
v_stx_1716_ = lean_ctor_get(v_snap_1706_, 3);
v_parserState_1717_ = lean_ctor_get(v_val_1709_, 0);
v_processedSnap_1718_ = lean_ctor_get(v_val_1709_, 1);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_val_1709_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1720_ = v_val_1709_;
v_isShared_1721_ = v_isSharedCheck_1808_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_processedSnap_1718_);
lean_inc(v_parserState_1717_);
lean_dec(v_val_1709_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1808_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v_processed_1722_; lean_object* v_result_x3f_1723_; 
v_processed_1722_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_1718_);
v_result_x3f_1723_ = lean_ctor_get(v_processed_1722_, 2);
lean_inc(v_result_x3f_1723_);
if (lean_obj_tag(v_result_x3f_1723_) == 1)
{
lean_object* v_val_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1807_; 
v_val_1724_ = lean_ctor_get(v_result_x3f_1723_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_result_x3f_1723_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1726_ = v_result_x3f_1723_;
v_isShared_1727_ = v_isSharedCheck_1807_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_val_1724_);
lean_dec(v_result_x3f_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1807_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_cmdState_1728_; lean_object* v_toSnapshot_1729_; lean_object* v_metaSnap_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1805_; 
v_cmdState_1728_ = lean_ctor_get(v_val_1724_, 0);
lean_inc_ref(v_cmdState_1728_);
v_toSnapshot_1729_ = lean_ctor_get(v_processed_1722_, 0);
v_metaSnap_1730_ = lean_ctor_get(v_processed_1722_, 1);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_processed_1722_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; 
v_unused_1806_ = lean_ctor_get(v_processed_1722_, 2);
lean_dec(v_unused_1806_);
v___x_1732_ = v_processed_1722_;
v_isShared_1733_ = v_isSharedCheck_1805_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_metaSnap_1730_);
lean_inc(v_toSnapshot_1729_);
lean_dec(v_processed_1722_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1805_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_firstCmdSnap_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1803_; 
v_firstCmdSnap_1734_ = lean_ctor_get(v_val_1724_, 1);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_val_1724_);
if (v_isSharedCheck_1803_ == 0)
{
lean_object* v_unused_1804_; 
v_unused_1804_ = lean_ctor_get(v_val_1724_, 0);
lean_dec(v_unused_1804_);
v___x_1736_ = v_val_1724_;
v_isShared_1737_ = v_isSharedCheck_1803_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_firstCmdSnap_1734_);
lean_dec(v_val_1724_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1803_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_env_1738_; lean_object* v_messages_1739_; lean_object* v_scopes_1740_; lean_object* v_usedQuotCtxts_1741_; lean_object* v_nextMacroScope_1742_; lean_object* v_maxRecDepth_1743_; lean_object* v_ngen_1744_; lean_object* v_auxDeclNGen_1745_; lean_object* v_infoState_1746_; lean_object* v_traceState_1747_; lean_object* v_snapshotTasks_1748_; lean_object* v_prevLinterStates_1749_; lean_object* v_codeQualityEntryTasks_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1802_; 
v_env_1738_ = lean_ctor_get(v_cmdState_1728_, 0);
v_messages_1739_ = lean_ctor_get(v_cmdState_1728_, 1);
v_scopes_1740_ = lean_ctor_get(v_cmdState_1728_, 2);
v_usedQuotCtxts_1741_ = lean_ctor_get(v_cmdState_1728_, 3);
v_nextMacroScope_1742_ = lean_ctor_get(v_cmdState_1728_, 4);
v_maxRecDepth_1743_ = lean_ctor_get(v_cmdState_1728_, 5);
v_ngen_1744_ = lean_ctor_get(v_cmdState_1728_, 6);
v_auxDeclNGen_1745_ = lean_ctor_get(v_cmdState_1728_, 7);
v_infoState_1746_ = lean_ctor_get(v_cmdState_1728_, 8);
v_traceState_1747_ = lean_ctor_get(v_cmdState_1728_, 9);
v_snapshotTasks_1748_ = lean_ctor_get(v_cmdState_1728_, 10);
v_prevLinterStates_1749_ = lean_ctor_get(v_cmdState_1728_, 11);
v_codeQualityEntryTasks_1750_ = lean_ctor_get(v_cmdState_1728_, 12);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_cmdState_1728_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1752_ = v_cmdState_1728_;
v_isShared_1753_ = v_isSharedCheck_1802_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1750_);
lean_inc(v_prevLinterStates_1749_);
lean_inc(v_snapshotTasks_1748_);
lean_inc(v_traceState_1747_);
lean_inc(v_infoState_1746_);
lean_inc(v_auxDeclNGen_1745_);
lean_inc(v_ngen_1744_);
lean_inc(v_maxRecDepth_1743_);
lean_inc(v_nextMacroScope_1742_);
lean_inc(v_usedQuotCtxts_1741_);
lean_inc(v_scopes_1740_);
lean_inc(v_messages_1739_);
lean_inc(v_env_1738_);
lean_dec(v_cmdState_1728_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1802_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v_mainModule_1755_; uint8_t v___x_1756_; 
v___x_1754_ = l_Lean_Environment_header(v_env_1738_);
v_mainModule_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_mainModule_1755_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = lean_name_eq(v_mainModule_1755_, v_m_1707_);
lean_dec(v_mainModule_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1796_; 
lean_inc(v_stx_1716_);
lean_inc_ref(v_ictx_1715_);
lean_inc_ref(v_metaSnap_1714_);
lean_inc_ref(v_toSnapshot_1713_);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_snap_1706_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; lean_object* v_unused_1798_; lean_object* v_unused_1799_; lean_object* v_unused_1800_; lean_object* v_unused_1801_; 
v_unused_1797_ = lean_ctor_get(v_snap_1706_, 4);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_snap_1706_, 3);
lean_dec(v_unused_1798_);
v_unused_1799_ = lean_ctor_get(v_snap_1706_, 2);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v_snap_1706_, 1);
lean_dec(v_unused_1800_);
v_unused_1801_ = lean_ctor_get(v_snap_1706_, 0);
lean_dec(v_unused_1801_);
v___x_1758_ = v_snap_1706_;
v_isShared_1759_ = v_isSharedCheck_1796_;
goto v_resetjp_1757_;
}
else
{
lean_dec(v_snap_1706_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1796_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_idx_1760_; lean_object* v_parentIdxs_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1794_; 
v_idx_1760_ = lean_ctor_get(v_auxDeclNGen_1745_, 1);
v_parentIdxs_1761_ = lean_ctor_get(v_auxDeclNGen_1745_, 2);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_auxDeclNGen_1745_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v_auxDeclNGen_1745_, 0);
lean_dec(v_unused_1795_);
v___x_1763_ = v_auxDeclNGen_1745_;
v_isShared_1764_ = v_isSharedCheck_1794_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_parentIdxs_1761_);
lean_inc(v_idx_1760_);
lean_dec(v_auxDeclNGen_1745_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1794_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v_newEnv_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
v_newEnv_1765_ = l_Lean_Environment_setMainModule(v_env_1738_, v_m_1707_);
v___x_1766_ = lean_box(0);
v___x_1767_ = l_Lean_mkPrivateName(v_newEnv_1765_, v___x_1766_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1767_);
v___x_1769_ = v___x_1763_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_idx_1760_);
lean_ctor_set(v_reuseFailAlloc_1793_, 2, v_parentIdxs_1761_);
v___x_1769_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v_newCmdState_1771_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 7, v___x_1769_);
lean_ctor_set(v___x_1752_, 0, v_newEnv_1765_);
v_newCmdState_1771_ = v___x_1752_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_newEnv_1765_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_messages_1739_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_scopes_1740_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_usedQuotCtxts_1741_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v_nextMacroScope_1742_);
lean_ctor_set(v_reuseFailAlloc_1792_, 5, v_maxRecDepth_1743_);
lean_ctor_set(v_reuseFailAlloc_1792_, 6, v_ngen_1744_);
lean_ctor_set(v_reuseFailAlloc_1792_, 7, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1792_, 8, v_infoState_1746_);
lean_ctor_set(v_reuseFailAlloc_1792_, 9, v_traceState_1747_);
lean_ctor_set(v_reuseFailAlloc_1792_, 10, v_snapshotTasks_1748_);
lean_ctor_set(v_reuseFailAlloc_1792_, 11, v_prevLinterStates_1749_);
lean_ctor_set(v_reuseFailAlloc_1792_, 12, v_codeQualityEntryTasks_1750_);
v_newCmdState_1771_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1773_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v_newCmdState_1771_);
v___x_1773_ = v___x_1736_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_newCmdState_1771_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_firstCmdSnap_1734_);
v___x_1773_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1775_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1773_);
v___x_1775_ = v___x_1726_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v_newProcessed_1777_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 2, v___x_1775_);
v_newProcessed_1777_ = v___x_1732_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_toSnapshot_1729_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_metaSnap_1730_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v___x_1775_);
v_newProcessed_1777_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1778_ = lean_box(0);
v___x_1779_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1778_, v_newProcessed_1777_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 1, v___x_1779_);
v___x_1781_ = v___x_1720_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_parserState_1717_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1781_);
v___x_1783_ = v___x_1711_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1785_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 4, v___x_1783_);
v___x_1785_ = v___x_1758_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_toSnapshot_1713_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_metaSnap_1714_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_ictx_1715_);
lean_ctor_set(v_reuseFailAlloc_1786_, 3, v_stx_1716_);
lean_ctor_set(v_reuseFailAlloc_1786_, 4, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
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
lean_del_object(v___x_1752_);
lean_dec_ref(v_codeQualityEntryTasks_1750_);
lean_dec(v_prevLinterStates_1749_);
lean_dec_ref(v_snapshotTasks_1748_);
lean_dec_ref(v_traceState_1747_);
lean_dec_ref(v_infoState_1746_);
lean_dec_ref(v_auxDeclNGen_1745_);
lean_dec_ref(v_ngen_1744_);
lean_dec(v_maxRecDepth_1743_);
lean_dec(v_nextMacroScope_1742_);
lean_dec(v_usedQuotCtxts_1741_);
lean_dec(v_scopes_1740_);
lean_dec_ref(v_messages_1739_);
lean_dec_ref(v_env_1738_);
lean_del_object(v___x_1736_);
lean_dec_ref(v_firstCmdSnap_1734_);
lean_del_object(v___x_1732_);
lean_dec_ref(v_metaSnap_1730_);
lean_dec_ref(v_toSnapshot_1729_);
lean_del_object(v___x_1726_);
lean_del_object(v___x_1720_);
lean_dec_ref(v_parserState_1717_);
lean_del_object(v___x_1711_);
lean_dec(v_m_1707_);
return v_snap_1706_;
}
}
}
}
}
}
else
{
lean_dec(v_result_x3f_1723_);
lean_dec(v_processed_1722_);
lean_del_object(v___x_1720_);
lean_dec_ref(v_parserState_1717_);
lean_del_object(v___x_1711_);
lean_dec(v_m_1707_);
return v_snap_1706_;
}
}
}
}
else
{
lean_dec(v_result_x3f_1708_);
lean_dec(v_m_1707_);
return v_snap_1706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object* v_incrFile_1810_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_incrFile_1810_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object* v_incrFile_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(v_incrFile_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object* v_opts_1816_, lean_object* v_incr_1817_, lean_object* v_res_1818_){
_start:
{
lean_object* v_cmdState_1820_; lean_object* v_env_1821_; lean_object* v_initModIdxs_1822_; lean_object* v___x_1823_; 
v_cmdState_1820_ = lean_ctor_get(v_res_1818_, 0);
lean_inc_ref(v_cmdState_1820_);
lean_dec_ref(v_res_1818_);
v_env_1821_ = lean_ctor_get(v_cmdState_1820_, 0);
lean_inc_ref(v_env_1821_);
lean_dec_ref(v_cmdState_1820_);
v_initModIdxs_1822_ = lean_ctor_get(v_incr_1817_, 1);
v___x_1823_ = l_Lean_runInitAttrsForModules(v_env_1821_, v_initModIdxs_1822_, v_opts_1816_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object* v_opts_1824_, lean_object* v_incr_1825_, lean_object* v_res_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(v_opts_1824_, v_incr_1825_, v_res_1826_);
lean_dec_ref(v_incr_1825_);
lean_dec_ref(v_opts_1824_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7(){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_enable_initializer_execution();
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object* v_a_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(lean_object* v_env_1836_, lean_object* v_incrFile_1837_, lean_object* v_toSave_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v_regions_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; 
v___x_1840_ = l_Lean_Environment_header(v_env_1836_);
v_regions_1841_ = lean_ctor_get(v___x_1840_, 2);
lean_inc_ref(v_regions_1841_);
lean_dec_ref(v___x_1840_);
v___x_1842_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1843_ = lean_box(0);
v___x_1844_ = 1;
v___x_1845_ = lean_compacted_region_save(v_incrFile_1837_, v___x_1842_, v_toSave_1838_, v_regions_1841_, v___x_1843_, v___x_1844_);
lean_dec_ref(v_regions_1841_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___boxed(lean_object* v_env_1846_, lean_object* v_incrFile_1847_, lean_object* v_toSave_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(v_env_1846_, v_incrFile_1847_, v_toSave_1848_);
lean_dec_ref(v_toSave_1848_);
lean_dec_ref(v_incrFile_1847_);
lean_dec_ref(v_env_1846_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_opts_1851_, lean_object* v_opt_1852_){
_start:
{
lean_object* v_name_1853_; lean_object* v_map_1854_; lean_object* v___x_1855_; 
v_name_1853_ = lean_ctor_get(v_opt_1852_, 0);
v_map_1854_ = lean_ctor_get(v_opts_1851_, 0);
v___x_1855_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1854_, v_name_1853_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_box(0);
return v___x_1856_;
}
else
{
lean_object* v_val_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1866_; 
v_val_1857_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1859_ = v___x_1855_;
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_val_1857_);
lean_dec(v___x_1855_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
if (lean_obj_tag(v_val_1857_) == 0)
{
lean_object* v_v_1861_; lean_object* v___x_1863_; 
v_v_1861_ = lean_ctor_get(v_val_1857_, 0);
lean_inc_ref(v_v_1861_);
lean_dec_ref_known(v_val_1857_, 1);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v_v_1861_);
v___x_1863_ = v___x_1859_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_v_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
else
{
lean_object* v___x_1865_; 
lean_del_object(v___x_1859_);
lean_dec(v_val_1857_);
v___x_1865_ = lean_box(0);
return v___x_1865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_opts_1867_, lean_object* v_opt_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v_opts_1867_, v_opt_1868_);
lean_dec_ref(v_opt_1868_);
lean_dec_ref(v_opts_1867_);
return v_res_1869_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_opts_1870_, lean_object* v_opt_1871_){
_start:
{
lean_object* v_name_1872_; lean_object* v_defValue_1873_; lean_object* v_map_1874_; lean_object* v___x_1875_; 
v_name_1872_ = lean_ctor_get(v_opt_1871_, 0);
v_defValue_1873_ = lean_ctor_get(v_opt_1871_, 1);
v_map_1874_ = lean_ctor_get(v_opts_1870_, 0);
v___x_1875_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1874_, v_name_1872_);
if (lean_obj_tag(v___x_1875_) == 0)
{
uint8_t v___x_1876_; 
v___x_1876_ = lean_unbox(v_defValue_1873_);
return v___x_1876_;
}
else
{
lean_object* v_val_1877_; 
v_val_1877_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_val_1877_);
lean_dec_ref_known(v___x_1875_, 1);
if (lean_obj_tag(v_val_1877_) == 1)
{
uint8_t v_v_1878_; 
v_v_1878_ = lean_ctor_get_uint8(v_val_1877_, 0);
lean_dec_ref_known(v_val_1877_, 0);
return v_v_1878_;
}
else
{
uint8_t v___x_1879_; 
lean_dec(v_val_1877_);
v___x_1879_ = lean_unbox(v_defValue_1873_);
return v___x_1879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_opts_1880_, lean_object* v_opt_1881_){
_start:
{
uint8_t v_res_1882_; lean_object* v_r_1883_; 
v_res_1882_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1880_, v_opt_1881_);
lean_dec_ref(v_opt_1881_);
lean_dec_ref(v_opts_1880_);
v_r_1883_ = lean_box(v_res_1882_);
return v_r_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v_hOpt_1886_){
_start:
{
lean_inc_ref(v_hOpt_1886_);
return v_hOpt_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v_hOpt_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_Elab_runFrontend___lam__0(v_x_1887_, v_x_1888_, v_hOpt_1889_);
lean_dec_ref(v_hOpt_1889_);
lean_dec_ref(v_x_1888_);
lean_dec(v_x_1887_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_x1_1891_, lean_object* v_x2_1892_){
_start:
{
lean_object* v_elabSnap_1893_; lean_object* v_resultSnap_1894_; lean_object* v___x_1895_; lean_object* v_codeQualityEntryTasks_1896_; lean_object* v___x_1897_; 
v_elabSnap_1893_ = lean_ctor_get(v_x2_1892_, 3);
lean_inc_ref(v_elabSnap_1893_);
lean_dec_ref(v_x2_1892_);
v_resultSnap_1894_ = lean_ctor_get(v_elabSnap_1893_, 2);
lean_inc_ref(v_resultSnap_1894_);
lean_dec_ref(v_elabSnap_1893_);
v___x_1895_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_1894_);
v_codeQualityEntryTasks_1896_ = lean_ctor_get(v___x_1895_, 2);
lean_inc_ref(v_codeQualityEntryTasks_1896_);
lean_dec(v___x_1895_);
v___x_1897_ = l_Array_append___redArg(v_x1_1891_, v_codeQualityEntryTasks_1896_);
lean_dec_ref(v_codeQualityEntryTasks_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(size_t v_sz_1898_, size_t v_i_1899_, lean_object* v_bs_1900_){
_start:
{
uint8_t v___x_1901_; 
v___x_1901_ = lean_usize_dec_lt(v_i_1899_, v_sz_1898_);
if (v___x_1901_ == 0)
{
return v_bs_1900_;
}
else
{
lean_object* v_v_1902_; lean_object* v___x_1903_; lean_object* v_bs_x27_1904_; lean_object* v___x_1905_; size_t v___x_1906_; size_t v___x_1907_; lean_object* v___x_1908_; 
v_v_1902_ = lean_array_uget(v_bs_1900_, v_i_1899_);
v___x_1903_ = lean_unsigned_to_nat(0u);
v_bs_x27_1904_ = lean_array_uset(v_bs_1900_, v_i_1899_, v___x_1903_);
v___x_1905_ = l_Lean_instToJsonModuleArtifacts_toJson(v_v_1902_);
v___x_1906_ = ((size_t)1ULL);
v___x_1907_ = lean_usize_add(v_i_1899_, v___x_1906_);
v___x_1908_ = lean_array_uset(v_bs_x27_1904_, v_i_1899_, v___x_1905_);
v_i_1899_ = v___x_1907_;
v_bs_1900_ = v___x_1908_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11___boxed(lean_object* v_sz_1910_, lean_object* v_i_1911_, lean_object* v_bs_1912_){
_start:
{
size_t v_sz_boxed_1913_; size_t v_i_boxed_1914_; lean_object* v_res_1915_; 
v_sz_boxed_1913_ = lean_unbox_usize(v_sz_1910_);
lean_dec(v_sz_1910_);
v_i_boxed_1914_ = lean_unbox_usize(v_i_1911_);
lean_dec(v_i_1911_);
v_res_1915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(v_sz_boxed_1913_, v_i_boxed_1914_, v_bs_1912_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8(lean_object* v_a_1916_){
_start:
{
size_t v_sz_1917_; size_t v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_sz_1917_ = lean_array_size(v_a_1916_);
v___x_1918_ = ((size_t)0ULL);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(v_sz_1917_, v___x_1918_, v_a_1916_);
v___x_1920_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_a_1921_, uint8_t v___x_1922_, lean_object* v_incrFile_1923_, lean_object* v_snapToSave_1924_){
_start:
{
lean_object* v___x_1926_; lean_object* v_regions_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1926_ = l_Lean_Environment_header(v_a_1921_);
v_regions_1927_ = lean_ctor_get(v___x_1926_, 2);
lean_inc_ref(v_regions_1927_);
lean_dec_ref(v___x_1926_);
v___x_1928_ = l_Lean_getRegularInitAttrModIdxs(v_a_1921_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v_snapToSave_1924_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_compacted_region_save(v_incrFile_1923_, v___x_1930_, v___x_1929_, v_regions_1927_, v___x_1931_, v___x_1922_);
lean_dec_ref_known(v___x_1929_, 2);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v___x_1934_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1927_);
lean_dec_ref(v_regions_1927_);
v___x_1935_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
v___x_1936_ = l_System_FilePath_addExtension(v_incrFile_1923_, v___x_1935_);
v___x_1937_ = l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8(v___x_1934_);
v___x_1938_ = l_Lean_Json_compress(v___x_1937_);
v___x_1939_ = l_IO_FS_writeFile(v___x_1936_, v___x_1938_);
lean_dec_ref(v___x_1938_);
lean_dec_ref(v___x_1936_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1947_; 
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; 
v_unused_1948_ = lean_ctor_get(v___x_1939_, 0);
lean_dec(v_unused_1948_);
v___x_1941_ = v___x_1939_;
v_isShared_1942_ = v_isSharedCheck_1947_;
goto v_resetjp_1940_;
}
else
{
lean_dec(v___x_1939_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1947_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1943_ = lean_runtime_forget(v_a_1933_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1943_);
v___x_1945_ = v___x_1941_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_dec(v_a_1933_);
return v___x_1939_;
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_regions_1927_);
lean_dec_ref(v_incrFile_1923_);
v_a_1949_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1932_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1932_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object* v_a_1957_, lean_object* v___x_1958_, lean_object* v_incrFile_1959_, lean_object* v_snapToSave_1960_, lean_object* v___y_1961_){
_start:
{
uint8_t v___x_6105__boxed_1962_; lean_object* v_res_1963_; 
v___x_6105__boxed_1962_ = lean_unbox(v___x_1958_);
v_res_1963_ = l_Lean_Elab_runFrontend___lam__2(v_a_1957_, v___x_6105__boxed_1962_, v_incrFile_1959_, v_snapToSave_1960_);
lean_dec_ref(v_a_1957_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_fileMap_1964_, lean_object* v_a_1965_, lean_object* v___x_1966_, lean_object* v_opts_1967_, lean_object* v_val_1968_, uint8_t v___x_1969_, uint8_t v_a_1970_){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1972_ = l_Lean_Linter_recordLints(v_fileMap_1964_, v_a_1965_, v___x_1966_);
v___x_1973_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1974_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1967_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_writeModule(v___x_1972_, v_val_1968_, v___x_1969_);
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_writeModule(v___x_1972_, v_val_1968_, v_a_1970_);
return v___x_1976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_fileMap_1977_, lean_object* v_a_1978_, lean_object* v___x_1979_, lean_object* v_opts_1980_, lean_object* v_val_1981_, lean_object* v___x_1982_, lean_object* v_a_1983_, lean_object* v___y_1984_){
_start:
{
uint8_t v___x_6179__boxed_1985_; uint8_t v_a_6180__boxed_1986_; lean_object* v_res_1987_; 
v___x_6179__boxed_1985_ = lean_unbox(v___x_1982_);
v_a_6180__boxed_1986_ = lean_unbox(v_a_1983_);
v_res_1987_ = l_Lean_Elab_runFrontend___lam__3(v_fileMap_1977_, v_a_1978_, v___x_1979_, v_opts_1980_, v_val_1981_, v___x_6179__boxed_1985_, v_a_6180__boxed_1986_);
lean_dec_ref(v_opts_1980_);
lean_dec_ref(v___x_1979_);
lean_dec_ref(v_fileMap_1977_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_1988_, size_t v_i_1989_, size_t v_stop_1990_, lean_object* v_b_1991_){
_start:
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_usize_dec_eq(v_i_1989_, v_stop_1990_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_array_uget_borrowed(v_as_1988_, v_i_1989_);
lean_inc(v___x_1994_);
v___x_1995_ = lean_load_dynlib(v___x_1994_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; size_t v___x_1997_; size_t v___x_1998_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_1997_ = ((size_t)1ULL);
v___x_1998_ = lean_usize_add(v_i_1989_, v___x_1997_);
v_i_1989_ = v___x_1998_;
v_b_1991_ = v_a_1996_;
goto _start;
}
else
{
return v___x_1995_;
}
}
else
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_b_1991_);
return v___x_2000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_2001_, lean_object* v_i_2002_, lean_object* v_stop_2003_, lean_object* v_b_2004_, lean_object* v___y_2005_){
_start:
{
size_t v_i_boxed_2006_; size_t v_stop_boxed_2007_; lean_object* v_res_2008_; 
v_i_boxed_2006_ = lean_unbox_usize(v_i_2002_);
lean_dec(v_i_2002_);
v_stop_boxed_2007_ = lean_unbox_usize(v_stop_2003_);
lean_dec(v_stop_2003_);
v_res_2008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_2001_, v_i_boxed_2006_, v_stop_boxed_2007_, v_b_2004_);
lean_dec_ref(v_as_2001_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* v_setup_x3f_2009_, lean_object* v___f_2010_, lean_object* v___x_2011_, lean_object* v_plugins_2012_, uint32_t v_trustLevel_2013_, uint8_t v___x_2014_, lean_object* v_mainModuleName_2015_, lean_object* v_stx_2016_, lean_object* v___y_2017_){
_start:
{
uint8_t v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; 
if (lean_obj_tag(v_setup_x3f_2009_) == 1)
{
lean_object* v_val_2033_; lean_object* v_name_2034_; lean_object* v_package_x3f_2035_; uint8_t v_isModule_2036_; lean_object* v_imports_x3f_2037_; lean_object* v_importArts_2038_; lean_object* v_dynlibs_2039_; lean_object* v_plugins_2040_; lean_object* v_options_2041_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
lean_dec(v_mainModuleName_2015_);
v_val_2033_ = lean_ctor_get(v_setup_x3f_2009_, 0);
lean_inc(v_val_2033_);
lean_dec_ref_known(v_setup_x3f_2009_, 1);
v_name_2034_ = lean_ctor_get(v_val_2033_, 0);
lean_inc(v_name_2034_);
v_package_x3f_2035_ = lean_ctor_get(v_val_2033_, 1);
lean_inc(v_package_x3f_2035_);
v_isModule_2036_ = lean_ctor_get_uint8(v_val_2033_, sizeof(void*)*7);
v_imports_x3f_2037_ = lean_ctor_get(v_val_2033_, 2);
lean_inc(v_imports_x3f_2037_);
v_importArts_2038_ = lean_ctor_get(v_val_2033_, 3);
lean_inc(v_importArts_2038_);
v_dynlibs_2039_ = lean_ctor_get(v_val_2033_, 4);
lean_inc_ref(v_dynlibs_2039_);
v_plugins_2040_ = lean_ctor_get(v_val_2033_, 5);
lean_inc_ref(v_plugins_2040_);
v_options_2041_ = lean_ctor_get(v_val_2033_, 6);
lean_inc(v_options_2041_);
lean_dec(v_val_2033_);
v___x_2047_ = lean_unsigned_to_nat(0u);
v___x_2048_ = lean_array_get_size(v_dynlibs_2039_);
v___x_2049_ = lean_nat_dec_lt(v___x_2047_, v___x_2048_);
if (v___x_2049_ == 0)
{
lean_dec_ref(v_dynlibs_2039_);
goto v___jp_2042_;
}
else
{
lean_object* v___x_2050_; size_t v___x_2051_; size_t v___x_2052_; lean_object* v___x_2053_; 
v___x_2050_ = lean_box(0);
v___x_2051_ = ((size_t)0ULL);
v___x_2052_ = lean_usize_of_nat(v___x_2048_);
v___x_2053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2039_, v___x_2051_, v___x_2052_, v___x_2050_);
lean_dec_ref(v_dynlibs_2039_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_dec_ref_known(v___x_2053_, 1);
goto v___jp_2042_;
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v_options_2041_);
lean_dec_ref(v_plugins_2040_);
lean_dec(v_importArts_2038_);
lean_dec(v_imports_x3f_2037_);
lean_dec(v_package_x3f_2035_);
lean_dec(v_name_2034_);
lean_dec(v_stx_2016_);
lean_dec_ref(v_plugins_2012_);
lean_dec_ref(v___x_2011_);
lean_dec_ref(v___f_2010_);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
v___jp_2042_:
{
uint8_t v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2016_);
v___x_2044_ = lean_strict_or(v_isModule_2036_, v___x_2043_);
if (lean_obj_tag(v_imports_x3f_2037_) == 0)
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2016_, v___x_2014_);
v___y_2020_ = v___x_2044_;
v___y_2021_ = v_name_2034_;
v___y_2022_ = v_package_x3f_2035_;
v___y_2023_ = v_importArts_2038_;
v___y_2024_ = v_options_2041_;
v___y_2025_ = v_plugins_2040_;
v___y_2026_ = v___x_2045_;
goto v___jp_2019_;
}
else
{
lean_object* v_val_2046_; 
lean_dec(v_stx_2016_);
v_val_2046_ = lean_ctor_get(v_imports_x3f_2037_, 0);
lean_inc(v_val_2046_);
lean_dec_ref_known(v_imports_x3f_2037_, 1);
v___y_2020_ = v___x_2044_;
v___y_2021_ = v_name_2034_;
v___y_2022_ = v_package_x3f_2035_;
v___y_2023_ = v_importArts_2038_;
v___y_2024_ = v_options_2041_;
v___y_2025_ = v_plugins_2040_;
v___y_2026_ = v_val_2046_;
goto v___jp_2019_;
}
}
}
else
{
lean_object* v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_dec_ref(v___f_2010_);
lean_dec(v_setup_x3f_2009_);
v___x_2062_ = lean_box(0);
v___x_2063_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2016_);
v___x_2064_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2016_, v___x_2014_);
v___x_2065_ = lean_box(1);
v___x_2066_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2066_, 0, v_mainModuleName_2015_);
lean_ctor_set(v___x_2066_, 1, v___x_2062_);
lean_ctor_set(v___x_2066_, 2, v___x_2064_);
lean_ctor_set(v___x_2066_, 3, v___x_2011_);
lean_ctor_set(v___x_2066_, 4, v___x_2065_);
lean_ctor_set(v___x_2066_, 5, v_plugins_2012_);
lean_ctor_set_uint8(v___x_2066_, sizeof(void*)*6 + 4, v___x_2063_);
lean_ctor_set_uint32(v___x_2066_, sizeof(void*)*6, v_trustLevel_2013_);
v___x_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
v___jp_2019_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2027_ = l_Lean_LeanOptions_toOptions(v___y_2024_);
v___x_2028_ = l_Lean_Options_mergeBy(v___f_2010_, v___x_2011_, v___x_2027_);
v___x_2029_ = l_Array_append___redArg(v_plugins_2012_, v___y_2025_);
lean_dec_ref(v___y_2025_);
v___x_2030_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2030_, 0, v___y_2021_);
lean_ctor_set(v___x_2030_, 1, v___y_2022_);
lean_ctor_set(v___x_2030_, 2, v___y_2026_);
lean_ctor_set(v___x_2030_, 3, v___x_2028_);
lean_ctor_set(v___x_2030_, 4, v___y_2023_);
lean_ctor_set(v___x_2030_, 5, v___x_2029_);
lean_ctor_set_uint8(v___x_2030_, sizeof(void*)*6 + 4, v___y_2020_);
lean_ctor_set_uint32(v___x_2030_, sizeof(void*)*6, v_trustLevel_2013_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
v___x_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
return v___x_2032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object* v_setup_x3f_2069_, lean_object* v___f_2070_, lean_object* v___x_2071_, lean_object* v_plugins_2072_, lean_object* v_trustLevel_2073_, lean_object* v___x_2074_, lean_object* v_mainModuleName_2075_, lean_object* v_stx_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
uint32_t v_trustLevel_boxed_2079_; uint8_t v___x_6226__boxed_2080_; lean_object* v_res_2081_; 
v_trustLevel_boxed_2079_ = lean_unbox_uint32(v_trustLevel_2073_);
lean_dec(v_trustLevel_2073_);
v___x_6226__boxed_2080_ = lean_unbox(v___x_2074_);
v_res_2081_ = l_Lean_Elab_runFrontend___lam__4(v_setup_x3f_2069_, v___f_2070_, v___x_2071_, v_plugins_2072_, v_trustLevel_boxed_2079_, v___x_6226__boxed_2080_, v_mainModuleName_2075_, v_stx_2076_, v___y_2077_);
lean_dec_ref(v___y_2077_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object* v_val_2082_, lean_object* v_initModIdxs_2083_, lean_object* v___x_2084_){
_start:
{
lean_object* v_cmdState_2086_; lean_object* v_env_2087_; lean_object* v___x_2088_; 
v_cmdState_2086_ = lean_ctor_get(v_val_2082_, 0);
lean_inc_ref(v_cmdState_2086_);
lean_dec_ref(v_val_2082_);
v_env_2087_ = lean_ctor_get(v_cmdState_2086_, 0);
lean_inc_ref(v_env_2087_);
lean_dec_ref(v_cmdState_2086_);
v___x_2088_ = l_Lean_runInitAttrsForModules(v_env_2087_, v_initModIdxs_2083_, v___x_2084_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5___boxed(lean_object* v_val_2089_, lean_object* v_initModIdxs_2090_, lean_object* v___x_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Elab_runFrontend___lam__5(v_val_2089_, v_initModIdxs_2090_, v___x_2091_);
lean_dec_ref(v___x_2091_);
lean_dec_ref(v_initModIdxs_2090_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(size_t v_sz_2094_, size_t v_i_2095_, lean_object* v_bs_2096_){
_start:
{
uint8_t v___x_2097_; 
v___x_2097_ = lean_usize_dec_lt(v_i_2095_, v_sz_2094_);
if (v___x_2097_ == 0)
{
return v_bs_2096_;
}
else
{
lean_object* v_v_2098_; lean_object* v_traces_2099_; lean_object* v___x_2100_; lean_object* v_bs_x27_2101_; size_t v___x_2102_; size_t v___x_2103_; lean_object* v___x_2104_; 
v_v_2098_ = lean_array_uget_borrowed(v_bs_2096_, v_i_2095_);
v_traces_2099_ = lean_ctor_get(v_v_2098_, 3);
lean_inc_ref(v_traces_2099_);
v___x_2100_ = lean_unsigned_to_nat(0u);
v_bs_x27_2101_ = lean_array_uset(v_bs_2096_, v_i_2095_, v___x_2100_);
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_add(v_i_2095_, v___x_2102_);
v___x_2104_ = lean_array_uset(v_bs_x27_2101_, v_i_2095_, v_traces_2099_);
v_i_2095_ = v___x_2103_;
v_bs_2096_ = v___x_2104_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_sz_2106_, lean_object* v_i_2107_, lean_object* v_bs_2108_){
_start:
{
size_t v_sz_boxed_2109_; size_t v_i_boxed_2110_; lean_object* v_res_2111_; 
v_sz_boxed_2109_ = lean_unbox_usize(v_sz_2106_);
lean_dec(v_sz_2106_);
v_i_boxed_2110_ = lean_unbox_usize(v_i_2107_);
lean_dec(v_i_2107_);
v_res_2111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_boxed_2109_, v_i_boxed_2110_, v_bs_2108_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_2112_, size_t v_i_2113_, size_t v_stop_2114_, lean_object* v_b_2115_){
_start:
{
lean_object* v___y_2117_; uint8_t v___x_2121_; 
v___x_2121_ = lean_usize_dec_eq(v_i_2113_, v_stop_2114_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v_infoTree_x3f_2123_; 
v___x_2122_ = lean_array_uget_borrowed(v_as_2112_, v_i_2113_);
v_infoTree_x3f_2123_ = lean_ctor_get(v___x_2122_, 2);
if (lean_obj_tag(v_infoTree_x3f_2123_) == 1)
{
lean_object* v_val_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_val_2124_ = lean_ctor_get(v_infoTree_x3f_2123_, 0);
v___x_2125_ = lean_unsigned_to_nat(1u);
v___x_2126_ = lean_mk_empty_array_with_capacity(v___x_2125_);
lean_inc(v_val_2124_);
v___x_2127_ = lean_array_push(v___x_2126_, v_val_2124_);
v___x_2128_ = l_Array_append___redArg(v_b_2115_, v___x_2127_);
lean_dec_ref(v___x_2127_);
v___y_2117_ = v___x_2128_;
goto v___jp_2116_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_2130_ = l_Array_append___redArg(v_b_2115_, v___x_2129_);
v___y_2117_ = v___x_2130_;
goto v___jp_2116_;
}
}
else
{
return v_b_2115_;
}
v___jp_2116_:
{
size_t v___x_2118_; size_t v___x_2119_; 
v___x_2118_ = ((size_t)1ULL);
v___x_2119_ = lean_usize_add(v_i_2113_, v___x_2118_);
v_i_2113_ = v___x_2119_;
v_b_2115_ = v___y_2117_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_2131_, lean_object* v_i_2132_, lean_object* v_stop_2133_, lean_object* v_b_2134_){
_start:
{
size_t v_i_boxed_2135_; size_t v_stop_boxed_2136_; lean_object* v_res_2137_; 
v_i_boxed_2135_ = lean_unbox_usize(v_i_2132_);
lean_dec(v_i_2132_);
v_stop_boxed_2136_ = lean_unbox_usize(v_stop_2133_);
lean_dec(v_stop_2133_);
v_res_2137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_2131_, v_i_boxed_2135_, v_stop_boxed_2136_, v_b_2134_);
lean_dec_ref(v_as_2131_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(lean_object* v_as_2138_, size_t v_i_2139_, size_t v_stop_2140_, lean_object* v_b_2141_){
_start:
{
uint8_t v___x_2142_; 
v___x_2142_ = lean_usize_dec_eq(v_i_2139_, v_stop_2140_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; size_t v___x_2147_; size_t v___x_2148_; 
v___x_2143_ = lean_array_uget_borrowed(v_as_2138_, v_i_2139_);
v___x_2144_ = 2;
v___x_2145_ = lean_box(v___x_2144_);
lean_inc(v___x_2143_);
v___x_2146_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2143_, v___x_2145_, v_b_2141_);
v___x_2147_ = ((size_t)1ULL);
v___x_2148_ = lean_usize_add(v_i_2139_, v___x_2147_);
v_i_2139_ = v___x_2148_;
v_b_2141_ = v___x_2146_;
goto _start;
}
else
{
return v_b_2141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9___boxed(lean_object* v_as_2150_, lean_object* v_i_2151_, lean_object* v_stop_2152_, lean_object* v_b_2153_){
_start:
{
size_t v_i_boxed_2154_; size_t v_stop_boxed_2155_; lean_object* v_res_2156_; 
v_i_boxed_2154_ = lean_unbox_usize(v_i_2151_);
lean_dec(v_i_2151_);
v_stop_boxed_2155_ = lean_unbox_usize(v_stop_2152_);
lean_dec(v_stop_2152_);
v_res_2156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_as_2150_, v_i_boxed_2154_, v_stop_boxed_2155_, v_b_2153_);
lean_dec_ref(v_as_2150_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_2160_, lean_object* v_k_2161_, uint8_t v_v_2162_){
_start:
{
lean_object* v_map_2163_; uint8_t v_hasTrace_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2178_; 
v_map_2163_ = lean_ctor_get(v_o_2160_, 0);
v_hasTrace_2164_ = lean_ctor_get_uint8(v_o_2160_, sizeof(void*)*1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_o_2160_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2166_ = v_o_2160_;
v_isShared_2167_ = v_isSharedCheck_2178_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_map_2163_);
lean_dec(v_o_2160_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2178_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2168_, 0, v_v_2162_);
lean_inc(v_k_2161_);
v___x_2169_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2161_, v___x_2168_, v_map_2163_);
if (v_hasTrace_2164_ == 0)
{
lean_object* v___x_2170_; uint8_t v___x_2171_; lean_object* v___x_2173_; 
v___x_2170_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_2171_ = l_Lean_Name_isPrefixOf(v___x_2170_, v_k_2161_);
lean_dec(v_k_2161_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2169_);
v___x_2173_ = v___x_2166_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2169_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*1, v___x_2171_);
return v___x_2173_;
}
}
else
{
lean_object* v___x_2176_; 
lean_dec(v_k_2161_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2169_);
v___x_2176_ = v___x_2166_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2169_);
lean_ctor_set_uint8(v_reuseFailAlloc_2177_, sizeof(void*)*1, v_hasTrace_2164_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_2179_, lean_object* v_k_2180_, lean_object* v_v_2181_){
_start:
{
uint8_t v_v_boxed_2182_; lean_object* v_res_2183_; 
v_v_boxed_2182_ = lean_unbox(v_v_2181_);
v_res_2183_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2179_, v_k_2180_, v_v_boxed_2182_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_2184_, lean_object* v_opt_2185_, uint8_t v_val_2186_){
_start:
{
lean_object* v_name_2187_; lean_object* v___x_2188_; 
v_name_2187_ = lean_ctor_get(v_opt_2185_, 0);
lean_inc(v_name_2187_);
lean_dec_ref(v_opt_2185_);
v___x_2188_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_2184_, v_name_2187_, v_val_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_2189_, lean_object* v_opt_2190_, lean_object* v_val_2191_){
_start:
{
uint8_t v_val_boxed_2192_; lean_object* v_res_2193_; 
v_val_boxed_2192_ = lean_unbox(v_val_2191_);
v_res_2193_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2189_, v_opt_2190_, v_val_boxed_2192_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_2194_, lean_object* v_opt_2195_, uint8_t v_val_2196_){
_start:
{
lean_object* v_name_2197_; lean_object* v_map_2198_; uint8_t v___x_2199_; 
v_name_2197_ = lean_ctor_get(v_opt_2195_, 0);
v_map_2198_ = lean_ctor_get(v_opts_2194_, 0);
v___x_2199_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_2197_, v_map_2198_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2194_, v_opt_2195_, v_val_2196_);
return v___x_2200_;
}
else
{
lean_dec_ref(v_opt_2195_);
return v_opts_2194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_2201_, lean_object* v_opt_2202_, lean_object* v_val_2203_){
_start:
{
uint8_t v_val_boxed_2204_; lean_object* v_res_2205_; 
v_val_boxed_2204_ = lean_unbox(v_val_2203_);
v_res_2205_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2201_, v_opt_2202_, v_val_boxed_2204_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0(lean_object* v_a_2206_, lean_object* v_ps_2207_){
_start:
{
lean_object* v_importedEntries_2208_; lean_object* v_state_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2218_; 
v_importedEntries_2208_ = lean_ctor_get(v_ps_2207_, 0);
v_state_2209_ = lean_ctor_get(v_ps_2207_, 1);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_ps_2207_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2211_ = v_ps_2207_;
v_isShared_2212_ = v_isSharedCheck_2218_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_state_2209_);
lean_inc(v_importedEntries_2208_);
lean_dec(v_ps_2207_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2218_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2213_ = lean_task_get_own(v_a_2206_);
v___x_2214_ = l_Array_append___redArg(v_state_2209_, v___x_2213_);
lean_dec(v___x_2213_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 1, v___x_2214_);
v___x_2216_ = v___x_2211_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_importedEntries_2208_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(lean_object* v_as_2219_, size_t v_sz_2220_, size_t v_i_2221_, lean_object* v_b_2222_){
_start:
{
lean_object* v_a_2225_; uint8_t v___x_2229_; 
v___x_2229_ = lean_usize_dec_lt(v_i_2221_, v_sz_2220_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v_b_2222_);
return v___x_2230_;
}
else
{
lean_object* v___x_2231_; lean_object* v_toEnvExtension_2232_; lean_object* v_asyncMode_2233_; uint8_t v_logWrites_2234_; lean_object* v_a_2235_; lean_object* v___f_2236_; lean_object* v___x_2237_; 
v___x_2231_ = l_Lean_Linter_codeQualityLogExt;
v_toEnvExtension_2232_ = lean_ctor_get(v___x_2231_, 0);
v_asyncMode_2233_ = lean_ctor_get(v_toEnvExtension_2232_, 2);
v_logWrites_2234_ = lean_ctor_get_uint8(v_toEnvExtension_2232_, sizeof(void*)*6);
v_a_2235_ = lean_array_uget_borrowed(v_as_2219_, v_i_2221_);
lean_inc(v_a_2235_);
v___f_2236_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2236_, 0, v_a_2235_);
v___x_2237_ = lean_box(0);
if (v_logWrites_2234_ == 0)
{
lean_object* v___x_2238_; 
lean_inc_ref(v_toEnvExtension_2232_);
v___x_2238_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2232_, v_b_2222_, v___f_2236_, v_asyncMode_2233_, v___x_2237_, v___x_2229_);
v_a_2225_ = v___x_2238_;
goto v___jp_2224_;
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_inc_ref_n(v_toEnvExtension_2232_, 2);
v___x_2239_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2232_, v_b_2222_);
lean_dec_ref(v_b_2222_);
v___x_2240_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2232_, v___x_2239_, v___f_2236_, v_asyncMode_2233_, v___x_2237_, v___x_2229_);
v_a_2225_ = v___x_2240_;
goto v___jp_2224_;
}
}
v___jp_2224_:
{
size_t v___x_2226_; size_t v___x_2227_; 
v___x_2226_ = ((size_t)1ULL);
v___x_2227_ = lean_usize_add(v_i_2221_, v___x_2226_);
v_i_2221_ = v___x_2227_;
v_b_2222_ = v_a_2225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object* v_as_2241_, lean_object* v_sz_2242_, lean_object* v_i_2243_, lean_object* v_b_2244_, lean_object* v___y_2245_){
_start:
{
size_t v_sz_boxed_2246_; size_t v_i_boxed_2247_; lean_object* v_res_2248_; 
v_sz_boxed_2246_ = lean_unbox_usize(v_sz_2242_);
lean_dec(v_sz_2242_);
v_i_boxed_2247_ = lean_unbox_usize(v_i_2243_);
lean_dec(v_i_2243_);
v_res_2248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v_as_2241_, v_sz_boxed_2246_, v_i_boxed_2247_, v_b_2244_);
lean_dec_ref(v_as_2241_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(lean_object* v_s_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = l_Lean_Language_Snapshot_transform(v_s_2251_, v___y_2252_);
v___x_2254_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___closed__0));
v___x_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___boxed(lean_object* v_s_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(v_s_2256_, v___y_2257_);
lean_dec_ref(v___y_2257_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(lean_object* v_t_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v___f_2262_; lean_object* v___x_2263_; 
v___f_2262_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___closed__0));
v___x_2263_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2260_, v___f_2262_, v_a_2261_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object* v_t_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_t_2264_, v_a_2265_);
lean_dec_ref(v_a_2265_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(lean_object* v_t_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___closed__0));
v___x_2271_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2268_, v___x_2270_, v_a_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___boxed(lean_object* v_t_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_t_2272_, v_a_2273_);
lean_dec_ref(v_a_2273_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(lean_object* v_s_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_toSnapshot_2277_; lean_object* v_metaSnap_2278_; lean_object* v_result_x3f_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___y_2283_; 
v_toSnapshot_2277_ = lean_ctor_get(v_s_2275_, 0);
lean_inc_ref(v_toSnapshot_2277_);
v_metaSnap_2278_ = lean_ctor_get(v_s_2275_, 1);
lean_inc_ref(v_metaSnap_2278_);
v_result_x3f_2279_ = lean_ctor_get(v_s_2275_, 2);
lean_inc(v_result_x3f_2279_);
lean_dec_ref(v_s_2275_);
v___x_2280_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2277_, v___y_2276_);
v___x_2281_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2278_, v___y_2276_);
if (lean_obj_tag(v_result_x3f_2279_) == 0)
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_box(0);
v___y_2283_ = v___x_2289_;
goto v___jp_2282_;
}
else
{
lean_object* v_val_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2299_; 
v_val_2290_ = lean_ctor_get(v_result_x3f_2279_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v_result_x3f_2279_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2292_ = v_result_x3f_2279_;
v_isShared_2293_ = v_isSharedCheck_2299_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_val_2290_);
lean_dec(v_result_x3f_2279_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2299_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_firstCmdSnap_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
v_firstCmdSnap_2294_ = lean_ctor_get(v_val_2290_, 1);
lean_inc_ref(v_firstCmdSnap_2294_);
lean_dec(v_val_2290_);
v___x_2295_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_firstCmdSnap_2294_, v___y_2276_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2295_);
v___x_2297_ = v___x_2292_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
v___y_2283_ = v___x_2297_;
goto v___jp_2282_;
}
}
}
v___jp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2284_ = lean_unsigned_to_nat(1u);
v___x_2285_ = lean_mk_empty_array_with_capacity(v___x_2284_);
v___x_2286_ = lean_array_push(v___x_2285_, v___x_2281_);
v___x_2287_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2283_, v___x_2286_);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2280_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
return v___x_2288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0___boxed(lean_object* v_s_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(v_s_2300_, v___y_2301_);
lean_dec_ref(v___y_2301_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(lean_object* v_t_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v___f_2306_; lean_object* v___x_2307_; 
v___f_2306_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___closed__0));
v___x_2307_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2304_, v___f_2306_, v_a_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___boxed(lean_object* v_t_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_t_2308_, v_a_2309_);
lean_dec_ref(v_a_2309_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_a_2311_){
_start:
{
lean_object* v_toSnapshot_2312_; lean_object* v_metaSnap_2313_; lean_object* v_result_x3f_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___y_2319_; 
v_toSnapshot_2312_ = lean_ctor_get(v_a_2311_, 0);
lean_inc_ref(v_toSnapshot_2312_);
v_metaSnap_2313_ = lean_ctor_get(v_a_2311_, 1);
lean_inc_ref(v_metaSnap_2313_);
v_result_x3f_2314_ = lean_ctor_get(v_a_2311_, 4);
lean_inc(v_result_x3f_2314_);
lean_dec_ref(v_a_2311_);
v___x_2315_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_2316_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2312_, v___x_2315_);
v___x_2317_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2313_, v___x_2315_);
if (lean_obj_tag(v_result_x3f_2314_) == 0)
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_box(0);
v___y_2319_ = v___x_2325_;
goto v___jp_2318_;
}
else
{
lean_object* v_val_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2335_; 
v_val_2326_ = lean_ctor_get(v_result_x3f_2314_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_result_x3f_2314_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2328_ = v_result_x3f_2314_;
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_val_2326_);
lean_dec(v_result_x3f_2314_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_processedSnap_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v_processedSnap_2330_ = lean_ctor_get(v_val_2326_, 1);
lean_inc_ref(v_processedSnap_2330_);
lean_dec(v_val_2326_);
v___x_2331_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_processedSnap_2330_, v___x_2315_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2331_);
v___x_2333_ = v___x_2328_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
v___y_2319_ = v___x_2333_;
goto v___jp_2318_;
}
}
}
v___jp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2320_ = lean_unsigned_to_nat(1u);
v___x_2321_ = lean_mk_empty_array_with_capacity(v___x_2320_);
v___x_2322_ = lean_array_push(v___x_2321_, v___x_2317_);
v___x_2323_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2319_, v___x_2322_);
v___x_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2316_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
return v___x_2324_;
}
}
}
static double _init_l_Lean_Elab_runFrontend___closed__2(void){
_start:
{
lean_object* v___x_2338_; double v___x_2339_; 
v___x_2338_ = lean_unsigned_to_nat(1000000000u);
v___x_2339_ = lean_float_of_nat(v___x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_2341_, lean_object* v_opts_2342_, lean_object* v_fileName_2343_, lean_object* v_mainModuleName_2344_, uint32_t v_trustLevel_2345_, lean_object* v_oleanFileName_x3f_2346_, lean_object* v_ileanFileName_x3f_2347_, uint8_t v_jsonOutput_2348_, lean_object* v_errorOnKinds_2349_, lean_object* v_plugins_2350_, uint8_t v_printStats_2351_, lean_object* v_setup_x3f_2352_, lean_object* v_incrSaveFileName_x3f_2353_, lean_object* v_incrLoadFileName_x3f_2354_, lean_object* v_incrHeaderSaveFileName_x3f_2355_){
_start:
{
lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___f_2363_; lean_object* v___f_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; double v___x_2367_; double v___x_2368_; double v___x_2369_; uint8_t v___x_2370_; lean_object* v___y_2372_; lean_object* v___y_2373_; size_t v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___y_2435_; lean_object* v___y_2436_; uint8_t v___y_2437_; size_t v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2475_; lean_object* v___y_2476_; uint8_t v___y_2477_; size_t v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2491_; uint8_t v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; uint8_t v___y_2496_; size_t v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2524_; uint8_t v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; uint8_t v___y_2529_; size_t v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2545_; uint8_t v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; uint8_t v___y_2550_; size_t v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; uint8_t v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; uint8_t v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v_a_2642_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v___y_2659_; 
v___f_2363_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___f_2364_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__1));
v___x_2365_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2366_ = lean_io_mono_nanos_now();
v___x_2367_ = lean_float_of_nat(v___x_2366_);
v___x_2368_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__2, &l_Lean_Elab_runFrontend___closed__2_once, _init_l_Lean_Elab_runFrontend___closed__2);
v___x_2369_ = lean_float_div(v___x_2367_, v___x_2368_);
v___x_2370_ = 1;
v___x_2432_ = lean_string_utf8_byte_size(v_input_2341_);
v___x_2433_ = l_Lean_Parser_mkInputContext___redArg(v_input_2341_, v_fileName_2343_, v___x_2370_, v___x_2432_);
v___x_2657_ = l_Lean_internal_cmdlineSnapshots;
if (lean_obj_tag(v_incrSaveFileName_x3f_2353_) == 0)
{
v___y_2659_ = v___x_2370_;
goto v___jp_2658_;
}
else
{
uint8_t v___x_2695_; 
v___x_2695_ = 0;
v___y_2659_ = v___x_2695_;
goto v___jp_2658_;
}
v___jp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = lean_runtime_forget(v___y_2359_);
v___x_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___y_2358_);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
return v___x_2362_;
}
v___jp_2371_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = l_Lean_trace_profiler_output;
v___x_2378_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v___y_2373_, v___x_2377_);
if (lean_obj_tag(v___x_2378_) == 1)
{
lean_object* v_val_2379_; lean_object* v___x_2380_; size_t v_sz_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
lean_dec_ref(v___y_2375_);
v_val_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_val_2379_);
lean_dec_ref_known(v___x_2378_, 1);
lean_inc_ref(v___y_2376_);
v___x_2380_ = l_Lean_Language_SnapshotTree_getAll(v___y_2376_);
v_sz_2381_ = lean_array_size(v___x_2380_);
v___x_2382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2381_, v___y_2374_, v___x_2380_);
v___x_2383_ = l_Lean_Name_toString(v_mainModuleName_2344_, v___x_2370_);
v___x_2384_ = l_Lean_Firefox_Profile_export(v___x_2383_, v___x_2369_, v___x_2382_, v___y_2373_);
lean_dec_ref(v___y_2373_);
lean_dec_ref(v___x_2382_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v___x_2386_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2385_);
v___x_2387_ = l_Lean_Json_compress(v___x_2386_);
v___x_2388_ = l_IO_FS_writeFile(v_val_2379_, v___x_2387_);
lean_dec_ref(v___x_2387_);
lean_dec(v_val_2379_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_dec_ref_known(v___x_2388_, 1);
v___y_2358_ = v___y_2372_;
v___y_2359_ = v___y_2376_;
goto v___jp_2357_;
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v___y_2376_);
lean_dec_ref(v___y_2372_);
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec(v_val_2379_);
lean_dec_ref(v___y_2376_);
lean_dec_ref(v___y_2372_);
v_a_2397_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2384_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2384_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v___x_2405_; uint8_t v___x_2406_; 
lean_dec(v___x_2378_);
v___x_2405_ = l_Lean_trace_profiler_serve;
v___x_2406_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v___y_2375_, v___x_2405_);
lean_dec_ref(v___y_2375_);
if (v___x_2406_ == 0)
{
lean_dec_ref(v___y_2373_);
lean_dec(v_mainModuleName_2344_);
v___y_2358_ = v___y_2372_;
v___y_2359_ = v___y_2376_;
goto v___jp_2357_;
}
else
{
lean_object* v___x_2407_; size_t v_sz_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
lean_inc_ref(v___y_2376_);
v___x_2407_ = l_Lean_Language_SnapshotTree_getAll(v___y_2376_);
v_sz_2408_ = lean_array_size(v___x_2407_);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2408_, v___y_2374_, v___x_2407_);
v___x_2410_ = l_Lean_Name_toString(v_mainModuleName_2344_, v___x_2370_);
v___x_2411_ = l_Lean_Firefox_Profile_export(v___x_2410_, v___x_2369_, v___x_2409_, v___y_2373_);
lean_dec_ref(v___y_2373_);
lean_dec_ref(v___x_2409_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v___x_2413_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2412_);
v___x_2414_ = l_Lean_Json_compress(v___x_2413_);
v___x_2415_ = l_Lean_Firefox_Profile_serve(v___x_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_dec_ref_known(v___x_2415_, 1);
v___y_2358_ = v___y_2372_;
v___y_2359_ = v___y_2376_;
goto v___jp_2357_;
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec_ref(v___y_2376_);
lean_dec_ref(v___y_2372_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec_ref(v___y_2376_);
lean_dec_ref(v___y_2372_);
v_a_2424_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2411_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2411_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
v___jp_2434_:
{
lean_object* v_fileMap_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_fst_2447_; lean_object* v_snd_2448_; lean_object* v_stx_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2469_; 
v_fileMap_2444_ = lean_ctor_get(v___x_2433_, 2);
lean_inc_ref(v_fileMap_2444_);
lean_dec_ref(v___x_2433_);
v___x_2445_ = l_Lean_Server_findModuleRefs(v_fileMap_2444_, v___y_2443_, v___y_2437_, v___y_2437_);
lean_dec_ref(v___y_2443_);
v___x_2446_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_2445_);
v_fst_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_fst_2447_);
v_snd_2448_ = lean_ctor_get(v___x_2446_, 1);
lean_inc(v_snd_2448_);
lean_dec_ref(v___x_2446_);
v_stx_2449_ = lean_ctor_get(v___y_2441_, 3);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___y_2441_);
if (v_isSharedCheck_2469_ == 0)
{
lean_object* v_unused_2470_; lean_object* v_unused_2471_; lean_object* v_unused_2472_; lean_object* v_unused_2473_; 
v_unused_2470_ = lean_ctor_get(v___y_2441_, 4);
lean_dec(v_unused_2470_);
v_unused_2471_ = lean_ctor_get(v___y_2441_, 2);
lean_dec(v_unused_2471_);
v_unused_2472_ = lean_ctor_get(v___y_2441_, 1);
lean_dec(v_unused_2472_);
v_unused_2473_ = lean_ctor_get(v___y_2441_, 0);
lean_dec(v_unused_2473_);
v___x_2451_ = v___y_2441_;
v_isShared_2452_ = v_isSharedCheck_2469_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_stx_2449_);
lean_dec(v___y_2441_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2469_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2453_ = lean_unsigned_to_nat(6u);
v___x_2454_ = l_Lean_Server_collectImports(v_stx_2449_);
lean_inc(v_mainModuleName_2344_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 4, v_snd_2448_);
lean_ctor_set(v___x_2451_, 3, v_fst_2447_);
lean_ctor_set(v___x_2451_, 2, v___x_2454_);
lean_ctor_set(v___x_2451_, 1, v_mainModuleName_2344_);
lean_ctor_set(v___x_2451_, 0, v___x_2453_);
v___x_2456_ = v___x_2451_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_mainModuleName_2344_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2468_, 3, v_fst_2447_);
lean_ctor_set(v_reuseFailAlloc_2468_, 4, v_snd_2448_);
v___x_2456_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = l_Lean_Server_instToJsonIlean_toJson(v___x_2456_);
v___x_2458_ = l_Lean_Json_compress(v___x_2457_);
v___x_2459_ = l_IO_FS_writeFile(v___y_2442_, v___x_2458_);
lean_dec_ref(v___x_2458_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_dec_ref_known(v___x_2459_, 1);
v___y_2372_ = v___y_2435_;
v___y_2373_ = v___y_2436_;
v___y_2374_ = v___y_2438_;
v___y_2375_ = v___y_2439_;
v___y_2376_ = v___y_2440_;
goto v___jp_2371_;
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec_ref(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v_mainModuleName_2344_);
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
}
v___jp_2474_:
{
if (lean_obj_tag(v_ileanFileName_x3f_2347_) == 1)
{
lean_object* v_val_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; uint8_t v___x_2487_; 
v_val_2483_ = lean_ctor_get(v_ileanFileName_x3f_2347_, 0);
lean_inc_ref(v___y_2481_);
v___x_2484_ = l_Lean_Language_SnapshotTree_getAll(v___y_2481_);
v___x_2485_ = lean_mk_empty_array_with_capacity(v___y_2479_);
v___x_2486_ = lean_array_get_size(v___x_2484_);
v___x_2487_ = lean_nat_dec_lt(v___y_2479_, v___x_2486_);
lean_dec(v___y_2479_);
if (v___x_2487_ == 0)
{
lean_dec_ref(v___x_2484_);
v___y_2435_ = v___y_2475_;
v___y_2436_ = v___y_2476_;
v___y_2437_ = v___y_2477_;
v___y_2438_ = v___y_2478_;
v___y_2439_ = v___y_2480_;
v___y_2440_ = v___y_2481_;
v___y_2441_ = v___y_2482_;
v___y_2442_ = v_val_2483_;
v___y_2443_ = v___x_2485_;
goto v___jp_2434_;
}
else
{
size_t v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = lean_usize_of_nat(v___x_2486_);
v___x_2489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v___x_2484_, v___y_2478_, v___x_2488_, v___x_2485_);
lean_dec_ref(v___x_2484_);
v___y_2435_ = v___y_2475_;
v___y_2436_ = v___y_2476_;
v___y_2437_ = v___y_2477_;
v___y_2438_ = v___y_2478_;
v___y_2439_ = v___y_2480_;
v___y_2440_ = v___y_2481_;
v___y_2441_ = v___y_2482_;
v___y_2442_ = v_val_2483_;
v___y_2443_ = v___x_2489_;
goto v___jp_2434_;
}
}
else
{
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2479_);
lean_dec_ref(v___x_2433_);
v___y_2372_ = v___y_2475_;
v___y_2373_ = v___y_2476_;
v___y_2374_ = v___y_2478_;
v___y_2375_ = v___y_2480_;
v___y_2376_ = v___y_2481_;
goto v___jp_2371_;
}
}
v___jp_2490_:
{
if (v___y_2496_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_2346_) == 1)
{
lean_object* v_val_2502_; lean_object* v_fileMap_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___f_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v_val_2502_ = lean_ctor_get(v_oleanFileName_x3f_2346_, 0);
lean_inc(v_val_2502_);
lean_dec_ref_known(v_oleanFileName_x3f_2346_, 1);
v_fileMap_2503_ = lean_ctor_get(v___x_2433_, 2);
v___x_2504_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__3));
v___x_2505_ = lean_box(0);
v___x_2506_ = lean_mk_empty_array_with_capacity(v___y_2498_);
lean_inc_ref(v___y_2500_);
v___x_2507_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___y_2500_, v___x_2505_, v___x_2506_);
v___x_2508_ = lean_box(v___x_2370_);
v___x_2509_ = lean_box(v___y_2492_);
lean_inc_ref(v_fileMap_2503_);
v___f_2510_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2510_, 0, v_fileMap_2503_);
lean_closure_set(v___f_2510_, 1, v___y_2491_);
lean_closure_set(v___f_2510_, 2, v___x_2507_);
lean_closure_set(v___f_2510_, 3, v___y_2493_);
lean_closure_set(v___f_2510_, 4, v_val_2502_);
lean_closure_set(v___f_2510_, 5, v___x_2508_);
lean_closure_set(v___f_2510_, 6, v___x_2509_);
v___x_2511_ = lean_box(0);
v___x_2512_ = l_Lean_profileitIOUnsafe___redArg(v___x_2504_, v___y_2499_, v___f_2510_, v___x_2511_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_dec_ref_known(v___x_2512_, 1);
v___y_2475_ = v___y_2494_;
v___y_2476_ = v___y_2495_;
v___y_2477_ = v___y_2496_;
v___y_2478_ = v___y_2497_;
v___y_2479_ = v___y_2498_;
v___y_2480_ = v___y_2499_;
v___y_2481_ = v___y_2500_;
v___y_2482_ = v___y_2501_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec_ref(v___x_2433_);
lean_dec(v_mainModuleName_2344_);
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
lean_dec_ref(v___y_2493_);
lean_dec_ref(v___y_2491_);
lean_dec(v_oleanFileName_x3f_2346_);
v___y_2475_ = v___y_2494_;
v___y_2476_ = v___y_2495_;
v___y_2477_ = v___y_2496_;
v___y_2478_ = v___y_2497_;
v___y_2479_ = v___y_2498_;
v___y_2480_ = v___y_2499_;
v___y_2481_ = v___y_2500_;
v___y_2482_ = v___y_2501_;
goto v___jp_2474_;
}
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_dec_ref(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v___x_2433_);
lean_dec(v_oleanFileName_x3f_2346_);
lean_dec(v_mainModuleName_2344_);
v___x_2521_ = lean_box(0);
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
return v___x_2522_;
}
}
v___jp_2523_:
{
if (v_printStats_2351_ == 0)
{
v___y_2491_ = v___y_2524_;
v___y_2492_ = v___y_2525_;
v___y_2493_ = v___y_2526_;
v___y_2494_ = v___y_2527_;
v___y_2495_ = v___y_2528_;
v___y_2496_ = v___y_2529_;
v___y_2497_ = v___y_2530_;
v___y_2498_ = v___y_2531_;
v___y_2499_ = v___y_2532_;
v___y_2500_ = v___y_2533_;
v___y_2501_ = v___y_2534_;
goto v___jp_2490_;
}
else
{
lean_object* v___x_2535_; 
lean_inc_ref(v___y_2527_);
v___x_2535_ = l_Lean_Environment_displayStats(v___y_2527_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_dec_ref_known(v___x_2535_, 1);
v___y_2491_ = v___y_2524_;
v___y_2492_ = v___y_2525_;
v___y_2493_ = v___y_2526_;
v___y_2494_ = v___y_2527_;
v___y_2495_ = v___y_2528_;
v___y_2496_ = v___y_2529_;
v___y_2497_ = v___y_2530_;
v___y_2498_ = v___y_2531_;
v___y_2499_ = v___y_2532_;
v___y_2500_ = v___y_2533_;
v___y_2501_ = v___y_2534_;
goto v___jp_2490_;
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec_ref(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___x_2433_);
lean_dec(v_oleanFileName_x3f_2346_);
lean_dec(v_mainModuleName_2344_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
v___jp_2544_:
{
if (lean_obj_tag(v_incrHeaderSaveFileName_x3f_2355_) == 1)
{
lean_object* v_val_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_val_2556_ = lean_ctor_get(v_incrHeaderSaveFileName_x3f_2355_, 0);
lean_inc(v_val_2556_);
lean_dec_ref_known(v_incrHeaderSaveFileName_x3f_2355_, 1);
lean_inc_ref(v___y_2555_);
v___x_2557_ = l_Lean_Language_Lean_truncateToHeader(v___y_2555_);
v___x_2558_ = lean_apply_3(v___y_2548_, v_val_2556_, v___x_2557_, lean_box(0));
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_dec_ref_known(v___x_2558_, 1);
lean_inc_ref(v___y_2545_);
v___y_2524_ = v___y_2545_;
v___y_2525_ = v___y_2546_;
v___y_2526_ = v___y_2547_;
v___y_2527_ = v___y_2545_;
v___y_2528_ = v___y_2549_;
v___y_2529_ = v___y_2550_;
v___y_2530_ = v___y_2551_;
v___y_2531_ = v___y_2552_;
v___y_2532_ = v___y_2553_;
v___y_2533_ = v___y_2554_;
v___y_2534_ = v___y_2555_;
goto v___jp_2523_;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2549_);
lean_dec_ref(v___y_2547_);
lean_dec_ref(v___y_2545_);
lean_dec_ref(v___x_2433_);
lean_dec(v_oleanFileName_x3f_2346_);
lean_dec(v_mainModuleName_2344_);
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
else
{
lean_dec_ref(v___y_2548_);
lean_dec(v_incrHeaderSaveFileName_x3f_2355_);
lean_inc_ref(v___y_2545_);
v___y_2524_ = v___y_2545_;
v___y_2525_ = v___y_2546_;
v___y_2526_ = v___y_2547_;
v___y_2527_ = v___y_2545_;
v___y_2528_ = v___y_2549_;
v___y_2529_ = v___y_2550_;
v___y_2530_ = v___y_2551_;
v___y_2531_ = v___y_2552_;
v___y_2532_ = v___y_2553_;
v___y_2533_ = v___y_2554_;
v___y_2534_ = v___y_2555_;
goto v___jp_2523_;
}
}
v___jp_2567_:
{
size_t v_sz_2577_; size_t v___x_2578_; lean_object* v___x_2579_; 
v_sz_2577_ = lean_array_size(v___y_2576_);
v___x_2578_ = ((size_t)0ULL);
v___x_2579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v___y_2576_, v_sz_2577_, v___x_2578_, v___y_2572_);
lean_dec_ref(v___y_2576_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v___x_2581_; lean_object* v___f_2582_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc_n(v_a_2580_, 2);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2581_ = lean_box(v___x_2370_);
v___f_2582_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2582_, 0, v_a_2580_);
lean_closure_set(v___f_2582_, 1, v___x_2581_);
if (lean_obj_tag(v_incrSaveFileName_x3f_2353_) == 1)
{
lean_object* v_val_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v_val_2583_ = lean_ctor_get(v_incrSaveFileName_x3f_2353_, 0);
lean_inc(v_val_2583_);
lean_dec_ref_known(v_incrSaveFileName_x3f_2353_, 1);
v___x_2584_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___y_2574_);
lean_inc_ref(v___y_2575_);
v___x_2585_ = l_Lean_Elab_runFrontend___lam__2(v_a_2580_, v___x_2370_, v_val_2583_, v___y_2575_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_dec_ref_known(v___x_2585_, 1);
lean_inc_ref(v___y_2569_);
v___y_2545_ = v_a_2580_;
v___y_2546_ = v___y_2568_;
v___y_2547_ = v___y_2569_;
v___y_2548_ = v___f_2582_;
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___y_2571_;
v___y_2551_ = v___x_2578_;
v___y_2552_ = v___y_2573_;
v___y_2553_ = v___y_2569_;
v___y_2554_ = v___y_2574_;
v___y_2555_ = v___y_2575_;
goto v___jp_2544_;
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec_ref(v___f_2582_);
lean_dec(v_a_2580_);
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v___x_2433_);
lean_dec(v_incrHeaderSaveFileName_x3f_2355_);
lean_dec(v_oleanFileName_x3f_2346_);
lean_dec(v_mainModuleName_2344_);
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
lean_dec(v_incrSaveFileName_x3f_2353_);
lean_inc_ref(v___y_2569_);
v___y_2545_ = v_a_2580_;
v___y_2546_ = v___y_2568_;
v___y_2547_ = v___y_2569_;
v___y_2548_ = v___f_2582_;
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___y_2571_;
v___y_2551_ = v___x_2578_;
v___y_2552_ = v___y_2573_;
v___y_2553_ = v___y_2569_;
v___y_2554_ = v___y_2574_;
v___y_2555_ = v___y_2575_;
goto v___jp_2544_;
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec_ref(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v___x_2433_);
lean_dec(v_incrHeaderSaveFileName_x3f_2355_);
lean_dec(v_incrSaveFileName_x3f_2353_);
lean_dec(v_oleanFileName_x3f_2346_);
lean_dec(v_mainModuleName_2344_);
v_a_2594_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2579_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2579_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
v___jp_2602_:
{
lean_object* v___x_2608_; 
lean_inc_ref(v___y_2605_);
v___x_2608_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_2605_, v___y_2603_, v_jsonOutput_2348_, v___y_2607_);
lean_dec(v___y_2607_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2630_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2630_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2630_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; 
lean_inc_ref(v___y_2606_);
v___x_2613_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___y_2606_);
if (lean_obj_tag(v___x_2613_) == 1)
{
lean_object* v_val_2614_; lean_object* v_env_2615_; lean_object* v_scopes_2616_; lean_object* v___x_2617_; lean_object* v_opts_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_del_object(v___x_2611_);
v_val_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_val_2614_);
lean_dec_ref_known(v___x_2613_, 1);
v_env_2615_ = lean_ctor_get(v_val_2614_, 0);
lean_inc_ref(v_env_2615_);
v_scopes_2616_ = lean_ctor_get(v_val_2614_, 2);
lean_inc(v_scopes_2616_);
lean_dec(v_val_2614_);
lean_inc(v___y_2604_);
v___x_2617_ = l_List_get_x21Internal___redArg(v___x_2365_, v_scopes_2616_, v___y_2604_);
lean_dec(v_scopes_2616_);
v_opts_2618_ = lean_ctor_get(v___x_2617_, 1);
lean_inc_ref(v_opts_2618_);
lean_dec(v___x_2617_);
v___x_2619_ = lean_mk_empty_array_with_capacity(v___y_2604_);
lean_inc_ref(v___x_2619_);
lean_inc_ref(v___y_2606_);
v___x_2620_ = l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(v___y_2606_, v___x_2619_, v___f_2364_);
if (lean_obj_tag(v___x_2620_) == 0)
{
uint8_t v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = lean_unbox(v_a_2609_);
v___x_2622_ = lean_unbox(v_a_2609_);
lean_dec(v_a_2609_);
v___y_2568_ = v___x_2621_;
v___y_2569_ = v_opts_2618_;
v___y_2570_ = v___y_2603_;
v___y_2571_ = v___x_2622_;
v___y_2572_ = v_env_2615_;
v___y_2573_ = v___y_2604_;
v___y_2574_ = v___y_2605_;
v___y_2575_ = v___y_2606_;
v___y_2576_ = v___x_2619_;
goto v___jp_2567_;
}
else
{
lean_object* v_val_2623_; uint8_t v___x_2624_; uint8_t v___x_2625_; 
lean_dec_ref(v___x_2619_);
v_val_2623_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_val_2623_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2624_ = lean_unbox(v_a_2609_);
v___x_2625_ = lean_unbox(v_a_2609_);
lean_dec(v_a_2609_);
v___y_2568_ = v___x_2624_;
v___y_2569_ = v_opts_2618_;
v___y_2570_ = v___y_2603_;
v___y_2571_ = v___x_2625_;
v___y_2572_ = v_env_2615_;
v___y_2573_ = v___y_2604_;
v___y_2574_ = v___y_2605_;
v___y_2575_ = v___y_2606_;
v___y_2576_ = v_val_2623_;
goto v___jp_2567_;
}
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
lean_dec(v___x_2613_);
lean_dec(v_a_2609_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v___x_2433_);
lean_dec(v_incrHeaderSaveFileName_x3f_2355_);
lean_dec(v_incrSaveFileName_x3f_2353_);
lean_dec(v_oleanFileName_x3f_2346_);
lean_dec(v_mainModuleName_2344_);
v___x_2626_ = lean_box(0);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2626_);
v___x_2628_ = v___x_2611_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v___x_2433_);
lean_dec(v_incrHeaderSaveFileName_x3f_2355_);
lean_dec(v_incrSaveFileName_x3f_2353_);
lean_dec(v_oleanFileName_x3f_2346_);
lean_dec(v_mainModuleName_2344_);
v_a_2631_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2608_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2608_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
v___jp_2639_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2643_ = l_Lean_Language_Lean_process(v___y_2641_, v_a_2642_, v___x_2433_);
lean_inc_ref(v___x_2643_);
v___x_2644_ = l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(v___x_2643_);
v___x_2645_ = lean_box(1);
v___x_2646_ = lean_unsigned_to_nat(0u);
v___x_2647_ = lean_array_get_size(v_errorOnKinds_2349_);
v___x_2648_ = lean_nat_dec_lt(v___x_2646_, v___x_2647_);
if (v___x_2648_ == 0)
{
v___y_2603_ = v___y_2640_;
v___y_2604_ = v___x_2646_;
v___y_2605_ = v___x_2644_;
v___y_2606_ = v___x_2643_;
v___y_2607_ = v___x_2645_;
goto v___jp_2602_;
}
else
{
size_t v___x_2649_; size_t v___x_2650_; lean_object* v___x_2651_; 
v___x_2649_ = ((size_t)0ULL);
v___x_2650_ = lean_usize_of_nat(v___x_2647_);
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_errorOnKinds_2349_, v___x_2649_, v___x_2650_, v___x_2645_);
v___y_2603_ = v___y_2640_;
v___y_2604_ = v___x_2646_;
v___y_2605_ = v___x_2644_;
v___y_2606_ = v___x_2643_;
v___y_2607_ = v___x_2651_;
goto v___jp_2602_;
}
}
v___jp_2652_:
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_a_2655_);
v___y_2640_ = v___y_2653_;
v___y_2641_ = v___y_2654_;
v_a_2642_ = v___x_2656_;
goto v___jp_2639_;
}
v___jp_2658_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___f_2665_; 
v___x_2660_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2342_, v___x_2657_, v___y_2659_);
v___x_2661_ = l_Lean_Elab_async;
v___x_2662_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_2660_, v___x_2661_, v___x_2370_);
v___x_2663_ = lean_box_uint32(v_trustLevel_2345_);
v___x_2664_ = lean_box(v___x_2370_);
lean_inc(v_mainModuleName_2344_);
lean_inc_ref(v___x_2662_);
v___f_2665_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4___boxed), 10, 7);
lean_closure_set(v___f_2665_, 0, v_setup_x3f_2352_);
lean_closure_set(v___f_2665_, 1, v___f_2363_);
lean_closure_set(v___f_2665_, 2, v___x_2662_);
lean_closure_set(v___f_2665_, 3, v_plugins_2350_);
lean_closure_set(v___f_2665_, 4, v___x_2663_);
lean_closure_set(v___f_2665_, 5, v___x_2664_);
lean_closure_set(v___f_2665_, 6, v_mainModuleName_2344_);
if (lean_obj_tag(v_incrLoadFileName_x3f_2354_) == 0)
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_box(0);
v___y_2640_ = v___x_2662_;
v___y_2641_ = v___f_2665_;
v_a_2642_ = v___x_2666_;
goto v___jp_2639_;
}
else
{
lean_object* v_val_2667_; lean_object* v___x_2668_; 
v_val_2667_ = lean_ctor_get(v_incrLoadFileName_x3f_2354_, 0);
lean_inc(v_val_2667_);
lean_dec_ref_known(v_incrLoadFileName_x3f_2354_, 1);
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
lean_inc(v_mainModuleName_2344_);
v___x_2672_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(v_snap_2670_, v_mainModuleName_2344_);
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
v___y_2653_ = v___x_2662_;
v___y_2654_ = v___f_2665_;
v_a_2655_ = v___x_2672_;
goto v___jp_2652_;
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec_ref(v___x_2672_);
lean_dec_ref(v___f_2665_);
lean_dec_ref(v___x_2662_);
lean_dec_ref(v___x_2433_);
lean_dec(v_incrHeaderSaveFileName_x3f_2355_);
lean_dec(v_incrSaveFileName_x3f_2353_);
lean_dec(v_oleanFileName_x3f_2346_);
lean_dec(v_mainModuleName_2344_);
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
v___y_2653_ = v___x_2662_;
v___y_2654_ = v___f_2665_;
v_a_2655_ = v___x_2672_;
goto v___jp_2652_;
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref(v___f_2665_);
lean_dec_ref(v___x_2662_);
lean_dec_ref(v___x_2433_);
lean_dec(v_incrHeaderSaveFileName_x3f_2355_);
lean_dec(v_incrSaveFileName_x3f_2353_);
lean_dec(v_oleanFileName_x3f_2346_);
lean_dec(v_mainModuleName_2344_);
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
