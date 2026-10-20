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
size_t v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_usize_of_nat(v___x_644_);
v___x_647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v___x_643_, v___x_642_, v___x_646_, v___x_638_);
lean_dec_ref(v___x_643_);
v___y_585_ = v___x_647_;
goto v___jp_584_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___boxed(lean_object* v_inputCtx_648_, lean_object* v_initialSnap_649_, lean_object* v_t_650_, lean_object* v_commands_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_648_, v_initialSnap_649_, v_t_650_, v_commands_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object* v_inputCtx_656_, lean_object* v_parserState_657_, lean_object* v_commandState_658_, lean_object* v_old_x3f_659_){
_start:
{
lean_object* v___y_662_; 
if (lean_obj_tag(v_old_x3f_659_) == 0)
{
lean_object* v___x_667_; 
v___x_667_ = lean_box(0);
v___y_662_ = v___x_667_;
goto v___jp_661_;
}
else
{
lean_object* v_val_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_678_; 
v_val_668_ = lean_ctor_get(v_old_x3f_659_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v_old_x3f_659_);
if (v_isSharedCheck_678_ == 0)
{
v___x_670_ = v_old_x3f_659_;
v_isShared_671_ = v_isSharedCheck_678_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_val_668_);
lean_dec(v_old_x3f_659_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_678_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_inputCtx_672_; lean_object* v_initialSnap_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v_inputCtx_672_ = lean_ctor_get(v_val_668_, 1);
lean_inc_ref(v_inputCtx_672_);
v_initialSnap_673_ = lean_ctor_get(v_val_668_, 2);
lean_inc_ref(v_initialSnap_673_);
lean_dec(v_val_668_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v_inputCtx_672_);
lean_ctor_set(v___x_674_, 1, v_initialSnap_673_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_674_);
v___x_676_ = v___x_670_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
v___y_662_ = v___x_676_;
goto v___jp_661_;
}
}
}
v___jp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_663_ = l_Lean_Language_Lean_processCommands(v_inputCtx_656_, v_parserState_657_, v_commandState_658_, v___y_662_);
lean_inc_ref(v___x_663_);
v___x_664_ = lean_task_get_own(v___x_663_);
v___x_665_ = ((lean_object*)(l_Lean_Elab_IO_processCommandsIncrementally___closed__0));
v___x_666_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_656_, v___x_664_, v___x_663_, v___x_665_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally___boxed(lean_object* v_inputCtx_679_, lean_object* v_parserState_680_, lean_object* v_commandState_681_, lean_object* v_old_x3f_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_679_, v_parserState_680_, v_commandState_681_, v_old_x3f_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object* v_inputCtx_685_, lean_object* v_parserState_686_, lean_object* v_commandState_687_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v_toState_691_; lean_object* v___x_692_; 
v___x_689_ = lean_box(0);
v___x_690_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_685_, v_parserState_686_, v_commandState_687_, v___x_689_);
v_toState_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref(v_toState_691_);
lean_dec_ref(v___x_690_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v_toState_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands___boxed(lean_object* v_inputCtx_693_, lean_object* v_parserState_694_, lean_object* v_commandState_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Elab_IO_processCommands(v_inputCtx_693_, v_parserState_694_, v_commandState_695_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object* v_input_703_, lean_object* v_env_704_, lean_object* v_opts_705_, lean_object* v_fileName_706_){
_start:
{
lean_object* v___y_709_; 
if (lean_obj_tag(v_fileName_706_) == 0)
{
lean_object* v___x_729_; 
v___x_729_ = ((lean_object*)(l_Lean_Elab_process___closed__1));
v___y_709_ = v___x_729_;
goto v___jp_708_;
}
else
{
lean_object* v_val_730_; 
v_val_730_ = lean_ctor_get(v_fileName_706_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v_fileName_706_, 1);
v___y_709_ = v_val_730_;
goto v___jp_708_;
}
v___jp_708_:
{
uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v_inputCtx_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_728_; 
v___x_710_ = 1;
v___x_711_ = lean_string_utf8_byte_size(v_input_703_);
v_inputCtx_712_ = l_Lean_Parser_mkInputContext___redArg(v_input_703_, v___y_709_, v___x_710_, v___x_711_);
v___x_713_ = ((lean_object*)(l_Lean_Elab_process___closed__0));
v___x_714_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
v___x_715_ = l_Lean_Elab_Command_mkState(v_env_704_, v___x_714_, v_opts_705_);
v___x_716_ = l_Lean_Elab_IO_processCommands(v_inputCtx_712_, v___x_713_, v___x_715_);
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_728_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_728_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_728_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_commandState_721_; lean_object* v_env_722_; lean_object* v_messages_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v_commandState_721_ = lean_ctor_get(v_a_717_, 0);
lean_inc_ref(v_commandState_721_);
lean_dec(v_a_717_);
v_env_722_ = lean_ctor_get(v_commandState_721_, 0);
lean_inc_ref(v_env_722_);
v_messages_723_ = lean_ctor_get(v_commandState_721_, 1);
lean_inc_ref(v_messages_723_);
lean_dec_ref(v_commandState_721_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v_env_722_);
lean_ctor_set(v___x_724_, 1, v_messages_723_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_724_);
v___x_726_ = v___x_719_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process___boxed(lean_object* v_input_731_, lean_object* v_env_732_, lean_object* v_opts_733_, lean_object* v_fileName_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Elab_process(v_input_731_, v_env_732_, v_opts_733_, v_fileName_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(lean_object* v_cmdStx_x3f_737_, lean_object* v_as_738_, size_t v_i_739_, size_t v_stop_740_, lean_object* v_b_741_){
_start:
{
lean_object* v___y_743_; uint8_t v___x_747_; 
v___x_747_ = lean_usize_dec_eq(v_i_739_, v_stop_740_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v_stx_x3f_749_; lean_object* v___x_750_; 
v___x_748_ = lean_array_uget_borrowed(v_as_738_, v_i_739_);
v_stx_x3f_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v___x_748_);
v___x_750_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_748_);
if (lean_obj_tag(v_stx_x3f_749_) == 0)
{
lean_object* v___x_751_; 
lean_inc(v_cmdStx_x3f_737_);
v___x_751_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_750_, v_cmdStx_x3f_737_, v_b_741_);
v___y_743_ = v___x_751_;
goto v___jp_742_;
}
else
{
lean_object* v___x_752_; 
lean_inc_ref(v_stx_x3f_749_);
v___x_752_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_750_, v_stx_x3f_749_, v_b_741_);
v___y_743_ = v___x_752_;
goto v___jp_742_;
}
}
else
{
lean_dec(v_cmdStx_x3f_737_);
return v_b_741_;
}
v___jp_742_:
{
size_t v___x_744_; size_t v___x_745_; 
v___x_744_ = ((size_t)1ULL);
v___x_745_ = lean_usize_add(v_i_739_, v___x_744_);
v_i_739_ = v___x_745_;
v_b_741_ = v___y_743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(lean_object* v_t_753_, lean_object* v_cmdStx_x3f_754_, lean_object* v_acc_755_){
_start:
{
lean_object* v_element_756_; lean_object* v_diagnostics_757_; lean_object* v_children_758_; lean_object* v_msgLog_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_773_; 
v_element_756_ = lean_ctor_get(v_t_753_, 0);
v_diagnostics_757_ = lean_ctor_get(v_element_756_, 1);
lean_inc_ref(v_diagnostics_757_);
v_children_758_ = lean_ctor_get(v_t_753_, 1);
lean_inc_ref(v_children_758_);
lean_dec_ref(v_t_753_);
v_msgLog_759_ = lean_ctor_get(v_diagnostics_757_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v_diagnostics_757_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_diagnostics_757_, 1);
lean_dec(v_unused_774_);
v___x_761_ = v_diagnostics_757_;
v_isShared_762_ = v_isSharedCheck_773_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_msgLog_759_);
lean_dec(v_diagnostics_757_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_773_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
lean_inc(v_cmdStx_x3f_754_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v_msgLog_759_);
lean_ctor_set(v___x_761_, 0, v_cmdStx_x3f_754_);
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_cmdStx_x3f_754_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_msgLog_759_);
v___x_764_ = v_reuseFailAlloc_772_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v_acc_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_acc_765_ = lean_array_push(v_acc_755_, v___x_764_);
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = lean_array_get_size(v_children_758_);
v___x_768_ = lean_nat_dec_lt(v___x_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_dec_ref(v_children_758_);
lean_dec(v_cmdStx_x3f_754_);
return v_acc_765_;
}
else
{
size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((size_t)0ULL);
v___x_770_ = lean_usize_of_nat(v___x_767_);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_754_, v_children_758_, v___x_769_, v___x_770_, v_acc_765_);
lean_dec_ref(v_children_758_);
return v___x_771_;
}
}
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
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v_nbuckets_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1005_ = lean_array_get_size(v_data_1004_);
v___x_1006_ = lean_unsigned_to_nat(2u);
v_nbuckets_1007_ = lean_nat_mul(v___x_1005_, v___x_1006_);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_mk_array(v_nbuckets_1007_, v___x_1009_);
v___x_1011_ = lean_array_propagate_mark(v_data_1004_, v___x_1010_);
v___x_1012_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v___x_1008_, v_data_1004_, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object* v_m_1013_, lean_object* v_a_1014_, lean_object* v_b_1015_){
_start:
{
lean_object* v_size_1016_; lean_object* v_buckets_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1060_; 
v_size_1016_ = lean_ctor_get(v_m_1013_, 0);
v_buckets_1017_ = lean_ctor_get(v_m_1013_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_m_1013_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1019_ = v_m_1013_;
v_isShared_1020_ = v_isSharedCheck_1060_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_buckets_1017_);
lean_inc(v_size_1016_);
lean_dec(v_m_1013_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1060_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; uint64_t v___x_1022_; uint64_t v___x_1023_; uint64_t v___x_1024_; uint64_t v_fold_1025_; uint64_t v___x_1026_; uint64_t v___x_1027_; uint64_t v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; size_t v___x_1031_; size_t v___x_1032_; size_t v___x_1033_; lean_object* v_bkt_1034_; uint8_t v___x_1035_; 
v___x_1021_ = lean_array_get_size(v_buckets_1017_);
v___x_1022_ = lean_string_hash(v_a_1014_);
v___x_1023_ = 32ULL;
v___x_1024_ = lean_uint64_shift_right(v___x_1022_, v___x_1023_);
v_fold_1025_ = lean_uint64_xor(v___x_1022_, v___x_1024_);
v___x_1026_ = 16ULL;
v___x_1027_ = lean_uint64_shift_right(v_fold_1025_, v___x_1026_);
v___x_1028_ = lean_uint64_xor(v_fold_1025_, v___x_1027_);
v___x_1029_ = lean_uint64_to_usize(v___x_1028_);
v___x_1030_ = lean_usize_of_nat(v___x_1021_);
v___x_1031_ = ((size_t)1ULL);
v___x_1032_ = lean_usize_sub(v___x_1030_, v___x_1031_);
v___x_1033_ = lean_usize_land(v___x_1029_, v___x_1032_);
v_bkt_1034_ = lean_array_uget_borrowed(v_buckets_1017_, v___x_1033_);
v___x_1035_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1014_, v_bkt_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v_size_x27_1037_; lean_object* v___x_1038_; lean_object* v_buckets_x27_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1036_ = lean_unsigned_to_nat(1u);
v_size_x27_1037_ = lean_nat_add(v_size_1016_, v___x_1036_);
lean_dec(v_size_1016_);
lean_inc(v_bkt_1034_);
v___x_1038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1038_, 0, v_a_1014_);
lean_ctor_set(v___x_1038_, 1, v_b_1015_);
lean_ctor_set(v___x_1038_, 2, v_bkt_1034_);
v_buckets_x27_1039_ = lean_array_uset(v_buckets_1017_, v___x_1033_, v___x_1038_);
v___x_1040_ = lean_unsigned_to_nat(4u);
v___x_1041_ = lean_nat_mul(v_size_x27_1037_, v___x_1040_);
v___x_1042_ = lean_unsigned_to_nat(3u);
v___x_1043_ = lean_nat_div(v___x_1041_, v___x_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_array_get_size(v_buckets_x27_1039_);
v___x_1045_ = lean_nat_dec_le(v___x_1043_, v___x_1044_);
lean_dec(v___x_1043_);
if (v___x_1045_ == 0)
{
lean_object* v_val_1046_; lean_object* v___x_1048_; 
v_val_1046_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_buckets_x27_1039_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_val_1046_);
lean_ctor_set(v___x_1019_, 0, v_size_x27_1037_);
v___x_1048_ = v___x_1019_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_size_x27_1037_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_val_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
else
{
lean_object* v___x_1051_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_buckets_x27_1039_);
lean_ctor_set(v___x_1019_, 0, v_size_x27_1037_);
v___x_1051_ = v___x_1019_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_size_x27_1037_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_buckets_x27_1039_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
else
{
lean_object* v___x_1053_; lean_object* v_buckets_x27_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
lean_inc(v_bkt_1034_);
v___x_1053_ = lean_box(0);
v_buckets_x27_1054_ = lean_array_uset(v_buckets_1017_, v___x_1033_, v___x_1053_);
v___x_1055_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1014_, v_b_1015_, v_bkt_1034_);
v___x_1056_ = lean_array_uset(v_buckets_x27_1054_, v___x_1033_, v___x_1055_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v___x_1056_);
v___x_1058_ = v___x_1019_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_size_1016_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object* v_as_1069_, size_t v_sz_1070_, size_t v_i_1071_, lean_object* v_b_1072_){
_start:
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_usize_dec_lt(v_i_1071_, v_sz_1070_);
if (v___x_1073_ == 0)
{
return v_b_1072_;
}
else
{
lean_object* v_fst_1074_; lean_object* v_snd_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1125_; 
v_fst_1074_ = lean_ctor_get(v_b_1072_, 0);
v_snd_1075_ = lean_ctor_get(v_b_1072_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_b_1072_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1077_ = v_b_1072_;
v_isShared_1078_ = v_isSharedCheck_1125_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_snd_1075_);
lean_inc(v_fst_1074_);
lean_dec(v_b_1072_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1125_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v_order_1082_; lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v_a_1098_; lean_object* v_filePath_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; 
v_a_1098_ = lean_array_uget_borrowed(v_as_1069_, v_i_1071_);
v_filePath_1099_ = lean_ctor_get(v_a_1098_, 0);
lean_inc_ref_n(v_filePath_1099_, 2);
v___f_1100_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1100_, 0, v_filePath_1099_);
v___x_1101_ = l_System_FilePath_extension(v_filePath_1099_);
if (lean_obj_tag(v___x_1101_) == 1)
{
lean_object* v_val_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_val_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_val_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v___x_1103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1));
v___x_1104_ = lean_string_dec_eq(v_val_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2));
v___x_1106_ = lean_string_dec_eq(v_val_1102_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3));
v___x_1108_ = lean_string_dec_eq(v_val_1102_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4));
v___x_1110_ = lean_string_dec_eq(v_val_1102_, v___x_1109_);
lean_dec(v_val_1102_);
if (v___x_1110_ == 0)
{
lean_inc_ref(v_filePath_1099_);
v_fst_1094_ = v_filePath_1099_;
v_snd_1095_ = v___f_1100_;
goto v___jp_1093_;
}
else
{
lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec_ref(v___f_1100_);
lean_inc_ref_n(v_filePath_1099_, 2);
v___f_1111_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1), 2, 1);
lean_closure_set(v___f_1111_, 0, v_filePath_1099_);
v___x_1112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1113_ = l_System_FilePath_withExtension(v_filePath_1099_, v___x_1112_);
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1115_ = l_System_FilePath_withExtension(v___x_1113_, v___x_1114_);
v_fst_1094_ = v___x_1115_;
v_snd_1095_ = v___f_1111_;
goto v___jp_1093_;
}
}
else
{
lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec(v_val_1102_);
lean_dec_ref(v___f_1100_);
lean_inc_ref_n(v_filePath_1099_, 2);
v___f_1116_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2), 2, 1);
lean_closure_set(v___f_1116_, 0, v_filePath_1099_);
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1118_ = l_System_FilePath_withExtension(v_filePath_1099_, v___x_1117_);
v_fst_1094_ = v___x_1118_;
v_snd_1095_ = v___f_1116_;
goto v___jp_1093_;
}
}
else
{
lean_object* v___f_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec(v_val_1102_);
lean_dec_ref(v___f_1100_);
lean_inc_ref_n(v_filePath_1099_, 2);
v___f_1119_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3), 2, 1);
lean_closure_set(v___f_1119_, 0, v_filePath_1099_);
v___x_1120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1121_ = l_System_FilePath_withExtension(v_filePath_1099_, v___x_1120_);
v_fst_1094_ = v___x_1121_;
v_snd_1095_ = v___f_1119_;
goto v___jp_1093_;
}
}
else
{
lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_dec(v_val_1102_);
lean_dec_ref(v___f_1100_);
lean_inc_ref_n(v_filePath_1099_, 2);
v___f_1122_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4), 2, 1);
lean_closure_set(v___f_1122_, 0, v_filePath_1099_);
v___x_1123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1124_ = l_System_FilePath_withExtension(v_filePath_1099_, v___x_1123_);
v_fst_1094_ = v___x_1124_;
v_snd_1095_ = v___f_1122_;
goto v___jp_1093_;
}
}
else
{
lean_dec(v___x_1101_);
lean_inc_ref(v_filePath_1099_);
v_fst_1094_ = v_filePath_1099_;
v_snd_1095_ = v___f_1100_;
goto v___jp_1093_;
}
v___jp_1079_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0));
v___x_1084_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_snd_1075_, v___y_1081_, v___x_1083_);
v___x_1085_ = lean_apply_1(v___y_1080_, v___x_1084_);
v___x_1086_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_snd_1075_, v___y_1081_, v___x_1085_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1086_);
lean_ctor_set(v___x_1077_, 0, v_order_1082_);
v___x_1088_ = v___x_1077_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_order_1082_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
size_t v___x_1089_; size_t v___x_1090_; 
v___x_1089_ = ((size_t)1ULL);
v___x_1090_ = lean_usize_add(v_i_1071_, v___x_1089_);
v_i_1071_ = v___x_1090_;
v_b_1072_ = v___x_1088_;
goto _start;
}
}
v___jp_1093_:
{
uint8_t v___x_1096_; 
v___x_1096_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1075_, v_fst_1094_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_inc_ref(v_fst_1094_);
v___x_1097_ = lean_array_push(v_fst_1074_, v_fst_1094_);
v___y_1080_ = v_snd_1095_;
v___y_1081_ = v_fst_1094_;
v_order_1082_ = v___x_1097_;
goto v___jp_1079_;
}
else
{
v___y_1080_ = v_snd_1095_;
v___y_1081_ = v_fst_1094_;
v_order_1082_ = v_fst_1074_;
goto v___jp_1079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object* v_as_1126_, lean_object* v_sz_1127_, lean_object* v_i_1128_, lean_object* v_b_1129_){
_start:
{
size_t v_sz_boxed_1130_; size_t v_i_boxed_1131_; lean_object* v_res_1132_; 
v_sz_boxed_1130_ = lean_unbox_usize(v_sz_1127_);
lean_dec(v_sz_1127_);
v_i_boxed_1131_ = lean_unbox_usize(v_i_1128_);
lean_dec(v_i_1128_);
v_res_1132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_as_1126_, v_sz_boxed_1130_, v_i_boxed_1131_, v_b_1129_);
lean_dec_ref(v_as_1126_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(lean_object* v_msg_1133_){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1135_ = lean_panic_fn_borrowed(v___x_1134_, v_msg_1133_);
return v___x_1135_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1139_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2));
v___x_1140_ = lean_unsigned_to_nat(11u);
v___x_1141_ = lean_unsigned_to_nat(163u);
v___x_1142_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1));
v___x_1143_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0));
v___x_1144_ = l_mkPanicMessageWithDecl(v___x_1143_, v___x_1142_, v___x_1141_, v___x_1140_, v___x_1139_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(lean_object* v_a_1145_, lean_object* v_x_1146_){
_start:
{
if (lean_obj_tag(v_x_1146_) == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3);
v___x_1148_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(v___x_1147_);
return v___x_1148_;
}
else
{
lean_object* v_key_1149_; lean_object* v_value_1150_; lean_object* v_tail_1151_; uint8_t v___x_1152_; 
v_key_1149_ = lean_ctor_get(v_x_1146_, 0);
v_value_1150_ = lean_ctor_get(v_x_1146_, 1);
v_tail_1151_ = lean_ctor_get(v_x_1146_, 2);
v___x_1152_ = lean_string_dec_eq(v_key_1149_, v_a_1145_);
if (v___x_1152_ == 0)
{
v_x_1146_ = v_tail_1151_;
goto _start;
}
else
{
lean_inc(v_value_1150_);
return v_value_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___boxed(lean_object* v_a_1154_, lean_object* v_x_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1154_, v_x_1155_);
lean_dec(v_x_1155_);
lean_dec_ref(v_a_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object* v_m_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_buckets_1159_; lean_object* v___x_1160_; uint64_t v___x_1161_; uint64_t v___x_1162_; uint64_t v___x_1163_; uint64_t v_fold_1164_; uint64_t v___x_1165_; uint64_t v___x_1166_; uint64_t v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; size_t v___x_1170_; size_t v___x_1171_; size_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_buckets_1159_ = lean_ctor_get(v_m_1157_, 1);
v___x_1160_ = lean_array_get_size(v_buckets_1159_);
v___x_1161_ = lean_string_hash(v_a_1158_);
v___x_1162_ = 32ULL;
v___x_1163_ = lean_uint64_shift_right(v___x_1161_, v___x_1162_);
v_fold_1164_ = lean_uint64_xor(v___x_1161_, v___x_1163_);
v___x_1165_ = 16ULL;
v___x_1166_ = lean_uint64_shift_right(v_fold_1164_, v___x_1165_);
v___x_1167_ = lean_uint64_xor(v_fold_1164_, v___x_1166_);
v___x_1168_ = lean_uint64_to_usize(v___x_1167_);
v___x_1169_ = lean_usize_of_nat(v___x_1160_);
v___x_1170_ = ((size_t)1ULL);
v___x_1171_ = lean_usize_sub(v___x_1169_, v___x_1170_);
v___x_1172_ = lean_usize_land(v___x_1168_, v___x_1171_);
v___x_1173_ = lean_array_uget_borrowed(v_buckets_1159_, v___x_1172_);
v___x_1174_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1158_, v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object* v_m_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v_m_1175_, v_a_1176_);
lean_dec_ref(v_a_1176_);
lean_dec_ref(v_m_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object* v___x_1178_, size_t v_sz_1179_, size_t v_i_1180_, lean_object* v_bs_1181_){
_start:
{
uint8_t v___x_1182_; 
v___x_1182_ = lean_usize_dec_lt(v_i_1180_, v_sz_1179_);
if (v___x_1182_ == 0)
{
return v_bs_1181_;
}
else
{
lean_object* v_v_1183_; lean_object* v___x_1184_; lean_object* v_bs_x27_1185_; lean_object* v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v_v_1183_ = lean_array_uget(v_bs_1181_, v_i_1180_);
v___x_1184_ = lean_unsigned_to_nat(0u);
v_bs_x27_1185_ = lean_array_uset(v_bs_1181_, v_i_1180_, v___x_1184_);
v___x_1186_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v___x_1178_, v_v_1183_);
lean_dec(v_v_1183_);
v___x_1187_ = ((size_t)1ULL);
v___x_1188_ = lean_usize_add(v_i_1180_, v___x_1187_);
v___x_1189_ = lean_array_uset(v_bs_x27_1185_, v_i_1180_, v___x_1186_);
v_i_1180_ = v___x_1188_;
v_bs_1181_ = v___x_1189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object* v___x_1191_, lean_object* v_sz_1192_, lean_object* v_i_1193_, lean_object* v_bs_1194_){
_start:
{
size_t v_sz_boxed_1195_; size_t v_i_boxed_1196_; lean_object* v_res_1197_; 
v_sz_boxed_1195_ = lean_unbox_usize(v_sz_1192_);
lean_dec(v_sz_1192_);
v_i_boxed_1196_ = lean_unbox_usize(v_i_1193_);
lean_dec(v_i_1193_);
v_res_1197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v___x_1191_, v_sz_boxed_1195_, v_i_boxed_1196_, v_bs_1194_);
lean_dec_ref(v___x_1191_);
return v_res_1197_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_unsigned_to_nat(16u);
v___x_1202_ = lean_mk_array(v___x_1201_, v___x_1200_);
return v___x_1202_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_byBase_1205_; 
v___x_1203_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1);
v___x_1204_ = lean_unsigned_to_nat(0u);
v_byBase_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byBase_1205_, 0, v___x_1204_);
lean_ctor_set(v_byBase_1205_, 1, v___x_1203_);
return v_byBase_1205_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3(void){
_start:
{
lean_object* v_byBase_1206_; lean_object* v_order_1207_; lean_object* v___x_1208_; 
v_byBase_1206_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2);
v_order_1207_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0));
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_order_1207_);
lean_ctor_set(v___x_1208_, 1, v_byBase_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object* v_regions_1209_){
_start:
{
lean_object* v___x_1210_; size_t v_sz_1211_; size_t v___x_1212_; lean_object* v___x_1213_; lean_object* v_fst_1214_; lean_object* v_snd_1215_; size_t v_sz_1216_; lean_object* v___x_1217_; 
v___x_1210_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3);
v_sz_1211_ = lean_array_size(v_regions_1209_);
v___x_1212_ = ((size_t)0ULL);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_regions_1209_, v_sz_1211_, v___x_1212_, v___x_1210_);
v_fst_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_fst_1214_);
v_snd_1215_ = lean_ctor_get(v___x_1213_, 1);
lean_inc(v_snd_1215_);
lean_dec_ref(v___x_1213_);
v_sz_1216_ = lean_array_size(v_fst_1214_);
v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v_snd_1215_, v_sz_1216_, v___x_1212_, v_fst_1214_);
lean_dec(v_snd_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object* v_regions_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1218_);
lean_dec_ref(v_regions_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object* v_00_u03b2_1220_, lean_object* v_m_1221_, lean_object* v_a_1222_, lean_object* v_fallback_1223_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_1221_, v_a_1222_, v_fallback_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object* v_00_u03b2_1225_, lean_object* v_m_1226_, lean_object* v_a_1227_, lean_object* v_fallback_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(v_00_u03b2_1225_, v_m_1226_, v_a_1227_, v_fallback_1228_);
lean_dec(v_fallback_1228_);
lean_dec_ref(v_a_1227_);
lean_dec_ref(v_m_1226_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object* v_00_u03b2_1230_, lean_object* v_m_1231_, lean_object* v_a_1232_, lean_object* v_b_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_1231_, v_a_1232_, v_b_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object* v_00_u03b2_1235_, lean_object* v_m_1236_, lean_object* v_a_1237_){
_start:
{
uint8_t v___x_1238_; 
v___x_1238_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_1236_, v_a_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object* v_00_u03b2_1239_, lean_object* v_m_1240_, lean_object* v_a_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(v_00_u03b2_1239_, v_m_1240_, v_a_1241_);
lean_dec_ref(v_a_1241_);
lean_dec_ref(v_m_1240_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object* v_00_u03b2_1244_, lean_object* v_a_1245_, lean_object* v_fallback_1246_, lean_object* v_x_1247_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_1245_, v_fallback_1246_, v_x_1247_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1249_, lean_object* v_a_1250_, lean_object* v_fallback_1251_, lean_object* v_x_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(v_00_u03b2_1249_, v_a_1250_, v_fallback_1251_, v_x_1252_);
lean_dec(v_x_1252_);
lean_dec(v_fallback_1251_);
lean_dec_ref(v_a_1250_);
return v_res_1253_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object* v_00_u03b2_1254_, lean_object* v_a_1255_, lean_object* v_x_1256_){
_start:
{
uint8_t v___x_1257_; 
v___x_1257_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1255_, v_x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1258_, lean_object* v_a_1259_, lean_object* v_x_1260_){
_start:
{
uint8_t v_res_1261_; lean_object* v_r_1262_; 
v_res_1261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(v_00_u03b2_1258_, v_a_1259_, v_x_1260_);
lean_dec(v_x_1260_);
lean_dec_ref(v_a_1259_);
v_r_1262_ = lean_box(v_res_1261_);
return v_r_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3(lean_object* v_00_u03b2_1263_, lean_object* v_data_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_data_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4(lean_object* v_00_u03b2_1266_, lean_object* v_a_1267_, lean_object* v_b_1268_, lean_object* v_x_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1267_, v_b_1268_, v_x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1271_, lean_object* v_i_1272_, lean_object* v_source_1273_, lean_object* v_target_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v_i_1272_, v_source_1273_, v_target_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_x_1277_, v_x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(lean_object* v_as_1280_, size_t v_sz_1281_, size_t v_i_1282_, lean_object* v_b_1283_){
_start:
{
uint8_t v___x_1285_; 
v___x_1285_ = lean_usize_dec_lt(v_i_1282_, v_sz_1281_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v_b_1283_);
return v___x_1286_;
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1288_; 
v_a_1287_ = lean_array_uget_borrowed(v_as_1280_, v_i_1282_);
v___x_1288_ = lean_compacted_region_read(v_a_1287_, v_b_1283_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v_snd_1290_; lean_object* v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v_snd_1290_ = lean_ctor_get(v_a_1289_, 1);
lean_inc(v_snd_1290_);
lean_dec(v_a_1289_);
v___x_1291_ = lean_array_push(v_b_1283_, v_snd_1290_);
v___x_1292_ = ((size_t)1ULL);
v___x_1293_ = lean_usize_add(v_i_1282_, v___x_1292_);
v_i_1282_ = v___x_1293_;
v_b_1283_ = v___x_1291_;
goto _start;
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v_b_1283_);
v_a_1295_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1288_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1288_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0___boxed(lean_object* v_as_1303_, lean_object* v_sz_1304_, lean_object* v_i_1305_, lean_object* v_b_1306_, lean_object* v___y_1307_){
_start:
{
size_t v_sz_boxed_1308_; size_t v_i_boxed_1309_; lean_object* v_res_1310_; 
v_sz_boxed_1308_ = lean_unbox_usize(v_sz_1304_);
lean_dec(v_sz_1304_);
v_i_boxed_1309_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_res_1310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v_as_1303_, v_sz_boxed_1308_, v_i_boxed_1309_, v_b_1306_);
lean_dec_ref(v_as_1303_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(lean_object* v_arts_1313_){
_start:
{
lean_object* v_oleanRegions_1315_; lean_object* v___x_1316_; size_t v_sz_1317_; size_t v___x_1318_; lean_object* v___x_1319_; 
v_oleanRegions_1315_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc_ref(v_arts_1313_);
v___x_1316_ = l_Lean_ModuleArtifacts_oleanParts(v_arts_1313_);
v_sz_1317_ = lean_array_size(v___x_1316_);
v___x_1318_ = ((size_t)0ULL);
v___x_1319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1316_, v_sz_1317_, v___x_1318_, v_oleanRegions_1315_);
lean_dec_ref(v___x_1316_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; size_t v_sz_1322_; lean_object* v___x_1323_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1319_, 1);
v___x_1321_ = l_Lean_ModuleArtifacts_irParts(v_arts_1313_);
v_sz_1322_ = lean_array_size(v___x_1321_);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1321_, v_sz_1322_, v___x_1318_, v_oleanRegions_1315_);
lean_dec_ref(v___x_1321_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1332_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = l_Array_append___redArg(v_a_1320_, v_a_1324_);
lean_dec(v_a_1324_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1328_);
v___x_1330_ = v___x_1326_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
lean_dec(v_a_1320_);
return v___x_1323_;
}
}
else
{
lean_dec_ref(v_arts_1313_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___boxed(lean_object* v_arts_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v_arts_1333_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(lean_object* v_e_1336_){
_start:
{
if (lean_obj_tag(v_e_1336_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1347_; 
v_a_1338_ = lean_ctor_get(v_e_1336_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_e_1336_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1340_ = v_e_1336_;
v_isShared_1341_ = v_isSharedCheck_1347_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v_e_1336_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1347_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1342_ = lean_io_error_to_string(v_a_1338_);
v___x_1343_ = lean_mk_io_user_error(v___x_1342_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set_tag(v___x_1340_, 1);
lean_ctor_set(v___x_1340_, 0, v___x_1343_);
v___x_1345_ = v___x_1340_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
v_a_1348_ = lean_ctor_get(v_e_1336_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_e_1336_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v_e_1336_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v_e_1336_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set_tag(v___x_1350_, 0);
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg___boxed(lean_object* v_e_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1356_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_object* v_00_u03b1_1359_, lean_object* v_e_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_e_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(v_00_u03b1_1363_, v_e_1364_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object* v_a_1367_, lean_object* v___y_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_fst_1371_; lean_object* v_snd_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1400_; 
v_fst_1371_ = lean_ctor_get(v_a_1369_, 0);
v_snd_1372_ = lean_ctor_get(v_a_1369_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_a_1369_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1374_ = v_a_1369_;
v_isShared_1375_ = v_isSharedCheck_1400_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_snd_1372_);
lean_inc(v_fst_1371_);
lean_dec(v_a_1369_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1400_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = lean_array_get_size(v_a_1367_);
v___x_1377_ = lean_nat_dec_lt(v_snd_1372_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1379_; 
if (v_isShared_1375_ == 0)
{
v___x_1379_ = v___x_1374_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_fst_1371_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_snd_1372_);
v___x_1379_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1383_ = lean_array_get_borrowed(v___x_1382_, v_a_1367_, v_snd_1372_);
lean_inc(v___x_1383_);
v___x_1384_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v___x_1383_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = l_Array_append___redArg(v_fst_1371_, v_a_1385_);
lean_dec(v_a_1385_);
v___x_1387_ = lean_nat_add(v_snd_1372_, v___y_1368_);
lean_dec(v_snd_1372_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v___x_1387_);
lean_ctor_set(v___x_1374_, 0, v___x_1386_);
v___x_1389_ = v___x_1374_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
v_a_1369_ = v___x_1389_;
goto _start;
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_del_object(v___x_1374_);
lean_dec(v_snd_1372_);
lean_dec(v_fst_1371_);
v_a_1392_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1384_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1384_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object* v_a_1401_, lean_object* v___y_1402_, lean_object* v_a_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1401_, v___y_1402_, v_a_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v_a_1401_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(lean_object* v_a_1406_, lean_object* v___y_1407_, lean_object* v___x_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1406_, v___y_1407_, v___x_1408_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1419_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1419_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1419_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_fst_1415_; lean_object* v___x_1417_; 
v_fst_1415_ = lean_ctor_get(v_a_1411_, 0);
lean_inc(v_fst_1415_);
lean_dec(v_a_1411_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 1);
lean_ctor_set(v___x_1413_, 0, v_fst_1415_);
v___x_1417_ = v___x_1413_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_fst_1415_);
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
v_a_1420_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1410_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1410_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed(lean_object* v_a_1428_, lean_object* v___y_1429_, lean_object* v___x_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(v_a_1428_, v___y_1429_, v___x_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v_a_1428_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(lean_object* v_upperBound_1433_, lean_object* v_a_1434_, lean_object* v___y_1435_, lean_object* v_a_1436_, lean_object* v_b_1437_){
_start:
{
uint8_t v___x_1439_; 
v___x_1439_ = lean_nat_dec_lt(v_a_1436_, v_upperBound_1433_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
lean_dec(v_a_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v_a_1434_);
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_b_1437_);
return v___x_1440_;
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___f_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1441_ = lean_unsigned_to_nat(0u);
v___x_1442_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc(v_a_1436_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
lean_ctor_set(v___x_1443_, 1, v_a_1436_);
lean_inc(v___y_1435_);
lean_inc_ref(v_a_1434_);
v___f_1444_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1444_, 0, v_a_1434_);
lean_closure_set(v___f_1444_, 1, v___y_1435_);
lean_closure_set(v___f_1444_, 2, v___x_1443_);
v___x_1445_ = lean_io_as_task(v___f_1444_, v___x_1441_);
v___x_1446_ = lean_array_push(v_b_1437_, v___x_1445_);
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_nat_add(v_a_1436_, v___x_1447_);
lean_dec(v_a_1436_);
v_a_1436_ = v___x_1448_;
v_b_1437_ = v___x_1446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___boxed(lean_object* v_upperBound_1450_, lean_object* v_a_1451_, lean_object* v___y_1452_, lean_object* v_a_1453_, lean_object* v_b_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1450_, v_a_1451_, v___y_1452_, v_a_1453_, v_b_1454_);
lean_dec(v_upperBound_1450_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(lean_object* v_as_1457_, size_t v_sz_1458_, size_t v_i_1459_, lean_object* v_b_1460_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_usize_dec_lt(v_i_1459_, v_sz_1458_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_b_1460_);
return v___x_1463_;
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_a_1464_ = lean_array_uget_borrowed(v_as_1457_, v_i_1459_);
lean_inc(v_a_1464_);
v___x_1465_ = lean_task_get_own(v_a_1464_);
v___x_1466_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v___x_1465_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; size_t v___x_1469_; size_t v___x_1470_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
v___x_1468_ = l_Array_append___redArg(v_b_1460_, v_a_1467_);
lean_dec(v_a_1467_);
v___x_1469_ = ((size_t)1ULL);
v___x_1470_ = lean_usize_add(v_i_1459_, v___x_1469_);
v_i_1459_ = v___x_1470_;
v_b_1460_ = v___x_1468_;
goto _start;
}
else
{
lean_dec_ref(v_b_1460_);
return v___x_1466_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2___boxed(lean_object* v_as_1472_, lean_object* v_sz_1473_, lean_object* v_i_1474_, lean_object* v_b_1475_, lean_object* v___y_1476_){
_start:
{
size_t v_sz_boxed_1477_; size_t v_i_boxed_1478_; lean_object* v_res_1479_; 
v_sz_boxed_1477_ = lean_unbox_usize(v_sz_1473_);
lean_dec(v_sz_1473_);
v_i_boxed_1478_ = lean_unbox_usize(v_i_1474_);
lean_dec(v_i_1474_);
v_res_1479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_as_1472_, v_sz_boxed_1477_, v_i_boxed_1478_, v_b_1475_);
lean_dec_ref(v_as_1472_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t v_sz_1480_, size_t v_i_1481_, lean_object* v_bs_1482_){
_start:
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_usize_dec_lt(v_i_1481_, v_sz_1480_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v_bs_1482_);
return v___x_1484_;
}
else
{
lean_object* v_v_1485_; lean_object* v___x_1486_; 
v_v_1485_ = lean_array_uget_borrowed(v_bs_1482_, v_i_1481_);
lean_inc(v_v_1485_);
v___x_1486_ = l_Lean_instFromJsonModuleArtifacts_fromJson(v_v_1485_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v_bs_1482_);
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1496_; lean_object* v_bs_x27_1497_; size_t v___x_1498_; size_t v___x_1499_; lean_object* v___x_1500_; 
v_a_1495_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1486_, 1);
v___x_1496_ = lean_unsigned_to_nat(0u);
v_bs_x27_1497_ = lean_array_uset(v_bs_1482_, v_i_1481_, v___x_1496_);
v___x_1498_ = ((size_t)1ULL);
v___x_1499_ = lean_usize_add(v_i_1481_, v___x_1498_);
v___x_1500_ = lean_array_uset(v_bs_x27_1497_, v_i_1481_, v_a_1495_);
v_i_1481_ = v___x_1499_;
v_bs_1482_ = v___x_1500_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object* v_sz_1502_, lean_object* v_i_1503_, lean_object* v_bs_1504_){
_start:
{
size_t v_sz_boxed_1505_; size_t v_i_boxed_1506_; lean_object* v_res_1507_; 
v_sz_boxed_1505_ = lean_unbox_usize(v_sz_1502_);
lean_dec(v_sz_1502_);
v_i_boxed_1506_ = lean_unbox_usize(v_i_1503_);
lean_dec(v_i_1503_);
v_res_1507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_boxed_1505_, v_i_boxed_1506_, v_bs_1504_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object* v_x_1510_){
_start:
{
if (lean_obj_tag(v_x_1510_) == 4)
{
lean_object* v_elems_1511_; size_t v_sz_1512_; size_t v___x_1513_; lean_object* v___x_1514_; 
v_elems_1511_ = lean_ctor_get(v_x_1510_, 0);
lean_inc_ref(v_elems_1511_);
lean_dec_ref_known(v_x_1510_, 1);
v_sz_1512_ = lean_array_size(v_elems_1511_);
v___x_1513_ = ((size_t)0ULL);
v___x_1514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_1512_, v___x_1513_, v_elems_1511_);
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1515_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0));
v___x_1516_ = lean_unsigned_to_nat(80u);
v___x_1517_ = l_Lean_Json_pretty(v_x_1510_, v___x_1516_);
v___x_1518_ = lean_string_append(v___x_1515_, v___x_1517_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1));
v___x_1520_ = lean_string_append(v___x_1518_, v___x_1519_);
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
return v___x_1521_;
}
}
}
static uint32_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3(void){
_start:
{
lean_object* v___x_1525_; uint32_t v___x_1526_; 
v___x_1525_ = lean_box(0);
v___x_1526_ = lean_internal_get_hardware_concurrency(v___x_1525_);
return v___x_1526_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4(void){
_start:
{
uint32_t v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = lean_uint32_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3);
v___x_1528_ = lean_uint32_to_nat(v___x_1527_);
return v___x_1528_;
}
}
static uint8_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1530_ = lean_unsigned_to_nat(4u);
v___x_1531_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1532_ = lean_nat_dec_le(v___x_1531_, v___x_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(lean_object* v_fname_1533_){
_start:
{
lean_object* v___x_1535_; lean_object* v_depsFile_1536_; lean_object* v___x_1537_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
lean_inc_ref(v_fname_1533_);
v_depsFile_1536_ = l_System_FilePath_addExtension(v_fname_1533_, v___x_1535_);
v___x_1537_ = l_IO_FS_readFile(v_depsFile_1536_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1624_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1624_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1624_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_a_1543_; lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_Json_parse(v_a_1538_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; 
lean_dec_ref(v_fname_1533_);
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v_a_1543_ = v_a_1554_;
goto v___jp_1542_;
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1556_; 
v_a_1555_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1556_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(v_a_1555_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; 
lean_dec_ref(v_fname_1533_);
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v_a_1543_ = v_a_1557_;
goto v___jp_1542_;
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___y_1562_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1613_; uint8_t v___x_1623_; 
lean_del_object(v___x_1540_);
lean_dec_ref(v_depsFile_1536_);
v_a_1558_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1559_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1560_ = lean_unsigned_to_nat(4u);
v___x_1623_ = lean_uint8_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6);
if (v___x_1623_ == 0)
{
v___y_1613_ = v___x_1560_;
goto v___jp_1612_;
}
else
{
v___y_1613_ = v___x_1559_;
goto v___jp_1612_;
}
v___jp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1563_ = lean_mk_empty_array_with_capacity(v___y_1562_);
v___x_1564_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_1558_);
lean_inc(v___y_1562_);
v___x_1565_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v___y_1562_, v_a_1558_, v___y_1562_, v___x_1564_, v___x_1563_);
lean_dec(v___y_1562_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; size_t v_sz_1570_; size_t v___x_1571_; lean_object* v___x_1572_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1567_ = lean_array_get_size(v_a_1558_);
lean_dec(v_a_1558_);
v___x_1568_ = lean_nat_mul(v___x_1567_, v___x_1560_);
v___x_1569_ = lean_mk_empty_array_with_capacity(v___x_1568_);
lean_dec(v___x_1568_);
v_sz_1570_ = lean_array_size(v_a_1566_);
v___x_1571_ = ((size_t)0ULL);
v___x_1572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_a_1566_, v_sz_1570_, v___x_1571_, v___x_1569_);
lean_dec(v_a_1566_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1574_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v___x_1574_ = lean_compacted_region_read(v_fname_1533_, v_a_1573_);
lean_dec(v_a_1573_);
lean_dec_ref(v_fname_1533_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1583_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1583_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1583_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v_fst_1579_; lean_object* v___x_1581_; 
v_fst_1579_ = lean_ctor_get(v_a_1575_, 0);
lean_inc(v_fst_1579_);
lean_dec(v_a_1575_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v_fst_1579_);
v___x_1581_ = v___x_1577_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_fst_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
v_a_1584_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1574_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1574_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec_ref(v_fname_1533_);
v_a_1592_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1572_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1572_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_a_1558_);
lean_dec_ref(v_fname_1533_);
v_a_1600_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1565_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1565_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
v___jp_1608_:
{
uint8_t v___x_1611_; 
v___x_1611_ = lean_nat_dec_le(v___y_1609_, v___y_1610_);
if (v___x_1611_ == 0)
{
lean_dec(v___y_1610_);
v___y_1562_ = v___y_1609_;
goto v___jp_1561_;
}
else
{
lean_dec(v___y_1609_);
v___y_1562_ = v___y_1610_;
goto v___jp_1561_;
}
}
v___jp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1614_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5));
v___x_1615_ = lean_io_getenv(v___x_1614_);
v___x_1616_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v___x_1615_) == 0)
{
v___y_1609_ = v___x_1616_;
v___y_1610_ = v___y_1613_;
goto v___jp_1608_;
}
else
{
lean_object* v_val_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_val_1617_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1619_ = lean_string_utf8_byte_size(v_val_1617_);
v___x_1620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1620_, 0, v_val_1617_);
lean_ctor_set(v___x_1620_, 1, v___x_1618_);
lean_ctor_set(v___x_1620_, 2, v___x_1619_);
v___x_1621_ = l_String_Slice_toNat_x3f(v___x_1620_);
lean_dec_ref_known(v___x_1620_, 3);
if (lean_obj_tag(v___x_1621_) == 0)
{
v___y_1609_ = v___x_1616_;
v___y_1610_ = v___y_1613_;
goto v___jp_1608_;
}
else
{
lean_object* v_val_1622_; 
lean_dec(v___y_1613_);
v_val_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_val_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___y_1609_ = v___x_1616_;
v___y_1610_ = v_val_1622_;
goto v___jp_1608_;
}
}
}
}
}
v___jp_1542_:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1544_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1));
v___x_1545_ = lean_string_append(v___x_1544_, v_depsFile_1536_);
lean_dec_ref(v_depsFile_1536_);
v___x_1546_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2));
v___x_1547_ = lean_string_append(v___x_1545_, v___x_1546_);
v___x_1548_ = lean_string_append(v___x_1547_, v_a_1543_);
lean_dec_ref(v_a_1543_);
v___x_1549_ = lean_mk_io_user_error(v___x_1548_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 1);
lean_ctor_set(v___x_1540_, 0, v___x_1549_);
v___x_1551_ = v___x_1540_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v_depsFile_1536_);
lean_dec_ref(v_fname_1533_);
v_a_1625_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1537_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1537_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___boxed(lean_object* v_fname_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_fname_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object* v_a_1636_, lean_object* v___y_1637_, lean_object* v_inst_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1636_, v___y_1637_, v_a_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object* v_a_1642_, lean_object* v___y_1643_, lean_object* v_inst_1644_, lean_object* v_a_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(v_a_1642_, v___y_1643_, v_inst_1644_, v_a_1645_);
lean_dec(v___y_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object* v_upperBound_1648_, lean_object* v_a_1649_, lean_object* v___y_1650_, lean_object* v_inst_1651_, lean_object* v_R_1652_, lean_object* v_a_1653_, lean_object* v_b_1654_, lean_object* v_c_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1648_, v_a_1649_, v___y_1650_, v_a_1653_, v_b_1654_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object* v_upperBound_1658_, lean_object* v_a_1659_, lean_object* v___y_1660_, lean_object* v_inst_1661_, lean_object* v_R_1662_, lean_object* v_a_1663_, lean_object* v_b_1664_, lean_object* v_c_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(v_upperBound_1658_, v_a_1659_, v___y_1660_, v_inst_1661_, v_R_1662_, v_a_1663_, v_b_1664_, v_c_1665_);
lean_dec(v_upperBound_1658_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object* v_as_1668_, size_t v_sz_1669_, size_t v_i_1670_, lean_object* v_b_1671_){
_start:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_usize_dec_lt(v_i_1670_, v_sz_1669_);
if (v___x_1673_ == 0)
{
return v_b_1671_;
}
else
{
lean_object* v_a_1674_; lean_object* v_cancelTk_x3f_1675_; lean_object* v___x_1676_; 
v_a_1674_ = lean_array_uget_borrowed(v_as_1668_, v_i_1670_);
v_cancelTk_x3f_1675_ = lean_ctor_get(v_a_1674_, 2);
v___x_1676_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_1675_) == 1)
{
lean_object* v_val_1683_; lean_object* v___x_1684_; 
v_val_1683_ = lean_ctor_get(v_cancelTk_x3f_1675_, 0);
v___x_1684_ = l_IO_CancelToken_set(v_val_1683_);
goto v___jp_1677_;
}
else
{
goto v___jp_1677_;
}
v___jp_1677_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; size_t v___x_1680_; size_t v___x_1681_; 
lean_inc(v_a_1674_);
v___x_1678_ = l_Lean_Language_SnapshotTask_get___redArg(v_a_1674_);
v___x_1679_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___x_1678_);
lean_dec(v___x_1678_);
v___x_1680_ = ((size_t)1ULL);
v___x_1681_ = lean_usize_add(v_i_1670_, v___x_1680_);
v_i_1670_ = v___x_1681_;
v_b_1671_ = v___x_1676_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object* v_s_1685_){
_start:
{
lean_object* v_children_1687_; lean_object* v___x_1688_; size_t v_sz_1689_; size_t v___x_1690_; lean_object* v___x_1691_; 
v_children_1687_ = lean_ctor_get(v_s_1685_, 1);
v___x_1688_ = lean_box(0);
v_sz_1689_ = lean_array_size(v_children_1687_);
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_children_1687_, v_sz_1689_, v___x_1690_, v___x_1688_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object* v_s_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v_s_1692_);
lean_dec_ref(v_s_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object* v_as_1695_, lean_object* v_sz_1696_, lean_object* v_i_1697_, lean_object* v_b_1698_, lean_object* v___y_1699_){
_start:
{
size_t v_sz_boxed_1700_; size_t v_i_boxed_1701_; lean_object* v_res_1702_; 
v_sz_boxed_1700_ = lean_unbox_usize(v_sz_1696_);
lean_dec(v_sz_1696_);
v_i_boxed_1701_ = lean_unbox_usize(v_i_1697_);
lean_dec(v_i_1697_);
v_res_1702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_as_1695_, v_sz_boxed_1700_, v_i_boxed_1701_, v_b_1698_);
lean_dec_ref(v_as_1695_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(lean_object* v_snap_1703_, lean_object* v_m_1704_){
_start:
{
lean_object* v_result_x3f_1705_; 
v_result_x3f_1705_ = lean_ctor_get(v_snap_1703_, 4);
lean_inc(v_result_x3f_1705_);
if (lean_obj_tag(v_result_x3f_1705_) == 1)
{
lean_object* v_val_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1806_; 
v_val_1706_ = lean_ctor_get(v_result_x3f_1705_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_result_x3f_1705_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1708_ = v_result_x3f_1705_;
v_isShared_1709_ = v_isSharedCheck_1806_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_val_1706_);
lean_dec(v_result_x3f_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1806_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v_toSnapshot_1710_; lean_object* v_metaSnap_1711_; lean_object* v_ictx_1712_; lean_object* v_stx_1713_; lean_object* v_parserState_1714_; lean_object* v_processedSnap_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1805_; 
v_toSnapshot_1710_ = lean_ctor_get(v_snap_1703_, 0);
v_metaSnap_1711_ = lean_ctor_get(v_snap_1703_, 1);
v_ictx_1712_ = lean_ctor_get(v_snap_1703_, 2);
v_stx_1713_ = lean_ctor_get(v_snap_1703_, 3);
v_parserState_1714_ = lean_ctor_get(v_val_1706_, 0);
v_processedSnap_1715_ = lean_ctor_get(v_val_1706_, 1);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_val_1706_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1717_ = v_val_1706_;
v_isShared_1718_ = v_isSharedCheck_1805_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_processedSnap_1715_);
lean_inc(v_parserState_1714_);
lean_dec(v_val_1706_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1805_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v_processed_1719_; lean_object* v_result_x3f_1720_; 
v_processed_1719_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_1715_);
v_result_x3f_1720_ = lean_ctor_get(v_processed_1719_, 2);
lean_inc(v_result_x3f_1720_);
if (lean_obj_tag(v_result_x3f_1720_) == 1)
{
lean_object* v_val_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1804_; 
v_val_1721_ = lean_ctor_get(v_result_x3f_1720_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_result_x3f_1720_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1723_ = v_result_x3f_1720_;
v_isShared_1724_ = v_isSharedCheck_1804_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_val_1721_);
lean_dec(v_result_x3f_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1804_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_cmdState_1725_; lean_object* v_toSnapshot_1726_; lean_object* v_metaSnap_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1802_; 
v_cmdState_1725_ = lean_ctor_get(v_val_1721_, 0);
lean_inc_ref(v_cmdState_1725_);
v_toSnapshot_1726_ = lean_ctor_get(v_processed_1719_, 0);
v_metaSnap_1727_ = lean_ctor_get(v_processed_1719_, 1);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_processed_1719_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v_processed_1719_, 2);
lean_dec(v_unused_1803_);
v___x_1729_ = v_processed_1719_;
v_isShared_1730_ = v_isSharedCheck_1802_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_metaSnap_1727_);
lean_inc(v_toSnapshot_1726_);
lean_dec(v_processed_1719_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1802_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v_firstCmdSnap_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1800_; 
v_firstCmdSnap_1731_ = lean_ctor_get(v_val_1721_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_val_1721_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_val_1721_, 0);
lean_dec(v_unused_1801_);
v___x_1733_ = v_val_1721_;
v_isShared_1734_ = v_isSharedCheck_1800_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_firstCmdSnap_1731_);
lean_dec(v_val_1721_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1800_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v_env_1735_; lean_object* v_messages_1736_; lean_object* v_scopes_1737_; lean_object* v_usedQuotCtxts_1738_; lean_object* v_nextMacroScope_1739_; lean_object* v_maxRecDepth_1740_; lean_object* v_ngen_1741_; lean_object* v_auxDeclNGen_1742_; lean_object* v_infoState_1743_; lean_object* v_traceState_1744_; lean_object* v_snapshotTasks_1745_; lean_object* v_prevLinterStates_1746_; lean_object* v_codeQualityEntryTasks_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1799_; 
v_env_1735_ = lean_ctor_get(v_cmdState_1725_, 0);
v_messages_1736_ = lean_ctor_get(v_cmdState_1725_, 1);
v_scopes_1737_ = lean_ctor_get(v_cmdState_1725_, 2);
v_usedQuotCtxts_1738_ = lean_ctor_get(v_cmdState_1725_, 3);
v_nextMacroScope_1739_ = lean_ctor_get(v_cmdState_1725_, 4);
v_maxRecDepth_1740_ = lean_ctor_get(v_cmdState_1725_, 5);
v_ngen_1741_ = lean_ctor_get(v_cmdState_1725_, 6);
v_auxDeclNGen_1742_ = lean_ctor_get(v_cmdState_1725_, 7);
v_infoState_1743_ = lean_ctor_get(v_cmdState_1725_, 8);
v_traceState_1744_ = lean_ctor_get(v_cmdState_1725_, 9);
v_snapshotTasks_1745_ = lean_ctor_get(v_cmdState_1725_, 10);
v_prevLinterStates_1746_ = lean_ctor_get(v_cmdState_1725_, 11);
v_codeQualityEntryTasks_1747_ = lean_ctor_get(v_cmdState_1725_, 12);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_cmdState_1725_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1749_ = v_cmdState_1725_;
v_isShared_1750_ = v_isSharedCheck_1799_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1747_);
lean_inc(v_prevLinterStates_1746_);
lean_inc(v_snapshotTasks_1745_);
lean_inc(v_traceState_1744_);
lean_inc(v_infoState_1743_);
lean_inc(v_auxDeclNGen_1742_);
lean_inc(v_ngen_1741_);
lean_inc(v_maxRecDepth_1740_);
lean_inc(v_nextMacroScope_1739_);
lean_inc(v_usedQuotCtxts_1738_);
lean_inc(v_scopes_1737_);
lean_inc(v_messages_1736_);
lean_inc(v_env_1735_);
lean_dec(v_cmdState_1725_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1799_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v_mainModule_1752_; uint8_t v___x_1753_; 
v___x_1751_ = l_Lean_Environment_header(v_env_1735_);
v_mainModule_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_mainModule_1752_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = lean_name_eq(v_mainModule_1752_, v_m_1704_);
lean_dec(v_mainModule_1752_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1793_; 
lean_inc(v_stx_1713_);
lean_inc_ref(v_ictx_1712_);
lean_inc_ref(v_metaSnap_1711_);
lean_inc_ref(v_toSnapshot_1710_);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_snap_1703_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; lean_object* v_unused_1795_; lean_object* v_unused_1796_; lean_object* v_unused_1797_; lean_object* v_unused_1798_; 
v_unused_1794_ = lean_ctor_get(v_snap_1703_, 4);
lean_dec(v_unused_1794_);
v_unused_1795_ = lean_ctor_get(v_snap_1703_, 3);
lean_dec(v_unused_1795_);
v_unused_1796_ = lean_ctor_get(v_snap_1703_, 2);
lean_dec(v_unused_1796_);
v_unused_1797_ = lean_ctor_get(v_snap_1703_, 1);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_snap_1703_, 0);
lean_dec(v_unused_1798_);
v___x_1755_ = v_snap_1703_;
v_isShared_1756_ = v_isSharedCheck_1793_;
goto v_resetjp_1754_;
}
else
{
lean_dec(v_snap_1703_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1793_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v_idx_1757_; lean_object* v_parentIdxs_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1791_; 
v_idx_1757_ = lean_ctor_get(v_auxDeclNGen_1742_, 1);
v_parentIdxs_1758_ = lean_ctor_get(v_auxDeclNGen_1742_, 2);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_auxDeclNGen_1742_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v_auxDeclNGen_1742_, 0);
lean_dec(v_unused_1792_);
v___x_1760_ = v_auxDeclNGen_1742_;
v_isShared_1761_ = v_isSharedCheck_1791_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_parentIdxs_1758_);
lean_inc(v_idx_1757_);
lean_dec(v_auxDeclNGen_1742_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1791_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_newEnv_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v_newEnv_1762_ = l_Lean_Environment_setMainModule(v_env_1735_, v_m_1704_);
v___x_1763_ = lean_box(0);
v___x_1764_ = l_Lean_mkPrivateName(v_newEnv_1762_, v___x_1763_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1764_);
v___x_1766_ = v___x_1760_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_idx_1757_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_parentIdxs_1758_);
v___x_1766_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v_newCmdState_1768_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 7, v___x_1766_);
lean_ctor_set(v___x_1749_, 0, v_newEnv_1762_);
v_newCmdState_1768_ = v___x_1749_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_newEnv_1762_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_messages_1736_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_scopes_1737_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_usedQuotCtxts_1738_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v_nextMacroScope_1739_);
lean_ctor_set(v_reuseFailAlloc_1789_, 5, v_maxRecDepth_1740_);
lean_ctor_set(v_reuseFailAlloc_1789_, 6, v_ngen_1741_);
lean_ctor_set(v_reuseFailAlloc_1789_, 7, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1789_, 8, v_infoState_1743_);
lean_ctor_set(v_reuseFailAlloc_1789_, 9, v_traceState_1744_);
lean_ctor_set(v_reuseFailAlloc_1789_, 10, v_snapshotTasks_1745_);
lean_ctor_set(v_reuseFailAlloc_1789_, 11, v_prevLinterStates_1746_);
lean_ctor_set(v_reuseFailAlloc_1789_, 12, v_codeQualityEntryTasks_1747_);
v_newCmdState_1768_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1770_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v_newCmdState_1768_);
v___x_1770_ = v___x_1733_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_newCmdState_1768_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_firstCmdSnap_1731_);
v___x_1770_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1770_);
v___x_1772_ = v___x_1723_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v_newProcessed_1774_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 2, v___x_1772_);
v_newProcessed_1774_ = v___x_1729_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_toSnapshot_1726_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_metaSnap_1727_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v___x_1772_);
v_newProcessed_1774_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1775_ = lean_box(0);
v___x_1776_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1775_, v_newProcessed_1774_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v___x_1776_);
v___x_1778_ = v___x_1717_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_parserState_1714_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1780_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1778_);
v___x_1780_ = v___x_1708_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1782_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 4, v___x_1780_);
v___x_1782_ = v___x_1755_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_toSnapshot_1710_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_metaSnap_1711_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_ictx_1712_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v_stx_1713_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
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
lean_del_object(v___x_1749_);
lean_dec_ref(v_codeQualityEntryTasks_1747_);
lean_dec(v_prevLinterStates_1746_);
lean_dec_ref(v_snapshotTasks_1745_);
lean_dec_ref(v_traceState_1744_);
lean_dec_ref(v_infoState_1743_);
lean_dec_ref(v_auxDeclNGen_1742_);
lean_dec_ref(v_ngen_1741_);
lean_dec(v_maxRecDepth_1740_);
lean_dec(v_nextMacroScope_1739_);
lean_dec(v_usedQuotCtxts_1738_);
lean_dec(v_scopes_1737_);
lean_dec_ref(v_messages_1736_);
lean_dec_ref(v_env_1735_);
lean_del_object(v___x_1733_);
lean_dec_ref(v_firstCmdSnap_1731_);
lean_del_object(v___x_1729_);
lean_dec_ref(v_metaSnap_1727_);
lean_dec_ref(v_toSnapshot_1726_);
lean_del_object(v___x_1723_);
lean_del_object(v___x_1717_);
lean_dec_ref(v_parserState_1714_);
lean_del_object(v___x_1708_);
lean_dec(v_m_1704_);
return v_snap_1703_;
}
}
}
}
}
}
else
{
lean_dec(v_result_x3f_1720_);
lean_dec(v_processed_1719_);
lean_del_object(v___x_1717_);
lean_dec_ref(v_parserState_1714_);
lean_del_object(v___x_1708_);
lean_dec(v_m_1704_);
return v_snap_1703_;
}
}
}
}
else
{
lean_dec(v_result_x3f_1705_);
lean_dec(v_m_1704_);
return v_snap_1703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object* v_incrFile_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_incrFile_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object* v_incrFile_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(v_incrFile_1810_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object* v_opts_1813_, lean_object* v_incr_1814_, lean_object* v_res_1815_){
_start:
{
lean_object* v_cmdState_1817_; lean_object* v_env_1818_; lean_object* v_initModIdxs_1819_; lean_object* v___x_1820_; 
v_cmdState_1817_ = lean_ctor_get(v_res_1815_, 0);
lean_inc_ref(v_cmdState_1817_);
lean_dec_ref(v_res_1815_);
v_env_1818_ = lean_ctor_get(v_cmdState_1817_, 0);
lean_inc_ref(v_env_1818_);
lean_dec_ref(v_cmdState_1817_);
v_initModIdxs_1819_ = lean_ctor_get(v_incr_1814_, 1);
v___x_1820_ = l_Lean_runInitAttrsForModules(v_env_1818_, v_initModIdxs_1819_, v_opts_1813_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object* v_opts_1821_, lean_object* v_incr_1822_, lean_object* v_res_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(v_opts_1821_, v_incr_1822_, v_res_1823_);
lean_dec_ref(v_incr_1822_);
lean_dec_ref(v_opts_1821_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7(){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_enable_initializer_execution();
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(lean_object* v_env_1833_, lean_object* v_incrFile_1834_, lean_object* v_toSave_1835_){
_start:
{
lean_object* v___x_1837_; lean_object* v_regions_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; 
v___x_1837_ = l_Lean_Environment_header(v_env_1833_);
v_regions_1838_ = lean_ctor_get(v___x_1837_, 2);
lean_inc_ref(v_regions_1838_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1840_ = lean_box(0);
v___x_1841_ = 1;
v___x_1842_ = lean_compacted_region_save(v_incrFile_1834_, v___x_1839_, v_toSave_1835_, v_regions_1838_, v___x_1840_, v___x_1841_);
lean_dec_ref(v_regions_1838_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___boxed(lean_object* v_env_1843_, lean_object* v_incrFile_1844_, lean_object* v_toSave_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(v_env_1843_, v_incrFile_1844_, v_toSave_1845_);
lean_dec_ref(v_toSave_1845_);
lean_dec_ref(v_incrFile_1844_);
lean_dec_ref(v_env_1843_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_opts_1848_, lean_object* v_opt_1849_){
_start:
{
lean_object* v_name_1850_; lean_object* v_map_1851_; lean_object* v___x_1852_; 
v_name_1850_ = lean_ctor_get(v_opt_1849_, 0);
v_map_1851_ = lean_ctor_get(v_opts_1848_, 0);
v___x_1852_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1851_, v_name_1850_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_box(0);
return v___x_1853_;
}
else
{
lean_object* v_val_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1863_; 
v_val_1854_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1856_ = v___x_1852_;
v_isShared_1857_ = v_isSharedCheck_1863_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_val_1854_);
lean_dec(v___x_1852_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1863_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
if (lean_obj_tag(v_val_1854_) == 0)
{
lean_object* v_v_1858_; lean_object* v___x_1860_; 
v_v_1858_ = lean_ctor_get(v_val_1854_, 0);
lean_inc_ref(v_v_1858_);
lean_dec_ref_known(v_val_1854_, 1);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v_v_1858_);
v___x_1860_ = v___x_1856_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_v_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
else
{
lean_object* v___x_1862_; 
lean_del_object(v___x_1856_);
lean_dec(v_val_1854_);
v___x_1862_ = lean_box(0);
return v___x_1862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_opts_1864_, lean_object* v_opt_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v_opts_1864_, v_opt_1865_);
lean_dec_ref(v_opt_1865_);
lean_dec_ref(v_opts_1864_);
return v_res_1866_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_opts_1867_, lean_object* v_opt_1868_){
_start:
{
lean_object* v_name_1869_; lean_object* v_defValue_1870_; lean_object* v_map_1871_; lean_object* v___x_1872_; 
v_name_1869_ = lean_ctor_get(v_opt_1868_, 0);
v_defValue_1870_ = lean_ctor_get(v_opt_1868_, 1);
v_map_1871_ = lean_ctor_get(v_opts_1867_, 0);
v___x_1872_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1871_, v_name_1869_);
if (lean_obj_tag(v___x_1872_) == 0)
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_unbox(v_defValue_1870_);
return v___x_1873_;
}
else
{
lean_object* v_val_1874_; 
v_val_1874_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_val_1874_);
lean_dec_ref_known(v___x_1872_, 1);
if (lean_obj_tag(v_val_1874_) == 1)
{
uint8_t v_v_1875_; 
v_v_1875_ = lean_ctor_get_uint8(v_val_1874_, 0);
lean_dec_ref_known(v_val_1874_, 0);
return v_v_1875_;
}
else
{
uint8_t v___x_1876_; 
lean_dec(v_val_1874_);
v___x_1876_ = lean_unbox(v_defValue_1870_);
return v___x_1876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_opts_1877_, lean_object* v_opt_1878_){
_start:
{
uint8_t v_res_1879_; lean_object* v_r_1880_; 
v_res_1879_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1877_, v_opt_1878_);
lean_dec_ref(v_opt_1878_);
lean_dec_ref(v_opts_1877_);
v_r_1880_ = lean_box(v_res_1879_);
return v_r_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_1881_, lean_object* v_x_1882_, lean_object* v_hOpt_1883_){
_start:
{
lean_inc_ref(v_hOpt_1883_);
return v_hOpt_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v_hOpt_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_Elab_runFrontend___lam__0(v_x_1884_, v_x_1885_, v_hOpt_1886_);
lean_dec_ref(v_hOpt_1886_);
lean_dec_ref(v_x_1885_);
lean_dec(v_x_1884_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_x1_1888_, lean_object* v_x2_1889_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(size_t v_sz_1895_, size_t v_i_1896_, lean_object* v_bs_1897_){
_start:
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_usize_dec_lt(v_i_1896_, v_sz_1895_);
if (v___x_1898_ == 0)
{
return v_bs_1897_;
}
else
{
lean_object* v_v_1899_; lean_object* v___x_1900_; lean_object* v_bs_x27_1901_; lean_object* v___x_1902_; size_t v___x_1903_; size_t v___x_1904_; lean_object* v___x_1905_; 
v_v_1899_ = lean_array_uget(v_bs_1897_, v_i_1896_);
v___x_1900_ = lean_unsigned_to_nat(0u);
v_bs_x27_1901_ = lean_array_uset(v_bs_1897_, v_i_1896_, v___x_1900_);
v___x_1902_ = l_Lean_instToJsonModuleArtifacts_toJson(v_v_1899_);
v___x_1903_ = ((size_t)1ULL);
v___x_1904_ = lean_usize_add(v_i_1896_, v___x_1903_);
v___x_1905_ = lean_array_uset(v_bs_x27_1901_, v_i_1896_, v___x_1902_);
v_i_1896_ = v___x_1904_;
v_bs_1897_ = v___x_1905_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11___boxed(lean_object* v_sz_1907_, lean_object* v_i_1908_, lean_object* v_bs_1909_){
_start:
{
size_t v_sz_boxed_1910_; size_t v_i_boxed_1911_; lean_object* v_res_1912_; 
v_sz_boxed_1910_ = lean_unbox_usize(v_sz_1907_);
lean_dec(v_sz_1907_);
v_i_boxed_1911_ = lean_unbox_usize(v_i_1908_);
lean_dec(v_i_1908_);
v_res_1912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(v_sz_boxed_1910_, v_i_boxed_1911_, v_bs_1909_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8(lean_object* v_a_1913_){
_start:
{
size_t v_sz_1914_; size_t v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_sz_1914_ = lean_array_size(v_a_1913_);
v___x_1915_ = ((size_t)0ULL);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(v_sz_1914_, v___x_1915_, v_a_1913_);
v___x_1917_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_a_1918_, uint8_t v___x_1919_, lean_object* v_incrFile_1920_, lean_object* v_snapToSave_1921_){
_start:
{
lean_object* v___x_1923_; lean_object* v_regions_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1923_ = l_Lean_Environment_header(v_a_1918_);
v_regions_1924_ = lean_ctor_get(v___x_1923_, 2);
lean_inc_ref(v_regions_1924_);
lean_dec_ref(v___x_1923_);
v___x_1925_ = l_Lean_getRegularInitAttrModIdxs(v_a_1918_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v_snapToSave_1921_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_compacted_region_save(v_incrFile_1920_, v___x_1927_, v___x_1926_, v_regions_1924_, v___x_1928_, v___x_1919_);
lean_dec_ref_known(v___x_1926_, 2);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1931_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1924_);
lean_dec_ref(v_regions_1924_);
v___x_1932_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
v___x_1933_ = l_System_FilePath_addExtension(v_incrFile_1920_, v___x_1932_);
v___x_1934_ = l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8(v___x_1931_);
v___x_1935_ = l_Lean_Json_compress(v___x_1934_);
v___x_1936_ = l_IO_FS_writeFile(v___x_1933_, v___x_1935_);
lean_dec_ref(v___x_1935_);
lean_dec_ref(v___x_1933_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1944_; 
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; 
v_unused_1945_ = lean_ctor_get(v___x_1936_, 0);
lean_dec(v_unused_1945_);
v___x_1938_ = v___x_1936_;
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
else
{
lean_dec(v___x_1936_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_runtime_forget(v_a_1930_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
else
{
lean_dec(v_a_1930_);
return v___x_1936_;
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v_regions_1924_);
lean_dec_ref(v_incrFile_1920_);
v_a_1946_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1929_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1929_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object* v_a_1954_, lean_object* v___x_1955_, lean_object* v_incrFile_1956_, lean_object* v_snapToSave_1957_, lean_object* v___y_1958_){
_start:
{
uint8_t v___x_6105__boxed_1959_; lean_object* v_res_1960_; 
v___x_6105__boxed_1959_ = lean_unbox(v___x_1955_);
v_res_1960_ = l_Lean_Elab_runFrontend___lam__2(v_a_1954_, v___x_6105__boxed_1959_, v_incrFile_1956_, v_snapToSave_1957_);
lean_dec_ref(v_a_1954_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_fileMap_1961_, lean_object* v_a_1962_, lean_object* v___x_1963_, lean_object* v_opts_1964_, lean_object* v_val_1965_, uint8_t v___x_1966_, uint8_t v_a_1967_){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1969_ = l_Lean_Linter_recordLints(v_fileMap_1961_, v_a_1962_, v___x_1963_);
v___x_1970_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1971_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1964_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_writeModule(v___x_1969_, v_val_1965_, v___x_1966_);
return v___x_1972_;
}
else
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_writeModule(v___x_1969_, v_val_1965_, v_a_1967_);
return v___x_1973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_fileMap_1974_, lean_object* v_a_1975_, lean_object* v___x_1976_, lean_object* v_opts_1977_, lean_object* v_val_1978_, lean_object* v___x_1979_, lean_object* v_a_1980_, lean_object* v___y_1981_){
_start:
{
uint8_t v___x_6179__boxed_1982_; uint8_t v_a_6180__boxed_1983_; lean_object* v_res_1984_; 
v___x_6179__boxed_1982_ = lean_unbox(v___x_1979_);
v_a_6180__boxed_1983_ = lean_unbox(v_a_1980_);
v_res_1984_ = l_Lean_Elab_runFrontend___lam__3(v_fileMap_1974_, v_a_1975_, v___x_1976_, v_opts_1977_, v_val_1978_, v___x_6179__boxed_1982_, v_a_6180__boxed_1983_);
lean_dec_ref(v_opts_1977_);
lean_dec_ref(v___x_1976_);
lean_dec_ref(v_fileMap_1974_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_1985_, size_t v_i_1986_, size_t v_stop_1987_, lean_object* v_b_1988_){
_start:
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_usize_dec_eq(v_i_1986_, v_stop_1987_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = lean_array_uget_borrowed(v_as_1985_, v_i_1986_);
lean_inc(v___x_1991_);
v___x_1992_ = lean_load_dynlib(v___x_1991_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; size_t v___x_1994_; size_t v___x_1995_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_1994_ = ((size_t)1ULL);
v___x_1995_ = lean_usize_add(v_i_1986_, v___x_1994_);
v_i_1986_ = v___x_1995_;
v_b_1988_ = v_a_1993_;
goto _start;
}
else
{
return v___x_1992_;
}
}
else
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_b_1988_);
return v___x_1997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_1998_, lean_object* v_i_1999_, lean_object* v_stop_2000_, lean_object* v_b_2001_, lean_object* v___y_2002_){
_start:
{
size_t v_i_boxed_2003_; size_t v_stop_boxed_2004_; lean_object* v_res_2005_; 
v_i_boxed_2003_ = lean_unbox_usize(v_i_1999_);
lean_dec(v_i_1999_);
v_stop_boxed_2004_ = lean_unbox_usize(v_stop_2000_);
lean_dec(v_stop_2000_);
v_res_2005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_1998_, v_i_boxed_2003_, v_stop_boxed_2004_, v_b_2001_);
lean_dec_ref(v_as_1998_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* v_setup_x3f_2006_, lean_object* v___f_2007_, lean_object* v___x_2008_, lean_object* v_plugins_2009_, uint32_t v_trustLevel_2010_, uint8_t v___x_2011_, lean_object* v_mainModuleName_2012_, lean_object* v_stx_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v___y_2023_; 
if (lean_obj_tag(v_setup_x3f_2006_) == 1)
{
lean_object* v_val_2030_; lean_object* v_name_2031_; lean_object* v_package_x3f_2032_; uint8_t v_isModule_2033_; lean_object* v_imports_x3f_2034_; lean_object* v_importArts_2035_; lean_object* v_dynlibs_2036_; lean_object* v_plugins_2037_; lean_object* v_options_2038_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
lean_dec(v_mainModuleName_2012_);
v_val_2030_ = lean_ctor_get(v_setup_x3f_2006_, 0);
lean_inc(v_val_2030_);
lean_dec_ref_known(v_setup_x3f_2006_, 1);
v_name_2031_ = lean_ctor_get(v_val_2030_, 0);
lean_inc(v_name_2031_);
v_package_x3f_2032_ = lean_ctor_get(v_val_2030_, 1);
lean_inc(v_package_x3f_2032_);
v_isModule_2033_ = lean_ctor_get_uint8(v_val_2030_, sizeof(void*)*7);
v_imports_x3f_2034_ = lean_ctor_get(v_val_2030_, 2);
lean_inc(v_imports_x3f_2034_);
v_importArts_2035_ = lean_ctor_get(v_val_2030_, 3);
lean_inc(v_importArts_2035_);
v_dynlibs_2036_ = lean_ctor_get(v_val_2030_, 4);
lean_inc_ref(v_dynlibs_2036_);
v_plugins_2037_ = lean_ctor_get(v_val_2030_, 5);
lean_inc_ref(v_plugins_2037_);
v_options_2038_ = lean_ctor_get(v_val_2030_, 6);
lean_inc(v_options_2038_);
lean_dec(v_val_2030_);
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = lean_array_get_size(v_dynlibs_2036_);
v___x_2046_ = lean_nat_dec_lt(v___x_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_dec_ref(v_dynlibs_2036_);
goto v___jp_2039_;
}
else
{
lean_object* v___x_2047_; size_t v___x_2048_; size_t v___x_2049_; lean_object* v___x_2050_; 
v___x_2047_ = lean_box(0);
v___x_2048_ = ((size_t)0ULL);
v___x_2049_ = lean_usize_of_nat(v___x_2045_);
v___x_2050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2036_, v___x_2048_, v___x_2049_, v___x_2047_);
lean_dec_ref(v_dynlibs_2036_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_dec_ref_known(v___x_2050_, 1);
goto v___jp_2039_;
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_options_2038_);
lean_dec_ref(v_plugins_2037_);
lean_dec(v_importArts_2035_);
lean_dec(v_imports_x3f_2034_);
lean_dec(v_package_x3f_2032_);
lean_dec(v_name_2031_);
lean_dec(v_stx_2013_);
lean_dec_ref(v_plugins_2009_);
lean_dec_ref(v___x_2008_);
lean_dec_ref(v___f_2007_);
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
v___jp_2039_:
{
uint8_t v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2013_);
v___x_2041_ = lean_strict_or(v_isModule_2033_, v___x_2040_);
if (lean_obj_tag(v_imports_x3f_2034_) == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2013_, v___x_2011_);
v___y_2017_ = v_name_2031_;
v___y_2018_ = v_options_2038_;
v___y_2019_ = v_package_x3f_2032_;
v___y_2020_ = v_importArts_2035_;
v___y_2021_ = v_plugins_2037_;
v___y_2022_ = v___x_2041_;
v___y_2023_ = v___x_2042_;
goto v___jp_2016_;
}
else
{
lean_object* v_val_2043_; 
lean_dec(v_stx_2013_);
v_val_2043_ = lean_ctor_get(v_imports_x3f_2034_, 0);
lean_inc(v_val_2043_);
lean_dec_ref_known(v_imports_x3f_2034_, 1);
v___y_2017_ = v_name_2031_;
v___y_2018_ = v_options_2038_;
v___y_2019_ = v_package_x3f_2032_;
v___y_2020_ = v_importArts_2035_;
v___y_2021_ = v_plugins_2037_;
v___y_2022_ = v___x_2041_;
v___y_2023_ = v_val_2043_;
goto v___jp_2016_;
}
}
}
else
{
lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_dec_ref(v___f_2007_);
lean_dec(v_setup_x3f_2006_);
v___x_2059_ = lean_box(0);
v___x_2060_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2013_);
v___x_2061_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2013_, v___x_2011_);
v___x_2062_ = lean_box(1);
v___x_2063_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2063_, 0, v_mainModuleName_2012_);
lean_ctor_set(v___x_2063_, 1, v___x_2059_);
lean_ctor_set(v___x_2063_, 2, v___x_2061_);
lean_ctor_set(v___x_2063_, 3, v___x_2008_);
lean_ctor_set(v___x_2063_, 4, v___x_2062_);
lean_ctor_set(v___x_2063_, 5, v_plugins_2009_);
lean_ctor_set_uint8(v___x_2063_, sizeof(void*)*6 + 4, v___x_2060_);
lean_ctor_set_uint32(v___x_2063_, sizeof(void*)*6, v_trustLevel_2010_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
return v___x_2065_;
}
v___jp_2016_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2024_ = l_Lean_LeanOptions_toOptions(v___y_2018_);
v___x_2025_ = l_Lean_Options_mergeBy(v___f_2007_, v___x_2008_, v___x_2024_);
v___x_2026_ = l_Array_append___redArg(v_plugins_2009_, v___y_2021_);
lean_dec_ref(v___y_2021_);
v___x_2027_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2027_, 0, v___y_2017_);
lean_ctor_set(v___x_2027_, 1, v___y_2019_);
lean_ctor_set(v___x_2027_, 2, v___y_2023_);
lean_ctor_set(v___x_2027_, 3, v___x_2025_);
lean_ctor_set(v___x_2027_, 4, v___y_2020_);
lean_ctor_set(v___x_2027_, 5, v___x_2026_);
lean_ctor_set_uint8(v___x_2027_, sizeof(void*)*6 + 4, v___y_2022_);
lean_ctor_set_uint32(v___x_2027_, sizeof(void*)*6, v_trustLevel_2010_);
v___x_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
v___x_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
return v___x_2029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object* v_setup_x3f_2066_, lean_object* v___f_2067_, lean_object* v___x_2068_, lean_object* v_plugins_2069_, lean_object* v_trustLevel_2070_, lean_object* v___x_2071_, lean_object* v_mainModuleName_2072_, lean_object* v_stx_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
uint32_t v_trustLevel_boxed_2076_; uint8_t v___x_6226__boxed_2077_; lean_object* v_res_2078_; 
v_trustLevel_boxed_2076_ = lean_unbox_uint32(v_trustLevel_2070_);
lean_dec(v_trustLevel_2070_);
v___x_6226__boxed_2077_ = lean_unbox(v___x_2071_);
v_res_2078_ = l_Lean_Elab_runFrontend___lam__4(v_setup_x3f_2066_, v___f_2067_, v___x_2068_, v_plugins_2069_, v_trustLevel_boxed_2076_, v___x_6226__boxed_2077_, v_mainModuleName_2072_, v_stx_2073_, v___y_2074_);
lean_dec_ref(v___y_2074_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object* v_val_2079_, lean_object* v_initModIdxs_2080_, lean_object* v___x_2081_){
_start:
{
lean_object* v_cmdState_2083_; lean_object* v_env_2084_; lean_object* v___x_2085_; 
v_cmdState_2083_ = lean_ctor_get(v_val_2079_, 0);
lean_inc_ref(v_cmdState_2083_);
lean_dec_ref(v_val_2079_);
v_env_2084_ = lean_ctor_get(v_cmdState_2083_, 0);
lean_inc_ref(v_env_2084_);
lean_dec_ref(v_cmdState_2083_);
v___x_2085_ = l_Lean_runInitAttrsForModules(v_env_2084_, v_initModIdxs_2080_, v___x_2081_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5___boxed(lean_object* v_val_2086_, lean_object* v_initModIdxs_2087_, lean_object* v___x_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Elab_runFrontend___lam__5(v_val_2086_, v_initModIdxs_2087_, v___x_2088_);
lean_dec_ref(v___x_2088_);
lean_dec_ref(v_initModIdxs_2087_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(size_t v_sz_2091_, size_t v_i_2092_, lean_object* v_bs_2093_){
_start:
{
uint8_t v___x_2094_; 
v___x_2094_ = lean_usize_dec_lt(v_i_2092_, v_sz_2091_);
if (v___x_2094_ == 0)
{
return v_bs_2093_;
}
else
{
lean_object* v_v_2095_; lean_object* v_traces_2096_; lean_object* v___x_2097_; lean_object* v_bs_x27_2098_; size_t v___x_2099_; size_t v___x_2100_; lean_object* v___x_2101_; 
v_v_2095_ = lean_array_uget_borrowed(v_bs_2093_, v_i_2092_);
v_traces_2096_ = lean_ctor_get(v_v_2095_, 3);
lean_inc_ref(v_traces_2096_);
v___x_2097_ = lean_unsigned_to_nat(0u);
v_bs_x27_2098_ = lean_array_uset(v_bs_2093_, v_i_2092_, v___x_2097_);
v___x_2099_ = ((size_t)1ULL);
v___x_2100_ = lean_usize_add(v_i_2092_, v___x_2099_);
v___x_2101_ = lean_array_uset(v_bs_x27_2098_, v_i_2092_, v_traces_2096_);
v_i_2092_ = v___x_2100_;
v_bs_2093_ = v___x_2101_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_sz_2103_, lean_object* v_i_2104_, lean_object* v_bs_2105_){
_start:
{
size_t v_sz_boxed_2106_; size_t v_i_boxed_2107_; lean_object* v_res_2108_; 
v_sz_boxed_2106_ = lean_unbox_usize(v_sz_2103_);
lean_dec(v_sz_2103_);
v_i_boxed_2107_ = lean_unbox_usize(v_i_2104_);
lean_dec(v_i_2104_);
v_res_2108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_boxed_2106_, v_i_boxed_2107_, v_bs_2105_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_2109_, size_t v_i_2110_, size_t v_stop_2111_, lean_object* v_b_2112_){
_start:
{
lean_object* v___y_2114_; uint8_t v___x_2118_; 
v___x_2118_ = lean_usize_dec_eq(v_i_2110_, v_stop_2111_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v_infoTree_x3f_2120_; 
v___x_2119_ = lean_array_uget_borrowed(v_as_2109_, v_i_2110_);
v_infoTree_x3f_2120_ = lean_ctor_get(v___x_2119_, 2);
if (lean_obj_tag(v_infoTree_x3f_2120_) == 1)
{
lean_object* v_val_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_val_2121_ = lean_ctor_get(v_infoTree_x3f_2120_, 0);
v___x_2122_ = lean_unsigned_to_nat(1u);
v___x_2123_ = lean_mk_empty_array_with_capacity(v___x_2122_);
lean_inc(v_val_2121_);
v___x_2124_ = lean_array_push(v___x_2123_, v_val_2121_);
v___x_2125_ = l_Array_append___redArg(v_b_2112_, v___x_2124_);
lean_dec_ref(v___x_2124_);
v___y_2114_ = v___x_2125_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_2127_ = l_Array_append___redArg(v_b_2112_, v___x_2126_);
v___y_2114_ = v___x_2127_;
goto v___jp_2113_;
}
}
else
{
return v_b_2112_;
}
v___jp_2113_:
{
size_t v___x_2115_; size_t v___x_2116_; 
v___x_2115_ = ((size_t)1ULL);
v___x_2116_ = lean_usize_add(v_i_2110_, v___x_2115_);
v_i_2110_ = v___x_2116_;
v_b_2112_ = v___y_2114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_2128_, lean_object* v_i_2129_, lean_object* v_stop_2130_, lean_object* v_b_2131_){
_start:
{
size_t v_i_boxed_2132_; size_t v_stop_boxed_2133_; lean_object* v_res_2134_; 
v_i_boxed_2132_ = lean_unbox_usize(v_i_2129_);
lean_dec(v_i_2129_);
v_stop_boxed_2133_ = lean_unbox_usize(v_stop_2130_);
lean_dec(v_stop_2130_);
v_res_2134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_2128_, v_i_boxed_2132_, v_stop_boxed_2133_, v_b_2131_);
lean_dec_ref(v_as_2128_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(lean_object* v_as_2135_, size_t v_i_2136_, size_t v_stop_2137_, lean_object* v_b_2138_){
_start:
{
uint8_t v___x_2139_; 
v___x_2139_ = lean_usize_dec_eq(v_i_2136_, v_stop_2137_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; uint8_t v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; size_t v___x_2144_; size_t v___x_2145_; 
v___x_2140_ = lean_array_uget_borrowed(v_as_2135_, v_i_2136_);
v___x_2141_ = 2;
v___x_2142_ = lean_box(v___x_2141_);
lean_inc(v___x_2140_);
v___x_2143_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2140_, v___x_2142_, v_b_2138_);
v___x_2144_ = ((size_t)1ULL);
v___x_2145_ = lean_usize_add(v_i_2136_, v___x_2144_);
v_i_2136_ = v___x_2145_;
v_b_2138_ = v___x_2143_;
goto _start;
}
else
{
return v_b_2138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9___boxed(lean_object* v_as_2147_, lean_object* v_i_2148_, lean_object* v_stop_2149_, lean_object* v_b_2150_){
_start:
{
size_t v_i_boxed_2151_; size_t v_stop_boxed_2152_; lean_object* v_res_2153_; 
v_i_boxed_2151_ = lean_unbox_usize(v_i_2148_);
lean_dec(v_i_2148_);
v_stop_boxed_2152_ = lean_unbox_usize(v_stop_2149_);
lean_dec(v_stop_2149_);
v_res_2153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_as_2147_, v_i_boxed_2151_, v_stop_boxed_2152_, v_b_2150_);
lean_dec_ref(v_as_2147_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_2157_, lean_object* v_k_2158_, uint8_t v_v_2159_){
_start:
{
lean_object* v_map_2160_; uint8_t v_hasTrace_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2175_; 
v_map_2160_ = lean_ctor_get(v_o_2157_, 0);
v_hasTrace_2161_ = lean_ctor_get_uint8(v_o_2157_, sizeof(void*)*1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_o_2157_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2163_ = v_o_2157_;
v_isShared_2164_ = v_isSharedCheck_2175_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_map_2160_);
lean_dec(v_o_2157_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2175_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2165_, 0, v_v_2159_);
lean_inc(v_k_2158_);
v___x_2166_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2158_, v___x_2165_, v_map_2160_);
if (v_hasTrace_2161_ == 0)
{
lean_object* v___x_2167_; uint8_t v___x_2168_; lean_object* v___x_2170_; 
v___x_2167_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_2168_ = l_Lean_Name_isPrefixOf(v___x_2167_, v_k_2158_);
lean_dec(v_k_2158_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2166_);
v___x_2170_ = v___x_2163_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2166_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*1, v___x_2168_);
return v___x_2170_;
}
}
else
{
lean_object* v___x_2173_; 
lean_dec(v_k_2158_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2166_);
v___x_2173_ = v___x_2163_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*1, v_hasTrace_2161_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_2176_, lean_object* v_k_2177_, lean_object* v_v_2178_){
_start:
{
uint8_t v_v_boxed_2179_; lean_object* v_res_2180_; 
v_v_boxed_2179_ = lean_unbox(v_v_2178_);
v_res_2180_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2176_, v_k_2177_, v_v_boxed_2179_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_2181_, lean_object* v_opt_2182_, uint8_t v_val_2183_){
_start:
{
lean_object* v_name_2184_; lean_object* v___x_2185_; 
v_name_2184_ = lean_ctor_get(v_opt_2182_, 0);
lean_inc(v_name_2184_);
lean_dec_ref(v_opt_2182_);
v___x_2185_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_2181_, v_name_2184_, v_val_2183_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_2186_, lean_object* v_opt_2187_, lean_object* v_val_2188_){
_start:
{
uint8_t v_val_boxed_2189_; lean_object* v_res_2190_; 
v_val_boxed_2189_ = lean_unbox(v_val_2188_);
v_res_2190_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2186_, v_opt_2187_, v_val_boxed_2189_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_2191_, lean_object* v_opt_2192_, uint8_t v_val_2193_){
_start:
{
lean_object* v_name_2194_; lean_object* v_map_2195_; uint8_t v___x_2196_; 
v_name_2194_ = lean_ctor_get(v_opt_2192_, 0);
v_map_2195_ = lean_ctor_get(v_opts_2191_, 0);
v___x_2196_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_2194_, v_map_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2191_, v_opt_2192_, v_val_2193_);
return v___x_2197_;
}
else
{
lean_dec_ref(v_opt_2192_);
return v_opts_2191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_2198_, lean_object* v_opt_2199_, lean_object* v_val_2200_){
_start:
{
uint8_t v_val_boxed_2201_; lean_object* v_res_2202_; 
v_val_boxed_2201_ = lean_unbox(v_val_2200_);
v_res_2202_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2198_, v_opt_2199_, v_val_boxed_2201_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0(lean_object* v_a_2203_, lean_object* v_ps_2204_){
_start:
{
lean_object* v_importedEntries_2205_; lean_object* v_state_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2215_; 
v_importedEntries_2205_ = lean_ctor_get(v_ps_2204_, 0);
v_state_2206_ = lean_ctor_get(v_ps_2204_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_ps_2204_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2208_ = v_ps_2204_;
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_state_2206_);
lean_inc(v_importedEntries_2205_);
lean_dec(v_ps_2204_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2210_ = lean_task_get_own(v_a_2203_);
v___x_2211_ = l_Array_append___redArg(v_state_2206_, v___x_2210_);
lean_dec(v___x_2210_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 1, v___x_2211_);
v___x_2213_ = v___x_2208_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_importedEntries_2205_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(lean_object* v_as_2216_, size_t v_sz_2217_, size_t v_i_2218_, lean_object* v_b_2219_){
_start:
{
lean_object* v_a_2222_; uint8_t v___x_2226_; 
v___x_2226_ = lean_usize_dec_lt(v_i_2218_, v_sz_2217_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2227_, 0, v_b_2219_);
return v___x_2227_;
}
else
{
lean_object* v___x_2228_; lean_object* v_toEnvExtension_2229_; lean_object* v_asyncMode_2230_; uint8_t v_logWrites_2231_; lean_object* v_a_2232_; lean_object* v___f_2233_; lean_object* v___x_2234_; 
v___x_2228_ = l_Lean_Linter_codeQualityLogExt;
v_toEnvExtension_2229_ = lean_ctor_get(v___x_2228_, 0);
v_asyncMode_2230_ = lean_ctor_get(v_toEnvExtension_2229_, 2);
v_logWrites_2231_ = lean_ctor_get_uint8(v_toEnvExtension_2229_, sizeof(void*)*6);
v_a_2232_ = lean_array_uget_borrowed(v_as_2216_, v_i_2218_);
lean_inc(v_a_2232_);
v___f_2233_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2233_, 0, v_a_2232_);
v___x_2234_ = lean_box(0);
if (v_logWrites_2231_ == 0)
{
lean_object* v___x_2235_; 
lean_inc_ref(v_toEnvExtension_2229_);
v___x_2235_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2229_, v_b_2219_, v___f_2233_, v_asyncMode_2230_, v___x_2234_, v___x_2226_);
v_a_2222_ = v___x_2235_;
goto v___jp_2221_;
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_inc_ref_n(v_toEnvExtension_2229_, 2);
v___x_2236_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2229_, v_b_2219_);
lean_dec_ref(v_b_2219_);
v___x_2237_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2229_, v___x_2236_, v___f_2233_, v_asyncMode_2230_, v___x_2234_, v___x_2226_);
v_a_2222_ = v___x_2237_;
goto v___jp_2221_;
}
}
v___jp_2221_:
{
size_t v___x_2223_; size_t v___x_2224_; 
v___x_2223_ = ((size_t)1ULL);
v___x_2224_ = lean_usize_add(v_i_2218_, v___x_2223_);
v_i_2218_ = v___x_2224_;
v_b_2219_ = v_a_2222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object* v_as_2238_, lean_object* v_sz_2239_, lean_object* v_i_2240_, lean_object* v_b_2241_, lean_object* v___y_2242_){
_start:
{
size_t v_sz_boxed_2243_; size_t v_i_boxed_2244_; lean_object* v_res_2245_; 
v_sz_boxed_2243_ = lean_unbox_usize(v_sz_2239_);
lean_dec(v_sz_2239_);
v_i_boxed_2244_ = lean_unbox_usize(v_i_2240_);
lean_dec(v_i_2240_);
v_res_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v_as_2238_, v_sz_boxed_2243_, v_i_boxed_2244_, v_b_2241_);
lean_dec_ref(v_as_2238_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(lean_object* v_s_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = l_Lean_Language_Snapshot_transform(v_s_2248_, v___y_2249_);
v___x_2251_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___closed__0));
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2250_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___boxed(lean_object* v_s_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(v_s_2253_, v___y_2254_);
lean_dec_ref(v___y_2254_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(lean_object* v_t_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v___f_2259_; lean_object* v___x_2260_; 
v___f_2259_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___closed__0));
v___x_2260_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2257_, v___f_2259_, v_a_2258_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object* v_t_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_t_2261_, v_a_2262_);
lean_dec_ref(v_a_2262_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(lean_object* v_t_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___closed__0));
v___x_2268_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2265_, v___x_2267_, v_a_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___boxed(lean_object* v_t_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_t_2269_, v_a_2270_);
lean_dec_ref(v_a_2270_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(lean_object* v_s_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_toSnapshot_2274_; lean_object* v_metaSnap_2275_; lean_object* v_result_x3f_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___y_2280_; 
v_toSnapshot_2274_ = lean_ctor_get(v_s_2272_, 0);
lean_inc_ref(v_toSnapshot_2274_);
v_metaSnap_2275_ = lean_ctor_get(v_s_2272_, 1);
lean_inc_ref(v_metaSnap_2275_);
v_result_x3f_2276_ = lean_ctor_get(v_s_2272_, 2);
lean_inc(v_result_x3f_2276_);
lean_dec_ref(v_s_2272_);
v___x_2277_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2274_, v___y_2273_);
v___x_2278_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2275_, v___y_2273_);
if (lean_obj_tag(v_result_x3f_2276_) == 0)
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_box(0);
v___y_2280_ = v___x_2286_;
goto v___jp_2279_;
}
else
{
lean_object* v_val_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2296_; 
v_val_2287_ = lean_ctor_get(v_result_x3f_2276_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_result_x3f_2276_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2289_ = v_result_x3f_2276_;
v_isShared_2290_ = v_isSharedCheck_2296_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_val_2287_);
lean_dec(v_result_x3f_2276_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2296_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v_firstCmdSnap_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v_firstCmdSnap_2291_ = lean_ctor_get(v_val_2287_, 1);
lean_inc_ref(v_firstCmdSnap_2291_);
lean_dec(v_val_2287_);
v___x_2292_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_firstCmdSnap_2291_, v___y_2273_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v___x_2292_);
v___x_2294_ = v___x_2289_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
v___y_2280_ = v___x_2294_;
goto v___jp_2279_;
}
}
}
v___jp_2279_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2281_ = lean_unsigned_to_nat(1u);
v___x_2282_ = lean_mk_empty_array_with_capacity(v___x_2281_);
v___x_2283_ = lean_array_push(v___x_2282_, v___x_2278_);
v___x_2284_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2280_, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2277_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0___boxed(lean_object* v_s_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(v_s_2297_, v___y_2298_);
lean_dec_ref(v___y_2298_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(lean_object* v_t_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___f_2303_; lean_object* v___x_2304_; 
v___f_2303_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___closed__0));
v___x_2304_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2301_, v___f_2303_, v_a_2302_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___boxed(lean_object* v_t_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_t_2305_, v_a_2306_);
lean_dec_ref(v_a_2306_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_a_2308_){
_start:
{
lean_object* v_toSnapshot_2309_; lean_object* v_metaSnap_2310_; lean_object* v_result_x3f_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___y_2316_; 
v_toSnapshot_2309_ = lean_ctor_get(v_a_2308_, 0);
lean_inc_ref(v_toSnapshot_2309_);
v_metaSnap_2310_ = lean_ctor_get(v_a_2308_, 1);
lean_inc_ref(v_metaSnap_2310_);
v_result_x3f_2311_ = lean_ctor_get(v_a_2308_, 4);
lean_inc(v_result_x3f_2311_);
lean_dec_ref(v_a_2308_);
v___x_2312_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_2313_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2309_, v___x_2312_);
v___x_2314_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2310_, v___x_2312_);
if (lean_obj_tag(v_result_x3f_2311_) == 0)
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_box(0);
v___y_2316_ = v___x_2322_;
goto v___jp_2315_;
}
else
{
lean_object* v_val_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2332_; 
v_val_2323_ = lean_ctor_get(v_result_x3f_2311_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v_result_x3f_2311_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2325_ = v_result_x3f_2311_;
v_isShared_2326_ = v_isSharedCheck_2332_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_val_2323_);
lean_dec(v_result_x3f_2311_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2332_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v_processedSnap_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v_processedSnap_2327_ = lean_ctor_get(v_val_2323_, 1);
lean_inc_ref(v_processedSnap_2327_);
lean_dec(v_val_2323_);
v___x_2328_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_processedSnap_2327_, v___x_2312_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2328_);
v___x_2330_ = v___x_2325_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
v___y_2316_ = v___x_2330_;
goto v___jp_2315_;
}
}
}
v___jp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_mk_empty_array_with_capacity(v___x_2317_);
v___x_2319_ = lean_array_push(v___x_2318_, v___x_2314_);
v___x_2320_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2316_, v___x_2319_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2313_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
return v___x_2321_;
}
}
}
static double _init_l_Lean_Elab_runFrontend___closed__2(void){
_start:
{
lean_object* v___x_2335_; double v___x_2336_; 
v___x_2335_ = lean_unsigned_to_nat(1000000000u);
v___x_2336_ = lean_float_of_nat(v___x_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_2338_, lean_object* v_opts_2339_, lean_object* v_fileName_2340_, lean_object* v_mainModuleName_2341_, uint32_t v_trustLevel_2342_, lean_object* v_oleanFileName_x3f_2343_, lean_object* v_ileanFileName_x3f_2344_, uint8_t v_jsonOutput_2345_, lean_object* v_errorOnKinds_2346_, lean_object* v_plugins_2347_, uint8_t v_printStats_2348_, lean_object* v_setup_x3f_2349_, lean_object* v_incrSaveFileName_x3f_2350_, lean_object* v_incrLoadFileName_x3f_2351_, lean_object* v_incrHeaderSaveFileName_x3f_2352_){
_start:
{
lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___f_2360_; lean_object* v___f_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; double v___x_2364_; double v___x_2365_; double v___x_2366_; uint8_t v___x_2367_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; size_t v___y_2372_; lean_object* v___y_2373_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; size_t v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; uint8_t v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; size_t v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; uint8_t v___y_2479_; lean_object* v___y_2488_; lean_object* v___y_2489_; uint8_t v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; size_t v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; uint8_t v___y_2498_; lean_object* v___y_2521_; lean_object* v___y_2522_; uint8_t v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; size_t v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; uint8_t v___y_2531_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; uint8_t v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; size_t v___y_2550_; lean_object* v___y_2551_; uint8_t v___y_2552_; lean_object* v___y_2565_; uint8_t v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; uint8_t v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v_a_2639_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v___y_2656_; 
v___f_2360_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___f_2361_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__1));
v___x_2362_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2363_ = lean_io_mono_nanos_now();
v___x_2364_ = lean_float_of_nat(v___x_2363_);
v___x_2365_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__2, &l_Lean_Elab_runFrontend___closed__2_once, _init_l_Lean_Elab_runFrontend___closed__2);
v___x_2366_ = lean_float_div(v___x_2364_, v___x_2365_);
v___x_2367_ = 1;
v___x_2429_ = lean_string_utf8_byte_size(v_input_2338_);
v___x_2430_ = l_Lean_Parser_mkInputContext___redArg(v_input_2338_, v_fileName_2340_, v___x_2367_, v___x_2429_);
v___x_2654_ = l_Lean_internal_cmdlineSnapshots;
if (lean_obj_tag(v_incrSaveFileName_x3f_2350_) == 0)
{
v___y_2656_ = v___x_2367_;
goto v___jp_2655_;
}
else
{
uint8_t v___x_2692_; 
v___x_2692_ = 0;
v___y_2656_ = v___x_2692_;
goto v___jp_2655_;
}
v___jp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2357_ = lean_runtime_forget(v___y_2355_);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___y_2356_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
v___jp_2368_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = l_Lean_trace_profiler_output;
v___x_2375_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v___y_2369_, v___x_2374_);
if (lean_obj_tag(v___x_2375_) == 1)
{
lean_object* v_val_2376_; lean_object* v___x_2377_; size_t v_sz_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
lean_dec_ref(v___y_2370_);
v_val_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_val_2376_);
lean_dec_ref_known(v___x_2375_, 1);
lean_inc_ref(v___y_2371_);
v___x_2377_ = l_Lean_Language_SnapshotTree_getAll(v___y_2371_);
v_sz_2378_ = lean_array_size(v___x_2377_);
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2378_, v___y_2372_, v___x_2377_);
v___x_2380_ = l_Lean_Name_toString(v_mainModuleName_2341_, v___x_2367_);
v___x_2381_ = l_Lean_Firefox_Profile_export(v___x_2380_, v___x_2366_, v___x_2379_, v___y_2369_);
lean_dec_ref(v___y_2369_);
lean_dec_ref(v___x_2379_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2381_, 1);
v___x_2383_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2382_);
v___x_2384_ = l_Lean_Json_compress(v___x_2383_);
v___x_2385_ = l_IO_FS_writeFile(v_val_2376_, v___x_2384_);
lean_dec_ref(v___x_2384_);
lean_dec(v_val_2376_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_dec_ref_known(v___x_2385_, 1);
v___y_2355_ = v___y_2371_;
v___y_2356_ = v___y_2373_;
goto v___jp_2354_;
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec_ref(v___y_2373_);
lean_dec_ref(v___y_2371_);
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec(v_val_2376_);
lean_dec_ref(v___y_2373_);
lean_dec_ref(v___y_2371_);
v_a_2394_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2381_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2381_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
else
{
lean_object* v___x_2402_; uint8_t v___x_2403_; 
lean_dec(v___x_2375_);
v___x_2402_ = l_Lean_trace_profiler_serve;
v___x_2403_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v___y_2370_, v___x_2402_);
lean_dec_ref(v___y_2370_);
if (v___x_2403_ == 0)
{
lean_dec_ref(v___y_2369_);
lean_dec(v_mainModuleName_2341_);
v___y_2355_ = v___y_2371_;
v___y_2356_ = v___y_2373_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2404_; size_t v_sz_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_inc_ref(v___y_2371_);
v___x_2404_ = l_Lean_Language_SnapshotTree_getAll(v___y_2371_);
v_sz_2405_ = lean_array_size(v___x_2404_);
v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2405_, v___y_2372_, v___x_2404_);
v___x_2407_ = l_Lean_Name_toString(v_mainModuleName_2341_, v___x_2367_);
v___x_2408_ = l_Lean_Firefox_Profile_export(v___x_2407_, v___x_2366_, v___x_2406_, v___y_2369_);
lean_dec_ref(v___y_2369_);
lean_dec_ref(v___x_2406_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2410_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2409_);
v___x_2411_ = l_Lean_Json_compress(v___x_2410_);
v___x_2412_ = l_Lean_Firefox_Profile_serve(v___x_2411_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_dec_ref_known(v___x_2412_, 1);
v___y_2355_ = v___y_2371_;
v___y_2356_ = v___y_2373_;
goto v___jp_2354_;
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec_ref(v___y_2373_);
lean_dec_ref(v___y_2371_);
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2412_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2412_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec_ref(v___y_2373_);
lean_dec_ref(v___y_2371_);
v_a_2421_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2408_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2408_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
}
v___jp_2431_:
{
lean_object* v_fileMap_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_fst_2444_; lean_object* v_snd_2445_; lean_object* v_stx_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2466_; 
v_fileMap_2441_ = lean_ctor_get(v___x_2430_, 2);
lean_inc_ref(v_fileMap_2441_);
lean_dec_ref(v___x_2430_);
v___x_2442_ = l_Lean_Server_findModuleRefs(v_fileMap_2441_, v___y_2440_, v___y_2439_, v___y_2439_);
lean_dec_ref(v___y_2440_);
v___x_2443_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_2442_);
v_fst_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_fst_2444_);
v_snd_2445_ = lean_ctor_get(v___x_2443_, 1);
lean_inc(v_snd_2445_);
lean_dec_ref(v___x_2443_);
v_stx_2446_ = lean_ctor_get(v___y_2438_, 3);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___y_2438_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; lean_object* v_unused_2468_; lean_object* v_unused_2469_; lean_object* v_unused_2470_; 
v_unused_2467_ = lean_ctor_get(v___y_2438_, 4);
lean_dec(v_unused_2467_);
v_unused_2468_ = lean_ctor_get(v___y_2438_, 2);
lean_dec(v_unused_2468_);
v_unused_2469_ = lean_ctor_get(v___y_2438_, 1);
lean_dec(v_unused_2469_);
v_unused_2470_ = lean_ctor_get(v___y_2438_, 0);
lean_dec(v_unused_2470_);
v___x_2448_ = v___y_2438_;
v_isShared_2449_ = v_isSharedCheck_2466_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_stx_2446_);
lean_dec(v___y_2438_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2466_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2450_ = lean_unsigned_to_nat(5u);
v___x_2451_ = l_Lean_Server_collectImports(v_stx_2446_);
lean_inc(v_mainModuleName_2341_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 4, v_snd_2445_);
lean_ctor_set(v___x_2448_, 3, v_fst_2444_);
lean_ctor_set(v___x_2448_, 2, v___x_2451_);
lean_ctor_set(v___x_2448_, 1, v_mainModuleName_2341_);
lean_ctor_set(v___x_2448_, 0, v___x_2450_);
v___x_2453_ = v___x_2448_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_mainModuleName_2341_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2465_, 3, v_fst_2444_);
lean_ctor_set(v_reuseFailAlloc_2465_, 4, v_snd_2445_);
v___x_2453_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2454_ = l_Lean_Server_instToJsonIlean_toJson(v___x_2453_);
v___x_2455_ = l_Lean_Json_compress(v___x_2454_);
v___x_2456_ = l_IO_FS_writeFile(v___y_2436_, v___x_2455_);
lean_dec_ref(v___x_2455_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_dec_ref_known(v___x_2456_, 1);
v___y_2369_ = v___y_2432_;
v___y_2370_ = v___y_2433_;
v___y_2371_ = v___y_2434_;
v___y_2372_ = v___y_2435_;
v___y_2373_ = v___y_2437_;
goto v___jp_2368_;
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec_ref(v___y_2437_);
lean_dec_ref(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v_mainModuleName_2341_);
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2456_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
}
v___jp_2471_:
{
if (lean_obj_tag(v_ileanFileName_x3f_2344_) == 1)
{
lean_object* v_val_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
v_val_2480_ = lean_ctor_get(v_ileanFileName_x3f_2344_, 0);
lean_inc_ref(v___y_2475_);
v___x_2481_ = l_Lean_Language_SnapshotTree_getAll(v___y_2475_);
v___x_2482_ = lean_mk_empty_array_with_capacity(v___y_2473_);
v___x_2483_ = lean_array_get_size(v___x_2481_);
v___x_2484_ = lean_nat_dec_lt(v___y_2473_, v___x_2483_);
lean_dec(v___y_2473_);
if (v___x_2484_ == 0)
{
lean_dec_ref(v___x_2481_);
v___y_2432_ = v___y_2472_;
v___y_2433_ = v___y_2474_;
v___y_2434_ = v___y_2475_;
v___y_2435_ = v___y_2476_;
v___y_2436_ = v_val_2480_;
v___y_2437_ = v___y_2478_;
v___y_2438_ = v___y_2477_;
v___y_2439_ = v___y_2479_;
v___y_2440_ = v___x_2482_;
goto v___jp_2431_;
}
else
{
size_t v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = lean_usize_of_nat(v___x_2483_);
v___x_2486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v___x_2481_, v___y_2476_, v___x_2485_, v___x_2482_);
lean_dec_ref(v___x_2481_);
v___y_2432_ = v___y_2472_;
v___y_2433_ = v___y_2474_;
v___y_2434_ = v___y_2475_;
v___y_2435_ = v___y_2476_;
v___y_2436_ = v_val_2480_;
v___y_2437_ = v___y_2478_;
v___y_2438_ = v___y_2477_;
v___y_2439_ = v___y_2479_;
v___y_2440_ = v___x_2486_;
goto v___jp_2431_;
}
}
else
{
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2473_);
lean_dec_ref(v___x_2430_);
v___y_2369_ = v___y_2472_;
v___y_2370_ = v___y_2474_;
v___y_2371_ = v___y_2475_;
v___y_2372_ = v___y_2476_;
v___y_2373_ = v___y_2478_;
goto v___jp_2368_;
}
}
v___jp_2487_:
{
if (v___y_2498_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_2343_) == 1)
{
lean_object* v_val_2499_; lean_object* v_fileMap_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___f_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v_val_2499_ = lean_ctor_get(v_oleanFileName_x3f_2343_, 0);
lean_inc(v_val_2499_);
lean_dec_ref_known(v_oleanFileName_x3f_2343_, 1);
v_fileMap_2500_ = lean_ctor_get(v___x_2430_, 2);
v___x_2501_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__3));
v___x_2502_ = lean_box(0);
v___x_2503_ = lean_mk_empty_array_with_capacity(v___y_2492_);
lean_inc_ref(v___y_2494_);
v___x_2504_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___y_2494_, v___x_2502_, v___x_2503_);
v___x_2505_ = lean_box(v___x_2367_);
v___x_2506_ = lean_box(v___y_2490_);
lean_inc_ref(v_fileMap_2500_);
v___f_2507_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2507_, 0, v_fileMap_2500_);
lean_closure_set(v___f_2507_, 1, v___y_2489_);
lean_closure_set(v___f_2507_, 2, v___x_2504_);
lean_closure_set(v___f_2507_, 3, v___y_2488_);
lean_closure_set(v___f_2507_, 4, v_val_2499_);
lean_closure_set(v___f_2507_, 5, v___x_2505_);
lean_closure_set(v___f_2507_, 6, v___x_2506_);
v___x_2508_ = lean_box(0);
v___x_2509_ = l_Lean_profileitIOUnsafe___redArg(v___x_2501_, v___y_2493_, v___f_2507_, v___x_2508_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_dec_ref_known(v___x_2509_, 1);
v___y_2472_ = v___y_2491_;
v___y_2473_ = v___y_2492_;
v___y_2474_ = v___y_2493_;
v___y_2475_ = v___y_2494_;
v___y_2476_ = v___y_2495_;
v___y_2477_ = v___y_2497_;
v___y_2478_ = v___y_2496_;
v___y_2479_ = v___y_2498_;
goto v___jp_2471_;
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec_ref(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v___x_2430_);
lean_dec(v_mainModuleName_2341_);
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
else
{
lean_dec_ref(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v_oleanFileName_x3f_2343_);
v___y_2472_ = v___y_2491_;
v___y_2473_ = v___y_2492_;
v___y_2474_ = v___y_2493_;
v___y_2475_ = v___y_2494_;
v___y_2476_ = v___y_2495_;
v___y_2477_ = v___y_2497_;
v___y_2478_ = v___y_2496_;
v___y_2479_ = v___y_2498_;
goto v___jp_2471_;
}
}
else
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec_ref(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec_ref(v___x_2430_);
lean_dec(v_oleanFileName_x3f_2343_);
lean_dec(v_mainModuleName_2341_);
v___x_2518_ = lean_box(0);
v___x_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
return v___x_2519_;
}
}
v___jp_2520_:
{
if (v_printStats_2348_ == 0)
{
v___y_2488_ = v___y_2521_;
v___y_2489_ = v___y_2522_;
v___y_2490_ = v___y_2523_;
v___y_2491_ = v___y_2524_;
v___y_2492_ = v___y_2525_;
v___y_2493_ = v___y_2526_;
v___y_2494_ = v___y_2527_;
v___y_2495_ = v___y_2528_;
v___y_2496_ = v___y_2530_;
v___y_2497_ = v___y_2529_;
v___y_2498_ = v___y_2531_;
goto v___jp_2487_;
}
else
{
lean_object* v___x_2532_; 
lean_inc_ref(v___y_2530_);
v___x_2532_ = l_Lean_Environment_displayStats(v___y_2530_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_dec_ref_known(v___x_2532_, 1);
v___y_2488_ = v___y_2521_;
v___y_2489_ = v___y_2522_;
v___y_2490_ = v___y_2523_;
v___y_2491_ = v___y_2524_;
v___y_2492_ = v___y_2525_;
v___y_2493_ = v___y_2526_;
v___y_2494_ = v___y_2527_;
v___y_2495_ = v___y_2528_;
v___y_2496_ = v___y_2530_;
v___y_2497_ = v___y_2529_;
v___y_2498_ = v___y_2531_;
goto v___jp_2487_;
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec_ref(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec_ref(v___x_2430_);
lean_dec(v_oleanFileName_x3f_2343_);
lean_dec(v_mainModuleName_2341_);
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
v___jp_2541_:
{
if (lean_obj_tag(v_incrHeaderSaveFileName_x3f_2352_) == 1)
{
lean_object* v_val_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_val_2553_ = lean_ctor_get(v_incrHeaderSaveFileName_x3f_2352_, 0);
lean_inc(v_val_2553_);
lean_dec_ref_known(v_incrHeaderSaveFileName_x3f_2352_, 1);
lean_inc_ref(v___y_2551_);
v___x_2554_ = l_Lean_Language_Lean_truncateToHeader(v___y_2551_);
v___x_2555_ = lean_apply_3(v___y_2543_, v_val_2553_, v___x_2554_, lean_box(0));
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_dec_ref_known(v___x_2555_, 1);
lean_inc_ref(v___y_2544_);
v___y_2521_ = v___y_2542_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___y_2545_;
v___y_2524_ = v___y_2546_;
v___y_2525_ = v___y_2547_;
v___y_2526_ = v___y_2548_;
v___y_2527_ = v___y_2549_;
v___y_2528_ = v___y_2550_;
v___y_2529_ = v___y_2551_;
v___y_2530_ = v___y_2544_;
v___y_2531_ = v___y_2552_;
goto v___jp_2520_;
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec_ref(v___y_2551_);
lean_dec_ref(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec_ref(v___y_2544_);
lean_dec_ref(v___y_2542_);
lean_dec_ref(v___x_2430_);
lean_dec(v_oleanFileName_x3f_2343_);
lean_dec(v_mainModuleName_2341_);
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
else
{
lean_dec_ref(v___y_2543_);
lean_dec(v_incrHeaderSaveFileName_x3f_2352_);
lean_inc_ref(v___y_2544_);
v___y_2521_ = v___y_2542_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___y_2545_;
v___y_2524_ = v___y_2546_;
v___y_2525_ = v___y_2547_;
v___y_2526_ = v___y_2548_;
v___y_2527_ = v___y_2549_;
v___y_2528_ = v___y_2550_;
v___y_2529_ = v___y_2551_;
v___y_2530_ = v___y_2544_;
v___y_2531_ = v___y_2552_;
goto v___jp_2520_;
}
}
v___jp_2564_:
{
size_t v_sz_2574_; size_t v___x_2575_; lean_object* v___x_2576_; 
v_sz_2574_ = lean_array_size(v___y_2573_);
v___x_2575_ = ((size_t)0ULL);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v___y_2573_, v_sz_2574_, v___x_2575_, v___y_2569_);
lean_dec_ref(v___y_2573_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2578_; lean_object* v___f_2579_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc_n(v_a_2577_, 2);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2578_ = lean_box(v___x_2367_);
v___f_2579_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2579_, 0, v_a_2577_);
lean_closure_set(v___f_2579_, 1, v___x_2578_);
if (lean_obj_tag(v_incrSaveFileName_x3f_2350_) == 1)
{
lean_object* v_val_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v_val_2580_ = lean_ctor_get(v_incrSaveFileName_x3f_2350_, 0);
lean_inc(v_val_2580_);
lean_dec_ref_known(v_incrSaveFileName_x3f_2350_, 1);
v___x_2581_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___y_2570_);
lean_inc_ref(v___y_2571_);
v___x_2582_ = l_Lean_Elab_runFrontend___lam__2(v_a_2577_, v___x_2367_, v_val_2580_, v___y_2571_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_dec_ref_known(v___x_2582_, 1);
lean_inc_ref(v___y_2565_);
v___y_2542_ = v___y_2565_;
v___y_2543_ = v___f_2579_;
v___y_2544_ = v_a_2577_;
v___y_2545_ = v___y_2566_;
v___y_2546_ = v___y_2567_;
v___y_2547_ = v___y_2568_;
v___y_2548_ = v___y_2565_;
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___x_2575_;
v___y_2551_ = v___y_2571_;
v___y_2552_ = v___y_2572_;
goto v___jp_2541_;
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec_ref(v___f_2579_);
lean_dec(v_a_2577_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___x_2430_);
lean_dec(v_incrHeaderSaveFileName_x3f_2352_);
lean_dec(v_oleanFileName_x3f_2343_);
lean_dec(v_mainModuleName_2341_);
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_dec(v_incrSaveFileName_x3f_2350_);
lean_inc_ref(v___y_2565_);
v___y_2542_ = v___y_2565_;
v___y_2543_ = v___f_2579_;
v___y_2544_ = v_a_2577_;
v___y_2545_ = v___y_2566_;
v___y_2546_ = v___y_2567_;
v___y_2547_ = v___y_2568_;
v___y_2548_ = v___y_2565_;
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___x_2575_;
v___y_2551_ = v___y_2571_;
v___y_2552_ = v___y_2572_;
goto v___jp_2541_;
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v___x_2430_);
lean_dec(v_incrHeaderSaveFileName_x3f_2352_);
lean_dec(v_incrSaveFileName_x3f_2350_);
lean_dec(v_oleanFileName_x3f_2343_);
lean_dec(v_mainModuleName_2341_);
v_a_2591_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2576_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2576_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
v___jp_2599_:
{
lean_object* v___x_2605_; 
lean_inc_ref(v___y_2602_);
v___x_2605_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_2602_, v___y_2600_, v_jsonOutput_2345_, v___y_2604_);
lean_dec(v___y_2604_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2627_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2627_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2627_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; 
lean_inc_ref(v___y_2603_);
v___x_2610_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___y_2603_);
if (lean_obj_tag(v___x_2610_) == 1)
{
lean_object* v_val_2611_; lean_object* v_env_2612_; lean_object* v_scopes_2613_; lean_object* v___x_2614_; lean_object* v_opts_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_del_object(v___x_2608_);
v_val_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_val_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v_env_2612_ = lean_ctor_get(v_val_2611_, 0);
lean_inc_ref(v_env_2612_);
v_scopes_2613_ = lean_ctor_get(v_val_2611_, 2);
lean_inc(v_scopes_2613_);
lean_dec(v_val_2611_);
lean_inc(v___y_2601_);
v___x_2614_ = l_List_get_x21Internal___redArg(v___x_2362_, v_scopes_2613_, v___y_2601_);
lean_dec(v_scopes_2613_);
v_opts_2615_ = lean_ctor_get(v___x_2614_, 1);
lean_inc_ref(v_opts_2615_);
lean_dec(v___x_2614_);
v___x_2616_ = lean_mk_empty_array_with_capacity(v___y_2601_);
lean_inc_ref(v___x_2616_);
lean_inc_ref(v___y_2603_);
v___x_2617_ = l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(v___y_2603_, v___x_2616_, v___f_2361_);
if (lean_obj_tag(v___x_2617_) == 0)
{
uint8_t v___x_2618_; uint8_t v___x_2619_; 
v___x_2618_ = lean_unbox(v_a_2606_);
v___x_2619_ = lean_unbox(v_a_2606_);
lean_dec(v_a_2606_);
v___y_2565_ = v_opts_2615_;
v___y_2566_ = v___x_2618_;
v___y_2567_ = v___y_2600_;
v___y_2568_ = v___y_2601_;
v___y_2569_ = v_env_2612_;
v___y_2570_ = v___y_2602_;
v___y_2571_ = v___y_2603_;
v___y_2572_ = v___x_2619_;
v___y_2573_ = v___x_2616_;
goto v___jp_2564_;
}
else
{
lean_object* v_val_2620_; uint8_t v___x_2621_; uint8_t v___x_2622_; 
lean_dec_ref(v___x_2616_);
v_val_2620_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_val_2620_);
lean_dec_ref_known(v___x_2617_, 1);
v___x_2621_ = lean_unbox(v_a_2606_);
v___x_2622_ = lean_unbox(v_a_2606_);
lean_dec(v_a_2606_);
v___y_2565_ = v_opts_2615_;
v___y_2566_ = v___x_2621_;
v___y_2567_ = v___y_2600_;
v___y_2568_ = v___y_2601_;
v___y_2569_ = v_env_2612_;
v___y_2570_ = v___y_2602_;
v___y_2571_ = v___y_2603_;
v___y_2572_ = v___x_2622_;
v___y_2573_ = v_val_2620_;
goto v___jp_2564_;
}
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
lean_dec(v___x_2610_);
lean_dec(v_a_2606_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec_ref(v___x_2430_);
lean_dec(v_incrHeaderSaveFileName_x3f_2352_);
lean_dec(v_incrSaveFileName_x3f_2350_);
lean_dec(v_oleanFileName_x3f_2343_);
lean_dec(v_mainModuleName_2341_);
v___x_2623_ = lean_box(0);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2623_);
v___x_2625_ = v___x_2608_;
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
lean_dec_ref(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec_ref(v___x_2430_);
lean_dec(v_incrHeaderSaveFileName_x3f_2352_);
lean_dec(v_incrSaveFileName_x3f_2350_);
lean_dec(v_oleanFileName_x3f_2343_);
lean_dec(v_mainModuleName_2341_);
v_a_2628_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2605_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2605_);
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
v___x_2640_ = l_Lean_Language_Lean_process(v___y_2638_, v_a_2639_, v___x_2430_);
lean_inc_ref(v___x_2640_);
v___x_2641_ = l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(v___x_2640_);
v___x_2642_ = lean_box(1);
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_array_get_size(v_errorOnKinds_2346_);
v___x_2645_ = lean_nat_dec_lt(v___x_2643_, v___x_2644_);
if (v___x_2645_ == 0)
{
v___y_2600_ = v___y_2637_;
v___y_2601_ = v___x_2643_;
v___y_2602_ = v___x_2641_;
v___y_2603_ = v___x_2640_;
v___y_2604_ = v___x_2642_;
goto v___jp_2599_;
}
else
{
size_t v___x_2646_; size_t v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = ((size_t)0ULL);
v___x_2647_ = lean_usize_of_nat(v___x_2644_);
v___x_2648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_errorOnKinds_2346_, v___x_2646_, v___x_2647_, v___x_2642_);
v___y_2600_ = v___y_2637_;
v___y_2601_ = v___x_2643_;
v___y_2602_ = v___x_2641_;
v___y_2603_ = v___x_2640_;
v___y_2604_ = v___x_2648_;
goto v___jp_2599_;
}
}
v___jp_2649_:
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2653_, 0, v_a_2652_);
v___y_2637_ = v___y_2650_;
v___y_2638_ = v___y_2651_;
v_a_2639_ = v___x_2653_;
goto v___jp_2636_;
}
v___jp_2655_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___f_2662_; 
v___x_2657_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2339_, v___x_2654_, v___y_2656_);
v___x_2658_ = l_Lean_Elab_async;
v___x_2659_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_2657_, v___x_2658_, v___x_2367_);
v___x_2660_ = lean_box_uint32(v_trustLevel_2342_);
v___x_2661_ = lean_box(v___x_2367_);
lean_inc(v_mainModuleName_2341_);
lean_inc_ref(v___x_2659_);
v___f_2662_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4___boxed), 10, 7);
lean_closure_set(v___f_2662_, 0, v_setup_x3f_2349_);
lean_closure_set(v___f_2662_, 1, v___f_2360_);
lean_closure_set(v___f_2662_, 2, v___x_2659_);
lean_closure_set(v___f_2662_, 3, v_plugins_2347_);
lean_closure_set(v___f_2662_, 4, v___x_2660_);
lean_closure_set(v___f_2662_, 5, v___x_2661_);
lean_closure_set(v___f_2662_, 6, v_mainModuleName_2341_);
if (lean_obj_tag(v_incrLoadFileName_x3f_2351_) == 0)
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_box(0);
v___y_2637_ = v___x_2659_;
v___y_2638_ = v___f_2662_;
v_a_2639_ = v___x_2663_;
goto v___jp_2636_;
}
else
{
lean_object* v_val_2664_; lean_object* v___x_2665_; 
v_val_2664_ = lean_ctor_get(v_incrLoadFileName_x3f_2351_, 0);
lean_inc(v_val_2664_);
lean_dec_ref_known(v_incrLoadFileName_x3f_2351_, 1);
v___x_2665_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_val_2664_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v_snap_2667_; lean_object* v_initModIdxs_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v_snap_2667_ = lean_ctor_get(v_a_2666_, 0);
lean_inc_ref(v_snap_2667_);
v_initModIdxs_2668_ = lean_ctor_get(v_a_2666_, 1);
lean_inc_ref(v_initModIdxs_2668_);
lean_dec(v_a_2666_);
lean_inc(v_mainModuleName_2341_);
v___x_2669_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(v_snap_2667_, v_mainModuleName_2341_);
lean_inc_ref(v___x_2669_);
v___x_2670_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v___x_2669_);
v___x_2671_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_2670_);
if (lean_obj_tag(v___x_2671_) == 1)
{
lean_object* v_val_2672_; lean_object* v___f_2673_; lean_object* v___x_2674_; 
v_val_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_val_2672_);
lean_dec_ref_known(v___x_2671_, 1);
lean_inc_ref(v___x_2659_);
v___f_2673_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__5___boxed), 4, 3);
lean_closure_set(v___f_2673_, 0, v_val_2672_);
lean_closure_set(v___f_2673_, 1, v_initModIdxs_2668_);
lean_closure_set(v___f_2673_, 2, v___x_2659_);
v___x_2674_ = l_Lean_withImporting___redArg(v___f_2673_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v___x_2675_; 
lean_dec_ref_known(v___x_2674_, 1);
v___x_2675_ = lean_enable_initializer_execution();
v___y_2650_ = v___x_2659_;
v___y_2651_ = v___f_2662_;
v_a_2652_ = v___x_2669_;
goto v___jp_2649_;
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec_ref(v___x_2669_);
lean_dec_ref(v___f_2662_);
lean_dec_ref(v___x_2659_);
lean_dec_ref(v___x_2430_);
lean_dec(v_incrHeaderSaveFileName_x3f_2352_);
lean_dec(v_incrSaveFileName_x3f_2350_);
lean_dec(v_oleanFileName_x3f_2343_);
lean_dec(v_mainModuleName_2341_);
v_a_2676_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2674_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2674_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_dec(v___x_2671_);
lean_dec_ref(v_initModIdxs_2668_);
v___y_2650_ = v___x_2659_;
v___y_2651_ = v___f_2662_;
v_a_2652_ = v___x_2669_;
goto v___jp_2649_;
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec_ref(v___f_2662_);
lean_dec_ref(v___x_2659_);
lean_dec_ref(v___x_2430_);
lean_dec(v_incrHeaderSaveFileName_x3f_2352_);
lean_dec(v_incrSaveFileName_x3f_2350_);
lean_dec(v_oleanFileName_x3f_2343_);
lean_dec(v_mainModuleName_2341_);
v_a_2684_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2665_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2665_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_2693_, lean_object* v_opts_2694_, lean_object* v_fileName_2695_, lean_object* v_mainModuleName_2696_, lean_object* v_trustLevel_2697_, lean_object* v_oleanFileName_x3f_2698_, lean_object* v_ileanFileName_x3f_2699_, lean_object* v_jsonOutput_2700_, lean_object* v_errorOnKinds_2701_, lean_object* v_plugins_2702_, lean_object* v_printStats_2703_, lean_object* v_setup_x3f_2704_, lean_object* v_incrSaveFileName_x3f_2705_, lean_object* v_incrLoadFileName_x3f_2706_, lean_object* v_incrHeaderSaveFileName_x3f_2707_, lean_object* v_a_2708_){
_start:
{
uint32_t v_trustLevel_boxed_2709_; uint8_t v_jsonOutput_boxed_2710_; uint8_t v_printStats_boxed_2711_; lean_object* v_res_2712_; 
v_trustLevel_boxed_2709_ = lean_unbox_uint32(v_trustLevel_2697_);
lean_dec(v_trustLevel_2697_);
v_jsonOutput_boxed_2710_ = lean_unbox(v_jsonOutput_2700_);
v_printStats_boxed_2711_ = lean_unbox(v_printStats_2703_);
v_res_2712_ = l_Lean_Elab_runFrontend(v_input_2693_, v_opts_2694_, v_fileName_2695_, v_mainModuleName_2696_, v_trustLevel_boxed_2709_, v_oleanFileName_x3f_2698_, v_ileanFileName_x3f_2699_, v_jsonOutput_boxed_2710_, v_errorOnKinds_2701_, v_plugins_2702_, v_printStats_boxed_2711_, v_setup_x3f_2704_, v_incrSaveFileName_x3f_2705_, v_incrLoadFileName_x3f_2706_, v_incrHeaderSaveFileName_x3f_2707_);
lean_dec_ref(v_errorOnKinds_2701_);
lean_dec(v_ileanFileName_x3f_2699_);
return v_res_2712_;
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
