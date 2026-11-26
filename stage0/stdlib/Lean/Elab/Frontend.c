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
static const lean_ctor_object l_Lean_Elab_process___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_process___closed__0 = (const lean_object*)&l_Lean_Elab_process___closed__0_value;
static const lean_ctor_object l_Lean_Elab_process___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_process___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_process___closed__1 = (const lean_object*)&l_Lean_Elab_process___closed__1_value;
static const lean_string_object l_Lean_Elab_process___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<input>"};
static const lean_object* l_Lean_Elab_process___closed__2 = (const lean_object*)&l_Lean_Elab_process___closed__2_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object* v_input_708_, lean_object* v_env_709_, lean_object* v_opts_710_, lean_object* v_fileName_711_){
_start:
{
lean_object* v___y_714_; 
if (lean_obj_tag(v_fileName_711_) == 0)
{
lean_object* v___x_734_; 
v___x_734_ = ((lean_object*)(l_Lean_Elab_process___closed__2));
v___y_714_ = v___x_734_;
goto v___jp_713_;
}
else
{
lean_object* v_val_735_; 
v_val_735_ = lean_ctor_get(v_fileName_711_, 0);
lean_inc(v_val_735_);
lean_dec_ref_known(v_fileName_711_, 1);
v___y_714_ = v_val_735_;
goto v___jp_713_;
}
v___jp_713_:
{
uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v_inputCtx_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_733_; 
v___x_715_ = 1;
v___x_716_ = lean_string_utf8_byte_size(v_input_708_);
v_inputCtx_717_ = l_Lean_Parser_mkInputContext___redArg(v_input_708_, v___y_714_, v___x_715_, v___x_716_);
v___x_718_ = ((lean_object*)(l_Lean_Elab_process___closed__1));
v___x_719_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
v___x_720_ = l_Lean_Elab_Command_mkState(v_env_709_, v___x_719_, v_opts_710_);
v___x_721_ = l_Lean_Elab_IO_processCommands(v_inputCtx_717_, v___x_718_, v___x_720_);
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_733_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_733_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_733_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_commandState_726_; lean_object* v_env_727_; lean_object* v_messages_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v_commandState_726_ = lean_ctor_get(v_a_722_, 0);
lean_inc_ref(v_commandState_726_);
lean_dec(v_a_722_);
v_env_727_ = lean_ctor_get(v_commandState_726_, 0);
lean_inc_ref(v_env_727_);
v_messages_728_ = lean_ctor_get(v_commandState_726_, 1);
lean_inc_ref(v_messages_728_);
lean_dec_ref(v_commandState_726_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v_env_727_);
lean_ctor_set(v___x_729_, 1, v_messages_728_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_729_);
v___x_731_ = v___x_724_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process___boxed(lean_object* v_input_736_, lean_object* v_env_737_, lean_object* v_opts_738_, lean_object* v_fileName_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Elab_process(v_input_736_, v_env_737_, v_opts_738_, v_fileName_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(lean_object* v_cmdStx_x3f_742_, lean_object* v_as_743_, size_t v_i_744_, size_t v_stop_745_, lean_object* v_b_746_){
_start:
{
lean_object* v___y_748_; uint8_t v___x_752_; 
v___x_752_ = lean_usize_dec_eq(v_i_744_, v_stop_745_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v_stx_x3f_754_; lean_object* v___x_755_; 
v___x_753_ = lean_array_uget_borrowed(v_as_743_, v_i_744_);
v_stx_x3f_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v___x_753_);
v___x_755_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_753_);
if (lean_obj_tag(v_stx_x3f_754_) == 0)
{
lean_object* v___x_756_; 
lean_inc(v_cmdStx_x3f_742_);
v___x_756_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_755_, v_cmdStx_x3f_742_, v_b_746_);
v___y_748_ = v___x_756_;
goto v___jp_747_;
}
else
{
lean_object* v___x_757_; 
lean_inc_ref(v_stx_x3f_754_);
v___x_757_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_755_, v_stx_x3f_754_, v_b_746_);
v___y_748_ = v___x_757_;
goto v___jp_747_;
}
}
else
{
lean_dec(v_cmdStx_x3f_742_);
return v_b_746_;
}
v___jp_747_:
{
size_t v___x_749_; size_t v___x_750_; 
v___x_749_ = ((size_t)1ULL);
v___x_750_ = lean_usize_add(v_i_744_, v___x_749_);
v_i_744_ = v___x_750_;
v_b_746_ = v___y_748_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(lean_object* v_t_758_, lean_object* v_cmdStx_x3f_759_, lean_object* v_acc_760_){
_start:
{
lean_object* v_element_761_; lean_object* v_diagnostics_762_; lean_object* v_children_763_; lean_object* v_msgLog_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_778_; 
v_element_761_ = lean_ctor_get(v_t_758_, 0);
v_diagnostics_762_ = lean_ctor_get(v_element_761_, 1);
lean_inc_ref(v_diagnostics_762_);
v_children_763_ = lean_ctor_get(v_t_758_, 1);
lean_inc_ref(v_children_763_);
lean_dec_ref(v_t_758_);
v_msgLog_764_ = lean_ctor_get(v_diagnostics_762_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_diagnostics_762_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_diagnostics_762_, 1);
lean_dec(v_unused_779_);
v___x_766_ = v_diagnostics_762_;
v_isShared_767_ = v_isSharedCheck_778_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_msgLog_764_);
lean_dec(v_diagnostics_762_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_778_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
lean_inc(v_cmdStx_x3f_759_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_msgLog_764_);
lean_ctor_set(v___x_766_, 0, v_cmdStx_x3f_759_);
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_cmdStx_x3f_759_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_msgLog_764_);
v___x_769_ = v_reuseFailAlloc_777_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v_acc_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_acc_770_ = lean_array_push(v_acc_760_, v___x_769_);
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = lean_array_get_size(v_children_763_);
v___x_773_ = lean_nat_dec_lt(v___x_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_dec_ref(v_children_763_);
lean_dec(v_cmdStx_x3f_759_);
return v_acc_770_;
}
else
{
size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
v___x_774_ = ((size_t)0ULL);
v___x_775_ = lean_usize_of_nat(v___x_772_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_759_, v_children_763_, v___x_774_, v___x_775_, v_acc_770_);
lean_dec_ref(v_children_763_);
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0___boxed(lean_object* v_cmdStx_x3f_780_, lean_object* v_as_781_, lean_object* v_i_782_, lean_object* v_stop_783_, lean_object* v_b_784_){
_start:
{
size_t v_i_boxed_785_; size_t v_stop_boxed_786_; lean_object* v_res_787_; 
v_i_boxed_785_ = lean_unbox_usize(v_i_782_);
lean_dec(v_i_782_);
v_stop_boxed_786_ = lean_unbox_usize(v_stop_783_);
lean_dec(v_stop_783_);
v_res_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_780_, v_as_781_, v_i_boxed_785_, v_stop_boxed_786_, v_b_784_);
lean_dec_ref(v_as_781_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3(lean_object* v_filePath_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_lean_x3f_790_; lean_object* v_olean_x3f_791_; lean_object* v_oleanServer_x3f_792_; lean_object* v_ilean_x3f_793_; lean_object* v_irSig_x3f_794_; lean_object* v_ir_x3f_795_; lean_object* v_c_x3f_796_; lean_object* v_bc_x3f_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_805_; 
v_lean_x3f_790_ = lean_ctor_get(v_a_789_, 0);
v_olean_x3f_791_ = lean_ctor_get(v_a_789_, 1);
v_oleanServer_x3f_792_ = lean_ctor_get(v_a_789_, 2);
v_ilean_x3f_793_ = lean_ctor_get(v_a_789_, 4);
v_irSig_x3f_794_ = lean_ctor_get(v_a_789_, 5);
v_ir_x3f_795_ = lean_ctor_get(v_a_789_, 6);
v_c_x3f_796_ = lean_ctor_get(v_a_789_, 7);
v_bc_x3f_797_ = lean_ctor_get(v_a_789_, 8);
v_isSharedCheck_805_ = !lean_is_exclusive(v_a_789_);
if (v_isSharedCheck_805_ == 0)
{
lean_object* v_unused_806_; 
v_unused_806_ = lean_ctor_get(v_a_789_, 3);
lean_dec(v_unused_806_);
v___x_799_ = v_a_789_;
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_bc_x3f_797_);
lean_inc(v_c_x3f_796_);
lean_inc(v_ir_x3f_795_);
lean_inc(v_irSig_x3f_794_);
lean_inc(v_ilean_x3f_793_);
lean_inc(v_oleanServer_x3f_792_);
lean_inc(v_olean_x3f_791_);
lean_inc(v_lean_x3f_790_);
lean_dec(v_a_789_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_801_, 0, v_filePath_788_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 3, v___x_801_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_lean_x3f_790_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_olean_x3f_791_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_oleanServer_x3f_792_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v_ilean_x3f_793_);
lean_ctor_set(v_reuseFailAlloc_804_, 5, v_irSig_x3f_794_);
lean_ctor_set(v_reuseFailAlloc_804_, 6, v_ir_x3f_795_);
lean_ctor_set(v_reuseFailAlloc_804_, 7, v_c_x3f_796_);
lean_ctor_set(v_reuseFailAlloc_804_, 8, v_bc_x3f_797_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1(lean_object* v_filePath_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_lean_x3f_809_; lean_object* v_olean_x3f_810_; lean_object* v_oleanServer_x3f_811_; lean_object* v_oleanPrivate_x3f_812_; lean_object* v_ilean_x3f_813_; lean_object* v_ir_x3f_814_; lean_object* v_c_x3f_815_; lean_object* v_bc_x3f_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
v_lean_x3f_809_ = lean_ctor_get(v_a_808_, 0);
v_olean_x3f_810_ = lean_ctor_get(v_a_808_, 1);
v_oleanServer_x3f_811_ = lean_ctor_get(v_a_808_, 2);
v_oleanPrivate_x3f_812_ = lean_ctor_get(v_a_808_, 3);
v_ilean_x3f_813_ = lean_ctor_get(v_a_808_, 4);
v_ir_x3f_814_ = lean_ctor_get(v_a_808_, 6);
v_c_x3f_815_ = lean_ctor_get(v_a_808_, 7);
v_bc_x3f_816_ = lean_ctor_get(v_a_808_, 8);
v_isSharedCheck_824_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v_a_808_, 5);
lean_dec(v_unused_825_);
v___x_818_ = v_a_808_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_bc_x3f_816_);
lean_inc(v_c_x3f_815_);
lean_inc(v_ir_x3f_814_);
lean_inc(v_ilean_x3f_813_);
lean_inc(v_oleanPrivate_x3f_812_);
lean_inc(v_oleanServer_x3f_811_);
lean_inc(v_olean_x3f_810_);
lean_inc(v_lean_x3f_809_);
lean_dec(v_a_808_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v_filePath_807_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 5, v___x_820_);
v___x_822_ = v___x_818_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_lean_x3f_809_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_olean_x3f_810_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v_oleanServer_x3f_811_);
lean_ctor_set(v_reuseFailAlloc_823_, 3, v_oleanPrivate_x3f_812_);
lean_ctor_set(v_reuseFailAlloc_823_, 4, v_ilean_x3f_813_);
lean_ctor_set(v_reuseFailAlloc_823_, 5, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_823_, 6, v_ir_x3f_814_);
lean_ctor_set(v_reuseFailAlloc_823_, 7, v_c_x3f_815_);
lean_ctor_set(v_reuseFailAlloc_823_, 8, v_bc_x3f_816_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4(lean_object* v_filePath_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_lean_x3f_828_; lean_object* v_olean_x3f_829_; lean_object* v_oleanPrivate_x3f_830_; lean_object* v_ilean_x3f_831_; lean_object* v_irSig_x3f_832_; lean_object* v_ir_x3f_833_; lean_object* v_c_x3f_834_; lean_object* v_bc_x3f_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_843_; 
v_lean_x3f_828_ = lean_ctor_get(v_a_827_, 0);
v_olean_x3f_829_ = lean_ctor_get(v_a_827_, 1);
v_oleanPrivate_x3f_830_ = lean_ctor_get(v_a_827_, 3);
v_ilean_x3f_831_ = lean_ctor_get(v_a_827_, 4);
v_irSig_x3f_832_ = lean_ctor_get(v_a_827_, 5);
v_ir_x3f_833_ = lean_ctor_get(v_a_827_, 6);
v_c_x3f_834_ = lean_ctor_get(v_a_827_, 7);
v_bc_x3f_835_ = lean_ctor_get(v_a_827_, 8);
v_isSharedCheck_843_ = !lean_is_exclusive(v_a_827_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v_a_827_, 2);
lean_dec(v_unused_844_);
v___x_837_ = v_a_827_;
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_bc_x3f_835_);
lean_inc(v_c_x3f_834_);
lean_inc(v_ir_x3f_833_);
lean_inc(v_irSig_x3f_832_);
lean_inc(v_ilean_x3f_831_);
lean_inc(v_oleanPrivate_x3f_830_);
lean_inc(v_olean_x3f_829_);
lean_inc(v_lean_x3f_828_);
lean_dec(v_a_827_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v_filePath_826_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 2, v___x_839_);
v___x_841_ = v___x_837_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_lean_x3f_828_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_olean_x3f_829_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_oleanPrivate_x3f_830_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_ilean_x3f_831_);
lean_ctor_set(v_reuseFailAlloc_842_, 5, v_irSig_x3f_832_);
lean_ctor_set(v_reuseFailAlloc_842_, 6, v_ir_x3f_833_);
lean_ctor_set(v_reuseFailAlloc_842_, 7, v_c_x3f_834_);
lean_ctor_set(v_reuseFailAlloc_842_, 8, v_bc_x3f_835_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(lean_object* v_a_845_, lean_object* v_x_846_){
_start:
{
if (lean_obj_tag(v_x_846_) == 0)
{
uint8_t v___x_847_; 
v___x_847_ = 0;
return v___x_847_;
}
else
{
lean_object* v_key_848_; lean_object* v_tail_849_; uint8_t v___x_850_; 
v_key_848_ = lean_ctor_get(v_x_846_, 0);
v_tail_849_ = lean_ctor_get(v_x_846_, 2);
v___x_850_ = lean_string_dec_eq(v_key_848_, v_a_845_);
if (v___x_850_ == 0)
{
v_x_846_ = v_tail_849_;
goto _start;
}
else
{
return v___x_850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg___boxed(lean_object* v_a_852_, lean_object* v_x_853_){
_start:
{
uint8_t v_res_854_; lean_object* v_r_855_; 
v_res_854_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_852_, v_x_853_);
lean_dec(v_x_853_);
lean_dec_ref(v_a_852_);
v_r_855_ = lean_box(v_res_854_);
return v_r_855_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(lean_object* v_m_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_buckets_858_; lean_object* v___x_859_; uint64_t v___x_860_; uint64_t v___x_861_; uint64_t v___x_862_; uint64_t v_fold_863_; uint64_t v___x_864_; uint64_t v___x_865_; uint64_t v___x_866_; size_t v___x_867_; size_t v___x_868_; size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v_buckets_858_ = lean_ctor_get(v_m_856_, 1);
v___x_859_ = lean_array_get_size(v_buckets_858_);
v___x_860_ = lean_string_hash(v_a_857_);
v___x_861_ = 32ULL;
v___x_862_ = lean_uint64_shift_right(v___x_860_, v___x_861_);
v_fold_863_ = lean_uint64_xor(v___x_860_, v___x_862_);
v___x_864_ = 16ULL;
v___x_865_ = lean_uint64_shift_right(v_fold_863_, v___x_864_);
v___x_866_ = lean_uint64_xor(v_fold_863_, v___x_865_);
v___x_867_ = lean_uint64_to_usize(v___x_866_);
v___x_868_ = lean_usize_of_nat(v___x_859_);
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_sub(v___x_868_, v___x_869_);
v___x_871_ = lean_usize_land(v___x_867_, v___x_870_);
v___x_872_ = lean_array_uget_borrowed(v_buckets_858_, v___x_871_);
v___x_873_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_857_, v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg___boxed(lean_object* v_m_874_, lean_object* v_a_875_){
_start:
{
uint8_t v_res_876_; lean_object* v_r_877_; 
v_res_876_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_874_, v_a_875_);
lean_dec_ref(v_a_875_);
lean_dec_ref(v_m_874_);
v_r_877_ = lean_box(v_res_876_);
return v_r_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(lean_object* v_a_878_, lean_object* v_fallback_879_, lean_object* v_x_880_){
_start:
{
if (lean_obj_tag(v_x_880_) == 0)
{
lean_inc(v_fallback_879_);
return v_fallback_879_;
}
else
{
lean_object* v_key_881_; lean_object* v_value_882_; lean_object* v_tail_883_; uint8_t v___x_884_; 
v_key_881_ = lean_ctor_get(v_x_880_, 0);
v_value_882_ = lean_ctor_get(v_x_880_, 1);
v_tail_883_ = lean_ctor_get(v_x_880_, 2);
v___x_884_ = lean_string_dec_eq(v_key_881_, v_a_878_);
if (v___x_884_ == 0)
{
v_x_880_ = v_tail_883_;
goto _start;
}
else
{
lean_inc(v_value_882_);
return v_value_882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg___boxed(lean_object* v_a_886_, lean_object* v_fallback_887_, lean_object* v_x_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_886_, v_fallback_887_, v_x_888_);
lean_dec(v_x_888_);
lean_dec(v_fallback_887_);
lean_dec_ref(v_a_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(lean_object* v_m_890_, lean_object* v_a_891_, lean_object* v_fallback_892_){
_start:
{
lean_object* v_buckets_893_; lean_object* v___x_894_; uint64_t v___x_895_; uint64_t v___x_896_; uint64_t v___x_897_; uint64_t v_fold_898_; uint64_t v___x_899_; uint64_t v___x_900_; uint64_t v___x_901_; size_t v___x_902_; size_t v___x_903_; size_t v___x_904_; size_t v___x_905_; size_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_buckets_893_ = lean_ctor_get(v_m_890_, 1);
v___x_894_ = lean_array_get_size(v_buckets_893_);
v___x_895_ = lean_string_hash(v_a_891_);
v___x_896_ = 32ULL;
v___x_897_ = lean_uint64_shift_right(v___x_895_, v___x_896_);
v_fold_898_ = lean_uint64_xor(v___x_895_, v___x_897_);
v___x_899_ = 16ULL;
v___x_900_ = lean_uint64_shift_right(v_fold_898_, v___x_899_);
v___x_901_ = lean_uint64_xor(v_fold_898_, v___x_900_);
v___x_902_ = lean_uint64_to_usize(v___x_901_);
v___x_903_ = lean_usize_of_nat(v___x_894_);
v___x_904_ = ((size_t)1ULL);
v___x_905_ = lean_usize_sub(v___x_903_, v___x_904_);
v___x_906_ = lean_usize_land(v___x_902_, v___x_905_);
v___x_907_ = lean_array_uget_borrowed(v_buckets_893_, v___x_906_);
v___x_908_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_891_, v_fallback_892_, v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg___boxed(lean_object* v_m_909_, lean_object* v_a_910_, lean_object* v_fallback_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_909_, v_a_910_, v_fallback_911_);
lean_dec(v_fallback_911_);
lean_dec_ref(v_a_910_);
lean_dec_ref(v_m_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2(lean_object* v_filePath_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_lean_x3f_915_; lean_object* v_olean_x3f_916_; lean_object* v_oleanServer_x3f_917_; lean_object* v_oleanPrivate_x3f_918_; lean_object* v_ilean_x3f_919_; lean_object* v_irSig_x3f_920_; lean_object* v_c_x3f_921_; lean_object* v_bc_x3f_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_930_; 
v_lean_x3f_915_ = lean_ctor_get(v_a_914_, 0);
v_olean_x3f_916_ = lean_ctor_get(v_a_914_, 1);
v_oleanServer_x3f_917_ = lean_ctor_get(v_a_914_, 2);
v_oleanPrivate_x3f_918_ = lean_ctor_get(v_a_914_, 3);
v_ilean_x3f_919_ = lean_ctor_get(v_a_914_, 4);
v_irSig_x3f_920_ = lean_ctor_get(v_a_914_, 5);
v_c_x3f_921_ = lean_ctor_get(v_a_914_, 7);
v_bc_x3f_922_ = lean_ctor_get(v_a_914_, 8);
v_isSharedCheck_930_ = !lean_is_exclusive(v_a_914_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v_a_914_, 6);
lean_dec(v_unused_931_);
v___x_924_ = v_a_914_;
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_bc_x3f_922_);
lean_inc(v_c_x3f_921_);
lean_inc(v_irSig_x3f_920_);
lean_inc(v_ilean_x3f_919_);
lean_inc(v_oleanPrivate_x3f_918_);
lean_inc(v_oleanServer_x3f_917_);
lean_inc(v_olean_x3f_916_);
lean_inc(v_lean_x3f_915_);
lean_dec(v_a_914_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_926_, 0, v_filePath_913_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 6, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_lean_x3f_915_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_olean_x3f_916_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_oleanServer_x3f_917_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_oleanPrivate_x3f_918_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v_ilean_x3f_919_);
lean_ctor_set(v_reuseFailAlloc_929_, 5, v_irSig_x3f_920_);
lean_ctor_set(v_reuseFailAlloc_929_, 6, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_929_, 7, v_c_x3f_921_);
lean_ctor_set(v_reuseFailAlloc_929_, 8, v_bc_x3f_922_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0(lean_object* v_filePath_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_lean_x3f_934_; lean_object* v_oleanServer_x3f_935_; lean_object* v_oleanPrivate_x3f_936_; lean_object* v_ilean_x3f_937_; lean_object* v_irSig_x3f_938_; lean_object* v_ir_x3f_939_; lean_object* v_c_x3f_940_; lean_object* v_bc_x3f_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_949_; 
v_lean_x3f_934_ = lean_ctor_get(v_a_933_, 0);
v_oleanServer_x3f_935_ = lean_ctor_get(v_a_933_, 2);
v_oleanPrivate_x3f_936_ = lean_ctor_get(v_a_933_, 3);
v_ilean_x3f_937_ = lean_ctor_get(v_a_933_, 4);
v_irSig_x3f_938_ = lean_ctor_get(v_a_933_, 5);
v_ir_x3f_939_ = lean_ctor_get(v_a_933_, 6);
v_c_x3f_940_ = lean_ctor_get(v_a_933_, 7);
v_bc_x3f_941_ = lean_ctor_get(v_a_933_, 8);
v_isSharedCheck_949_ = !lean_is_exclusive(v_a_933_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v_a_933_, 1);
lean_dec(v_unused_950_);
v___x_943_ = v_a_933_;
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_bc_x3f_941_);
lean_inc(v_c_x3f_940_);
lean_inc(v_ir_x3f_939_);
lean_inc(v_irSig_x3f_938_);
lean_inc(v_ilean_x3f_937_);
lean_inc(v_oleanPrivate_x3f_936_);
lean_inc(v_oleanServer_x3f_935_);
lean_inc(v_lean_x3f_934_);
lean_dec(v_a_933_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_945_, 0, v_filePath_932_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_945_);
v___x_947_ = v___x_943_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_lean_x3f_934_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_oleanServer_x3f_935_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_oleanPrivate_x3f_936_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v_ilean_x3f_937_);
lean_ctor_set(v_reuseFailAlloc_948_, 5, v_irSig_x3f_938_);
lean_ctor_set(v_reuseFailAlloc_948_, 6, v_ir_x3f_939_);
lean_ctor_set(v_reuseFailAlloc_948_, 7, v_c_x3f_940_);
lean_ctor_set(v_reuseFailAlloc_948_, 8, v_bc_x3f_941_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(lean_object* v_a_951_, lean_object* v_b_952_, lean_object* v_x_953_){
_start:
{
if (lean_obj_tag(v_x_953_) == 0)
{
lean_dec(v_b_952_);
lean_dec_ref(v_a_951_);
return v_x_953_;
}
else
{
lean_object* v_key_954_; lean_object* v_value_955_; lean_object* v_tail_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_968_; 
v_key_954_ = lean_ctor_get(v_x_953_, 0);
v_value_955_ = lean_ctor_get(v_x_953_, 1);
v_tail_956_ = lean_ctor_get(v_x_953_, 2);
v_isSharedCheck_968_ = !lean_is_exclusive(v_x_953_);
if (v_isSharedCheck_968_ == 0)
{
v___x_958_ = v_x_953_;
v_isShared_959_ = v_isSharedCheck_968_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_tail_956_);
lean_inc(v_value_955_);
lean_inc(v_key_954_);
lean_dec(v_x_953_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_968_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
uint8_t v___x_960_; 
v___x_960_ = lean_string_dec_eq(v_key_954_, v_a_951_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_951_, v_b_952_, v_tail_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 2, v___x_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_key_954_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_value_955_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
else
{
lean_object* v___x_966_; 
lean_dec(v_value_955_);
lean_dec(v_key_954_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v_b_952_);
lean_ctor_set(v___x_958_, 0, v_a_951_);
v___x_966_ = v___x_958_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_951_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_b_952_);
lean_ctor_set(v_reuseFailAlloc_967_, 2, v_tail_956_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
if (lean_obj_tag(v_x_970_) == 0)
{
return v_x_969_;
}
else
{
lean_object* v_key_971_; lean_object* v_value_972_; lean_object* v_tail_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_996_; 
v_key_971_ = lean_ctor_get(v_x_970_, 0);
v_value_972_ = lean_ctor_get(v_x_970_, 1);
v_tail_973_ = lean_ctor_get(v_x_970_, 2);
v_isSharedCheck_996_ = !lean_is_exclusive(v_x_970_);
if (v_isSharedCheck_996_ == 0)
{
v___x_975_ = v_x_970_;
v_isShared_976_ = v_isSharedCheck_996_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_tail_973_);
lean_inc(v_value_972_);
lean_inc(v_key_971_);
lean_dec(v_x_970_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_996_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; uint64_t v___x_978_; uint64_t v___x_979_; uint64_t v___x_980_; uint64_t v_fold_981_; uint64_t v___x_982_; uint64_t v___x_983_; uint64_t v___x_984_; size_t v___x_985_; size_t v___x_986_; size_t v___x_987_; size_t v___x_988_; size_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_977_ = lean_array_get_size(v_x_969_);
v___x_978_ = lean_string_hash(v_key_971_);
v___x_979_ = 32ULL;
v___x_980_ = lean_uint64_shift_right(v___x_978_, v___x_979_);
v_fold_981_ = lean_uint64_xor(v___x_978_, v___x_980_);
v___x_982_ = 16ULL;
v___x_983_ = lean_uint64_shift_right(v_fold_981_, v___x_982_);
v___x_984_ = lean_uint64_xor(v_fold_981_, v___x_983_);
v___x_985_ = lean_uint64_to_usize(v___x_984_);
v___x_986_ = lean_usize_of_nat(v___x_977_);
v___x_987_ = ((size_t)1ULL);
v___x_988_ = lean_usize_sub(v___x_986_, v___x_987_);
v___x_989_ = lean_usize_land(v___x_985_, v___x_988_);
v___x_990_ = lean_array_uget_borrowed(v_x_969_, v___x_989_);
lean_inc(v___x_990_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 2, v___x_990_);
v___x_992_ = v___x_975_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_key_971_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_value_972_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v___x_990_);
v___x_992_ = v_reuseFailAlloc_995_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; 
v___x_993_ = lean_array_uset(v_x_969_, v___x_989_, v___x_992_);
v_x_969_ = v___x_993_;
v_x_970_ = v_tail_973_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(lean_object* v_i_997_, lean_object* v_source_998_, lean_object* v_target_999_){
_start:
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = lean_array_get_size(v_source_998_);
v___x_1001_ = lean_nat_dec_lt(v_i_997_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_dec_ref(v_source_998_);
lean_dec(v_i_997_);
return v_target_999_;
}
else
{
lean_object* v_es_1002_; lean_object* v___x_1003_; lean_object* v_source_1004_; lean_object* v_target_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_es_1002_ = lean_array_fget(v_source_998_, v_i_997_);
v___x_1003_ = lean_box(0);
v_source_1004_ = lean_array_fset(v_source_998_, v_i_997_, v___x_1003_);
v_target_1005_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_target_999_, v_es_1002_);
v___x_1006_ = lean_unsigned_to_nat(1u);
v___x_1007_ = lean_nat_add(v_i_997_, v___x_1006_);
lean_dec(v_i_997_);
v_i_997_ = v___x_1007_;
v_source_998_ = v_source_1004_;
v_target_999_ = v_target_1005_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(lean_object* v_data_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v_nbuckets_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1010_ = lean_array_get_size(v_data_1009_);
v___x_1011_ = lean_unsigned_to_nat(2u);
v_nbuckets_1012_ = lean_nat_mul(v___x_1010_, v___x_1011_);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_mk_array(v_nbuckets_1012_, v___x_1014_);
v___x_1016_ = lean_array_propagate_mark(v_data_1009_, v___x_1015_);
v___x_1017_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v___x_1013_, v_data_1009_, v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object* v_m_1018_, lean_object* v_a_1019_, lean_object* v_b_1020_){
_start:
{
lean_object* v_size_1021_; lean_object* v_buckets_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1065_; 
v_size_1021_ = lean_ctor_get(v_m_1018_, 0);
v_buckets_1022_ = lean_ctor_get(v_m_1018_, 1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_m_1018_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1024_ = v_m_1018_;
v_isShared_1025_ = v_isSharedCheck_1065_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_buckets_1022_);
lean_inc(v_size_1021_);
lean_dec(v_m_1018_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1065_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; uint64_t v___x_1027_; uint64_t v___x_1028_; uint64_t v___x_1029_; uint64_t v_fold_1030_; uint64_t v___x_1031_; uint64_t v___x_1032_; uint64_t v___x_1033_; size_t v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; lean_object* v_bkt_1039_; uint8_t v___x_1040_; 
v___x_1026_ = lean_array_get_size(v_buckets_1022_);
v___x_1027_ = lean_string_hash(v_a_1019_);
v___x_1028_ = 32ULL;
v___x_1029_ = lean_uint64_shift_right(v___x_1027_, v___x_1028_);
v_fold_1030_ = lean_uint64_xor(v___x_1027_, v___x_1029_);
v___x_1031_ = 16ULL;
v___x_1032_ = lean_uint64_shift_right(v_fold_1030_, v___x_1031_);
v___x_1033_ = lean_uint64_xor(v_fold_1030_, v___x_1032_);
v___x_1034_ = lean_uint64_to_usize(v___x_1033_);
v___x_1035_ = lean_usize_of_nat(v___x_1026_);
v___x_1036_ = ((size_t)1ULL);
v___x_1037_ = lean_usize_sub(v___x_1035_, v___x_1036_);
v___x_1038_ = lean_usize_land(v___x_1034_, v___x_1037_);
v_bkt_1039_ = lean_array_uget_borrowed(v_buckets_1022_, v___x_1038_);
v___x_1040_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1019_, v_bkt_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v_size_x27_1042_; lean_object* v___x_1043_; lean_object* v_buckets_x27_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1041_ = lean_unsigned_to_nat(1u);
v_size_x27_1042_ = lean_nat_add(v_size_1021_, v___x_1041_);
lean_dec(v_size_1021_);
lean_inc(v_bkt_1039_);
v___x_1043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1043_, 0, v_a_1019_);
lean_ctor_set(v___x_1043_, 1, v_b_1020_);
lean_ctor_set(v___x_1043_, 2, v_bkt_1039_);
v_buckets_x27_1044_ = lean_array_uset(v_buckets_1022_, v___x_1038_, v___x_1043_);
v___x_1045_ = lean_unsigned_to_nat(4u);
v___x_1046_ = lean_nat_mul(v_size_x27_1042_, v___x_1045_);
v___x_1047_ = lean_unsigned_to_nat(3u);
v___x_1048_ = lean_nat_div(v___x_1046_, v___x_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_array_get_size(v_buckets_x27_1044_);
v___x_1050_ = lean_nat_dec_le(v___x_1048_, v___x_1049_);
lean_dec(v___x_1048_);
if (v___x_1050_ == 0)
{
lean_object* v_val_1051_; lean_object* v___x_1053_; 
v_val_1051_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_buckets_x27_1044_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v_val_1051_);
lean_ctor_set(v___x_1024_, 0, v_size_x27_1042_);
v___x_1053_ = v___x_1024_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_size_x27_1042_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_val_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
else
{
lean_object* v___x_1056_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v_buckets_x27_1044_);
lean_ctor_set(v___x_1024_, 0, v_size_x27_1042_);
v___x_1056_ = v___x_1024_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_size_x27_1042_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_buckets_x27_1044_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
else
{
lean_object* v___x_1058_; lean_object* v_buckets_x27_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_inc(v_bkt_1039_);
v___x_1058_ = lean_box(0);
v_buckets_x27_1059_ = lean_array_uset(v_buckets_1022_, v___x_1038_, v___x_1058_);
v___x_1060_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1019_, v_b_1020_, v_bkt_1039_);
v___x_1061_ = lean_array_uset(v_buckets_x27_1059_, v___x_1038_, v___x_1060_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v___x_1061_);
v___x_1063_ = v___x_1024_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_size_1021_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object* v_as_1074_, size_t v_sz_1075_, size_t v_i_1076_, lean_object* v_b_1077_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_lt(v_i_1076_, v_sz_1075_);
if (v___x_1078_ == 0)
{
return v_b_1077_;
}
else
{
lean_object* v_fst_1079_; lean_object* v_snd_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1130_; 
v_fst_1079_ = lean_ctor_get(v_b_1077_, 0);
v_snd_1080_ = lean_ctor_get(v_b_1077_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_b_1077_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1082_ = v_b_1077_;
v_isShared_1083_ = v_isSharedCheck_1130_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_snd_1080_);
lean_inc(v_fst_1079_);
lean_dec(v_b_1077_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1130_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v_order_1087_; lean_object* v_fst_1099_; lean_object* v_snd_1100_; lean_object* v_a_1103_; lean_object* v_filePath_1104_; lean_object* v___f_1105_; lean_object* v___x_1106_; 
v_a_1103_ = lean_array_uget_borrowed(v_as_1074_, v_i_1076_);
v_filePath_1104_ = lean_ctor_get(v_a_1103_, 0);
lean_inc_ref_n(v_filePath_1104_, 2);
v___f_1105_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1105_, 0, v_filePath_1104_);
v___x_1106_ = l_System_FilePath_extension(v_filePath_1104_);
if (lean_obj_tag(v___x_1106_) == 1)
{
lean_object* v_val_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v_val_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_val_1107_);
lean_dec_ref_known(v___x_1106_, 1);
v___x_1108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1));
v___x_1109_ = lean_string_dec_eq(v_val_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2));
v___x_1111_ = lean_string_dec_eq(v_val_1107_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3));
v___x_1113_ = lean_string_dec_eq(v_val_1107_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4));
v___x_1115_ = lean_string_dec_eq(v_val_1107_, v___x_1114_);
lean_dec(v_val_1107_);
if (v___x_1115_ == 0)
{
lean_inc_ref(v_filePath_1104_);
v_fst_1099_ = v_filePath_1104_;
v_snd_1100_ = v___f_1105_;
goto v___jp_1098_;
}
else
{
lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec_ref(v___f_1105_);
lean_inc_ref_n(v_filePath_1104_, 2);
v___f_1116_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1), 2, 1);
lean_closure_set(v___f_1116_, 0, v_filePath_1104_);
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1118_ = l_System_FilePath_withExtension(v_filePath_1104_, v___x_1117_);
v___x_1119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1120_ = l_System_FilePath_withExtension(v___x_1118_, v___x_1119_);
v_fst_1099_ = v___x_1120_;
v_snd_1100_ = v___f_1116_;
goto v___jp_1098_;
}
}
else
{
lean_object* v___f_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec(v_val_1107_);
lean_dec_ref(v___f_1105_);
lean_inc_ref_n(v_filePath_1104_, 2);
v___f_1121_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2), 2, 1);
lean_closure_set(v___f_1121_, 0, v_filePath_1104_);
v___x_1122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1123_ = l_System_FilePath_withExtension(v_filePath_1104_, v___x_1122_);
v_fst_1099_ = v___x_1123_;
v_snd_1100_ = v___f_1121_;
goto v___jp_1098_;
}
}
else
{
lean_object* v___f_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec(v_val_1107_);
lean_dec_ref(v___f_1105_);
lean_inc_ref_n(v_filePath_1104_, 2);
v___f_1124_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3), 2, 1);
lean_closure_set(v___f_1124_, 0, v_filePath_1104_);
v___x_1125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1126_ = l_System_FilePath_withExtension(v_filePath_1104_, v___x_1125_);
v_fst_1099_ = v___x_1126_;
v_snd_1100_ = v___f_1124_;
goto v___jp_1098_;
}
}
else
{
lean_object* v___f_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec(v_val_1107_);
lean_dec_ref(v___f_1105_);
lean_inc_ref_n(v_filePath_1104_, 2);
v___f_1127_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4), 2, 1);
lean_closure_set(v___f_1127_, 0, v_filePath_1104_);
v___x_1128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1129_ = l_System_FilePath_withExtension(v_filePath_1104_, v___x_1128_);
v_fst_1099_ = v___x_1129_;
v_snd_1100_ = v___f_1127_;
goto v___jp_1098_;
}
}
else
{
lean_dec(v___x_1106_);
lean_inc_ref(v_filePath_1104_);
v_fst_1099_ = v_filePath_1104_;
v_snd_1100_ = v___f_1105_;
goto v___jp_1098_;
}
v___jp_1084_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0));
v___x_1089_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_snd_1080_, v___y_1085_, v___x_1088_);
v___x_1090_ = lean_apply_1(v___y_1086_, v___x_1089_);
v___x_1091_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_snd_1080_, v___y_1085_, v___x_1090_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 1, v___x_1091_);
lean_ctor_set(v___x_1082_, 0, v_order_1087_);
v___x_1093_ = v___x_1082_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_order_1087_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
size_t v___x_1094_; size_t v___x_1095_; 
v___x_1094_ = ((size_t)1ULL);
v___x_1095_ = lean_usize_add(v_i_1076_, v___x_1094_);
v_i_1076_ = v___x_1095_;
v_b_1077_ = v___x_1093_;
goto _start;
}
}
v___jp_1098_:
{
uint8_t v___x_1101_; 
v___x_1101_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1080_, v_fst_1099_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
lean_inc_ref(v_fst_1099_);
v___x_1102_ = lean_array_push(v_fst_1079_, v_fst_1099_);
v___y_1085_ = v_fst_1099_;
v___y_1086_ = v_snd_1100_;
v_order_1087_ = v___x_1102_;
goto v___jp_1084_;
}
else
{
v___y_1085_ = v_fst_1099_;
v___y_1086_ = v_snd_1100_;
v_order_1087_ = v_fst_1079_;
goto v___jp_1084_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object* v_as_1131_, lean_object* v_sz_1132_, lean_object* v_i_1133_, lean_object* v_b_1134_){
_start:
{
size_t v_sz_boxed_1135_; size_t v_i_boxed_1136_; lean_object* v_res_1137_; 
v_sz_boxed_1135_ = lean_unbox_usize(v_sz_1132_);
lean_dec(v_sz_1132_);
v_i_boxed_1136_ = lean_unbox_usize(v_i_1133_);
lean_dec(v_i_1133_);
v_res_1137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_as_1131_, v_sz_boxed_1135_, v_i_boxed_1136_, v_b_1134_);
lean_dec_ref(v_as_1131_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(lean_object* v_msg_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1140_ = lean_panic_fn_borrowed(v___x_1139_, v_msg_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1144_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2));
v___x_1145_ = lean_unsigned_to_nat(11u);
v___x_1146_ = lean_unsigned_to_nat(163u);
v___x_1147_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1));
v___x_1148_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0));
v___x_1149_ = l_mkPanicMessageWithDecl(v___x_1148_, v___x_1147_, v___x_1146_, v___x_1145_, v___x_1144_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(lean_object* v_a_1150_, lean_object* v_x_1151_){
_start:
{
if (lean_obj_tag(v_x_1151_) == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3);
v___x_1153_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(v___x_1152_);
return v___x_1153_;
}
else
{
lean_object* v_key_1154_; lean_object* v_value_1155_; lean_object* v_tail_1156_; uint8_t v___x_1157_; 
v_key_1154_ = lean_ctor_get(v_x_1151_, 0);
v_value_1155_ = lean_ctor_get(v_x_1151_, 1);
v_tail_1156_ = lean_ctor_get(v_x_1151_, 2);
v___x_1157_ = lean_string_dec_eq(v_key_1154_, v_a_1150_);
if (v___x_1157_ == 0)
{
v_x_1151_ = v_tail_1156_;
goto _start;
}
else
{
lean_inc(v_value_1155_);
return v_value_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___boxed(lean_object* v_a_1159_, lean_object* v_x_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1159_, v_x_1160_);
lean_dec(v_x_1160_);
lean_dec_ref(v_a_1159_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object* v_m_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_buckets_1164_; lean_object* v___x_1165_; uint64_t v___x_1166_; uint64_t v___x_1167_; uint64_t v___x_1168_; uint64_t v_fold_1169_; uint64_t v___x_1170_; uint64_t v___x_1171_; uint64_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; size_t v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_buckets_1164_ = lean_ctor_get(v_m_1162_, 1);
v___x_1165_ = lean_array_get_size(v_buckets_1164_);
v___x_1166_ = lean_string_hash(v_a_1163_);
v___x_1167_ = 32ULL;
v___x_1168_ = lean_uint64_shift_right(v___x_1166_, v___x_1167_);
v_fold_1169_ = lean_uint64_xor(v___x_1166_, v___x_1168_);
v___x_1170_ = 16ULL;
v___x_1171_ = lean_uint64_shift_right(v_fold_1169_, v___x_1170_);
v___x_1172_ = lean_uint64_xor(v_fold_1169_, v___x_1171_);
v___x_1173_ = lean_uint64_to_usize(v___x_1172_);
v___x_1174_ = lean_usize_of_nat(v___x_1165_);
v___x_1175_ = ((size_t)1ULL);
v___x_1176_ = lean_usize_sub(v___x_1174_, v___x_1175_);
v___x_1177_ = lean_usize_land(v___x_1173_, v___x_1176_);
v___x_1178_ = lean_array_uget_borrowed(v_buckets_1164_, v___x_1177_);
v___x_1179_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1163_, v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object* v_m_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v_m_1180_, v_a_1181_);
lean_dec_ref(v_a_1181_);
lean_dec_ref(v_m_1180_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object* v___x_1183_, size_t v_sz_1184_, size_t v_i_1185_, lean_object* v_bs_1186_){
_start:
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_usize_dec_lt(v_i_1185_, v_sz_1184_);
if (v___x_1187_ == 0)
{
return v_bs_1186_;
}
else
{
lean_object* v_v_1188_; lean_object* v___x_1189_; lean_object* v_bs_x27_1190_; lean_object* v___x_1191_; size_t v___x_1192_; size_t v___x_1193_; lean_object* v___x_1194_; 
v_v_1188_ = lean_array_uget(v_bs_1186_, v_i_1185_);
v___x_1189_ = lean_unsigned_to_nat(0u);
v_bs_x27_1190_ = lean_array_uset(v_bs_1186_, v_i_1185_, v___x_1189_);
v___x_1191_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v___x_1183_, v_v_1188_);
lean_dec(v_v_1188_);
v___x_1192_ = ((size_t)1ULL);
v___x_1193_ = lean_usize_add(v_i_1185_, v___x_1192_);
v___x_1194_ = lean_array_uset(v_bs_x27_1190_, v_i_1185_, v___x_1191_);
v_i_1185_ = v___x_1193_;
v_bs_1186_ = v___x_1194_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object* v___x_1196_, lean_object* v_sz_1197_, lean_object* v_i_1198_, lean_object* v_bs_1199_){
_start:
{
size_t v_sz_boxed_1200_; size_t v_i_boxed_1201_; lean_object* v_res_1202_; 
v_sz_boxed_1200_ = lean_unbox_usize(v_sz_1197_);
lean_dec(v_sz_1197_);
v_i_boxed_1201_ = lean_unbox_usize(v_i_1198_);
lean_dec(v_i_1198_);
v_res_1202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v___x_1196_, v_sz_boxed_1200_, v_i_boxed_1201_, v_bs_1199_);
lean_dec_ref(v___x_1196_);
return v_res_1202_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_unsigned_to_nat(16u);
v___x_1207_ = lean_mk_array(v___x_1206_, v___x_1205_);
return v___x_1207_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_byBase_1210_; 
v___x_1208_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1);
v___x_1209_ = lean_unsigned_to_nat(0u);
v_byBase_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byBase_1210_, 0, v___x_1209_);
lean_ctor_set(v_byBase_1210_, 1, v___x_1208_);
return v_byBase_1210_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3(void){
_start:
{
lean_object* v_byBase_1211_; lean_object* v_order_1212_; lean_object* v___x_1213_; 
v_byBase_1211_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2);
v_order_1212_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0));
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v_order_1212_);
lean_ctor_set(v___x_1213_, 1, v_byBase_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object* v_regions_1214_){
_start:
{
lean_object* v___x_1215_; size_t v_sz_1216_; size_t v___x_1217_; lean_object* v___x_1218_; lean_object* v_fst_1219_; lean_object* v_snd_1220_; size_t v_sz_1221_; lean_object* v___x_1222_; 
v___x_1215_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3);
v_sz_1216_ = lean_array_size(v_regions_1214_);
v___x_1217_ = ((size_t)0ULL);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_regions_1214_, v_sz_1216_, v___x_1217_, v___x_1215_);
v_fst_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_fst_1219_);
v_snd_1220_ = lean_ctor_get(v___x_1218_, 1);
lean_inc(v_snd_1220_);
lean_dec_ref(v___x_1218_);
v_sz_1221_ = lean_array_size(v_fst_1219_);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v_snd_1220_, v_sz_1221_, v___x_1217_, v_fst_1219_);
lean_dec(v_snd_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object* v_regions_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1223_);
lean_dec_ref(v_regions_1223_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object* v_00_u03b2_1225_, lean_object* v_m_1226_, lean_object* v_a_1227_, lean_object* v_fallback_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_1226_, v_a_1227_, v_fallback_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object* v_00_u03b2_1230_, lean_object* v_m_1231_, lean_object* v_a_1232_, lean_object* v_fallback_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(v_00_u03b2_1230_, v_m_1231_, v_a_1232_, v_fallback_1233_);
lean_dec(v_fallback_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_m_1231_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object* v_00_u03b2_1235_, lean_object* v_m_1236_, lean_object* v_a_1237_, lean_object* v_b_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_1236_, v_a_1237_, v_b_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object* v_00_u03b2_1240_, lean_object* v_m_1241_, lean_object* v_a_1242_){
_start:
{
uint8_t v___x_1243_; 
v___x_1243_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_1241_, v_a_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object* v_00_u03b2_1244_, lean_object* v_m_1245_, lean_object* v_a_1246_){
_start:
{
uint8_t v_res_1247_; lean_object* v_r_1248_; 
v_res_1247_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(v_00_u03b2_1244_, v_m_1245_, v_a_1246_);
lean_dec_ref(v_a_1246_);
lean_dec_ref(v_m_1245_);
v_r_1248_ = lean_box(v_res_1247_);
return v_r_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object* v_00_u03b2_1249_, lean_object* v_a_1250_, lean_object* v_fallback_1251_, lean_object* v_x_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_1250_, v_fallback_1251_, v_x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1254_, lean_object* v_a_1255_, lean_object* v_fallback_1256_, lean_object* v_x_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(v_00_u03b2_1254_, v_a_1255_, v_fallback_1256_, v_x_1257_);
lean_dec(v_x_1257_);
lean_dec(v_fallback_1256_);
lean_dec_ref(v_a_1255_);
return v_res_1258_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object* v_00_u03b2_1259_, lean_object* v_a_1260_, lean_object* v_x_1261_){
_start:
{
uint8_t v___x_1262_; 
v___x_1262_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1260_, v_x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1263_, lean_object* v_a_1264_, lean_object* v_x_1265_){
_start:
{
uint8_t v_res_1266_; lean_object* v_r_1267_; 
v_res_1266_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(v_00_u03b2_1263_, v_a_1264_, v_x_1265_);
lean_dec(v_x_1265_);
lean_dec_ref(v_a_1264_);
v_r_1267_ = lean_box(v_res_1266_);
return v_r_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3(lean_object* v_00_u03b2_1268_, lean_object* v_data_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_data_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4(lean_object* v_00_u03b2_1271_, lean_object* v_a_1272_, lean_object* v_b_1273_, lean_object* v_x_1274_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1272_, v_b_1273_, v_x_1274_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1276_, lean_object* v_i_1277_, lean_object* v_source_1278_, lean_object* v_target_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v_i_1277_, v_source_1278_, v_target_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1281_, lean_object* v_x_1282_, lean_object* v_x_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_x_1282_, v_x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(lean_object* v_as_1285_, size_t v_sz_1286_, size_t v_i_1287_, lean_object* v_b_1288_){
_start:
{
uint8_t v___x_1290_; 
v___x_1290_ = lean_usize_dec_lt(v_i_1287_, v_sz_1286_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v_b_1288_);
return v___x_1291_;
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1293_; 
v_a_1292_ = lean_array_uget_borrowed(v_as_1285_, v_i_1287_);
v___x_1293_ = lean_compacted_region_read(v_a_1292_, v_b_1288_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v_snd_1295_; lean_object* v___x_1296_; size_t v___x_1297_; size_t v___x_1298_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v_snd_1295_ = lean_ctor_get(v_a_1294_, 1);
lean_inc(v_snd_1295_);
lean_dec(v_a_1294_);
v___x_1296_ = lean_array_push(v_b_1288_, v_snd_1295_);
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = lean_usize_add(v_i_1287_, v___x_1297_);
v_i_1287_ = v___x_1298_;
v_b_1288_ = v___x_1296_;
goto _start;
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v_b_1288_);
v_a_1300_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1293_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1293_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0___boxed(lean_object* v_as_1308_, lean_object* v_sz_1309_, lean_object* v_i_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_){
_start:
{
size_t v_sz_boxed_1313_; size_t v_i_boxed_1314_; lean_object* v_res_1315_; 
v_sz_boxed_1313_ = lean_unbox_usize(v_sz_1309_);
lean_dec(v_sz_1309_);
v_i_boxed_1314_ = lean_unbox_usize(v_i_1310_);
lean_dec(v_i_1310_);
v_res_1315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v_as_1308_, v_sz_boxed_1313_, v_i_boxed_1314_, v_b_1311_);
lean_dec_ref(v_as_1308_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(lean_object* v_arts_1318_){
_start:
{
lean_object* v_oleanRegions_1320_; lean_object* v___x_1321_; size_t v_sz_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v_oleanRegions_1320_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc_ref(v_arts_1318_);
v___x_1321_ = l_Lean_ModuleArtifacts_oleanParts(v_arts_1318_);
v_sz_1322_ = lean_array_size(v___x_1321_);
v___x_1323_ = ((size_t)0ULL);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1321_, v_sz_1322_, v___x_1323_, v_oleanRegions_1320_);
lean_dec_ref(v___x_1321_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1326_; size_t v_sz_1327_; lean_object* v___x_1328_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v___x_1326_ = l_Lean_ModuleArtifacts_irParts(v_arts_1318_);
v_sz_1327_ = lean_array_size(v___x_1326_);
v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1326_, v_sz_1327_, v___x_1323_, v_oleanRegions_1320_);
lean_dec_ref(v___x_1326_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1337_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1337_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1337_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1333_ = l_Array_append___redArg(v_a_1325_, v_a_1329_);
lean_dec(v_a_1329_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1333_);
v___x_1335_ = v___x_1331_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
else
{
lean_dec(v_a_1325_);
return v___x_1328_;
}
}
else
{
lean_dec_ref(v_arts_1318_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___boxed(lean_object* v_arts_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v_arts_1338_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(lean_object* v_e_1341_){
_start:
{
if (lean_obj_tag(v_e_1341_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1352_; 
v_a_1343_ = lean_ctor_get(v_e_1341_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_e_1341_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1345_ = v_e_1341_;
v_isShared_1346_ = v_isSharedCheck_1352_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v_e_1341_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1352_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1347_ = lean_io_error_to_string(v_a_1343_);
v___x_1348_ = lean_mk_io_user_error(v___x_1347_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 1);
lean_ctor_set(v___x_1345_, 0, v___x_1348_);
v___x_1350_ = v___x_1345_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_a_1353_ = lean_ctor_get(v_e_1341_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_e_1341_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v_e_1341_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v_e_1341_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 0);
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg___boxed(lean_object* v_e_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_object* v_00_u03b1_1364_, lean_object* v_e_1365_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___boxed(lean_object* v_00_u03b1_1368_, lean_object* v_e_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(v_00_u03b1_1368_, v_e_1369_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object* v_a_1372_, lean_object* v___y_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v_fst_1376_; lean_object* v_snd_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1405_; 
v_fst_1376_ = lean_ctor_get(v_a_1374_, 0);
v_snd_1377_ = lean_ctor_get(v_a_1374_, 1);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_a_1374_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1379_ = v_a_1374_;
v_isShared_1380_ = v_isSharedCheck_1405_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_snd_1377_);
lean_inc(v_fst_1376_);
lean_dec(v_a_1374_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1405_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1381_ = lean_array_get_size(v_a_1372_);
v___x_1382_ = lean_nat_dec_lt(v_snd_1377_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1384_; 
if (v_isShared_1380_ == 0)
{
v___x_1384_ = v___x_1379_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_fst_1376_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_snd_1377_);
v___x_1384_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
return v___x_1385_;
}
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1388_ = lean_array_get_borrowed(v___x_1387_, v_a_1372_, v_snd_1377_);
lean_inc(v___x_1388_);
v___x_1389_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v___x_1388_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = l_Array_append___redArg(v_fst_1376_, v_a_1390_);
lean_dec(v_a_1390_);
v___x_1392_ = lean_nat_add(v_snd_1377_, v___y_1373_);
lean_dec(v_snd_1377_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 1, v___x_1392_);
lean_ctor_set(v___x_1379_, 0, v___x_1391_);
v___x_1394_ = v___x_1379_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
v_a_1374_ = v___x_1394_;
goto _start;
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_del_object(v___x_1379_);
lean_dec(v_snd_1377_);
lean_dec(v_fst_1376_);
v_a_1397_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1389_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1389_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object* v_a_1406_, lean_object* v___y_1407_, lean_object* v_a_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1406_, v___y_1407_, v_a_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v_a_1406_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(lean_object* v_a_1411_, lean_object* v___y_1412_, lean_object* v___x_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1411_, v___y_1412_, v___x_1413_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_fst_1420_; lean_object* v___x_1422_; 
v_fst_1420_ = lean_ctor_get(v_a_1416_, 0);
lean_inc(v_fst_1420_);
lean_dec(v_a_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set_tag(v___x_1418_, 1);
lean_ctor_set(v___x_1418_, 0, v_fst_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_fst_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
v_a_1425_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1415_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1415_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set_tag(v___x_1427_, 0);
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed(lean_object* v_a_1433_, lean_object* v___y_1434_, lean_object* v___x_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(v_a_1433_, v___y_1434_, v___x_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v_a_1433_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(lean_object* v_upperBound_1438_, lean_object* v_a_1439_, lean_object* v___y_1440_, lean_object* v_a_1441_, lean_object* v_b_1442_){
_start:
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_nat_dec_lt(v_a_1441_, v_upperBound_1438_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; 
lean_dec(v_a_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v_a_1439_);
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v_b_1442_);
return v___x_1445_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___f_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc(v_a_1441_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
lean_ctor_set(v___x_1448_, 1, v_a_1441_);
lean_inc(v___y_1440_);
lean_inc_ref(v_a_1439_);
v___f_1449_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1449_, 0, v_a_1439_);
lean_closure_set(v___f_1449_, 1, v___y_1440_);
lean_closure_set(v___f_1449_, 2, v___x_1448_);
v___x_1450_ = lean_io_as_task(v___f_1449_, v___x_1446_);
v___x_1451_ = lean_array_push(v_b_1442_, v___x_1450_);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v_a_1441_, v___x_1452_);
lean_dec(v_a_1441_);
v_a_1441_ = v___x_1453_;
v_b_1442_ = v___x_1451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___boxed(lean_object* v_upperBound_1455_, lean_object* v_a_1456_, lean_object* v___y_1457_, lean_object* v_a_1458_, lean_object* v_b_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1455_, v_a_1456_, v___y_1457_, v_a_1458_, v_b_1459_);
lean_dec(v_upperBound_1455_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(lean_object* v_as_1462_, size_t v_sz_1463_, size_t v_i_1464_, lean_object* v_b_1465_){
_start:
{
uint8_t v___x_1467_; 
v___x_1467_ = lean_usize_dec_lt(v_i_1464_, v_sz_1463_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_b_1465_);
return v___x_1468_;
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_a_1469_ = lean_array_uget_borrowed(v_as_1462_, v_i_1464_);
lean_inc(v_a_1469_);
v___x_1470_ = lean_task_get_own(v_a_1469_);
v___x_1471_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v___x_1470_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; size_t v___x_1474_; size_t v___x_1475_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1473_ = l_Array_append___redArg(v_b_1465_, v_a_1472_);
lean_dec(v_a_1472_);
v___x_1474_ = ((size_t)1ULL);
v___x_1475_ = lean_usize_add(v_i_1464_, v___x_1474_);
v_i_1464_ = v___x_1475_;
v_b_1465_ = v___x_1473_;
goto _start;
}
else
{
lean_dec_ref(v_b_1465_);
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2___boxed(lean_object* v_as_1477_, lean_object* v_sz_1478_, lean_object* v_i_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_){
_start:
{
size_t v_sz_boxed_1482_; size_t v_i_boxed_1483_; lean_object* v_res_1484_; 
v_sz_boxed_1482_ = lean_unbox_usize(v_sz_1478_);
lean_dec(v_sz_1478_);
v_i_boxed_1483_ = lean_unbox_usize(v_i_1479_);
lean_dec(v_i_1479_);
v_res_1484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_as_1477_, v_sz_boxed_1482_, v_i_boxed_1483_, v_b_1480_);
lean_dec_ref(v_as_1477_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t v_sz_1485_, size_t v_i_1486_, lean_object* v_bs_1487_){
_start:
{
uint8_t v___x_1488_; 
v___x_1488_ = lean_usize_dec_lt(v_i_1486_, v_sz_1485_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1489_, 0, v_bs_1487_);
return v___x_1489_;
}
else
{
lean_object* v_v_1490_; lean_object* v___x_1491_; 
v_v_1490_ = lean_array_uget_borrowed(v_bs_1487_, v_i_1486_);
lean_inc(v_v_1490_);
v___x_1491_ = l_Lean_instFromJsonModuleArtifacts_fromJson(v_v_1490_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v_bs_1487_);
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
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
else
{
lean_object* v_a_1500_; lean_object* v___x_1501_; lean_object* v_bs_x27_1502_; size_t v___x_1503_; size_t v___x_1504_; lean_object* v___x_1505_; 
v_a_1500_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1501_ = lean_unsigned_to_nat(0u);
v_bs_x27_1502_ = lean_array_uset(v_bs_1487_, v_i_1486_, v___x_1501_);
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = lean_usize_add(v_i_1486_, v___x_1503_);
v___x_1505_ = lean_array_uset(v_bs_x27_1502_, v_i_1486_, v_a_1500_);
v_i_1486_ = v___x_1504_;
v_bs_1487_ = v___x_1505_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object* v_sz_1507_, lean_object* v_i_1508_, lean_object* v_bs_1509_){
_start:
{
size_t v_sz_boxed_1510_; size_t v_i_boxed_1511_; lean_object* v_res_1512_; 
v_sz_boxed_1510_ = lean_unbox_usize(v_sz_1507_);
lean_dec(v_sz_1507_);
v_i_boxed_1511_ = lean_unbox_usize(v_i_1508_);
lean_dec(v_i_1508_);
v_res_1512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_boxed_1510_, v_i_boxed_1511_, v_bs_1509_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object* v_x_1515_){
_start:
{
if (lean_obj_tag(v_x_1515_) == 4)
{
lean_object* v_elems_1516_; size_t v_sz_1517_; size_t v___x_1518_; lean_object* v___x_1519_; 
v_elems_1516_ = lean_ctor_get(v_x_1515_, 0);
lean_inc_ref(v_elems_1516_);
lean_dec_ref_known(v_x_1515_, 1);
v_sz_1517_ = lean_array_size(v_elems_1516_);
v___x_1518_ = ((size_t)0ULL);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_1517_, v___x_1518_, v_elems_1516_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1520_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0));
v___x_1521_ = lean_unsigned_to_nat(80u);
v___x_1522_ = l_Lean_Json_pretty(v_x_1515_, v___x_1521_);
v___x_1523_ = lean_string_append(v___x_1520_, v___x_1522_);
lean_dec_ref(v___x_1522_);
v___x_1524_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1));
v___x_1525_ = lean_string_append(v___x_1523_, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
}
static uint32_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3(void){
_start:
{
lean_object* v___x_1530_; uint32_t v___x_1531_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_internal_get_hardware_concurrency(v___x_1530_);
return v___x_1531_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4(void){
_start:
{
uint32_t v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_uint32_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3);
v___x_1533_ = lean_uint32_to_nat(v___x_1532_);
return v___x_1533_;
}
}
static uint8_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1535_ = lean_unsigned_to_nat(4u);
v___x_1536_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1537_ = lean_nat_dec_le(v___x_1536_, v___x_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(lean_object* v_fname_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v_depsFile_1541_; lean_object* v___x_1542_; 
v___x_1540_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
lean_inc_ref(v_fname_1538_);
v_depsFile_1541_ = l_System_FilePath_addExtension(v_fname_1538_, v___x_1540_);
v___x_1542_ = l_IO_FS_readFile(v_depsFile_1541_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1629_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1629_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1629_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v_a_1548_; lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Json_parse(v_a_1543_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; 
lean_dec_ref(v_fname_1538_);
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v_a_1548_ = v_a_1559_;
goto v___jp_1547_;
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1561_; 
v_a_1560_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1561_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(v_a_1560_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; 
lean_dec_ref(v_fname_1538_);
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
v_a_1548_ = v_a_1562_;
goto v___jp_1547_;
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___y_1567_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1618_; uint8_t v___x_1628_; 
lean_del_object(v___x_1545_);
lean_dec_ref(v_depsFile_1541_);
v_a_1563_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1561_, 1);
v___x_1564_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1565_ = lean_unsigned_to_nat(4u);
v___x_1628_ = lean_uint8_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6);
if (v___x_1628_ == 0)
{
v___y_1618_ = v___x_1565_;
goto v___jp_1617_;
}
else
{
v___y_1618_ = v___x_1564_;
goto v___jp_1617_;
}
v___jp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = lean_mk_empty_array_with_capacity(v___y_1567_);
v___x_1569_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_1563_);
lean_inc(v___y_1567_);
v___x_1570_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v___y_1567_, v_a_1563_, v___y_1567_, v___x_1569_, v___x_1568_);
lean_dec(v___y_1567_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; size_t v_sz_1575_; size_t v___x_1576_; lean_object* v___x_1577_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v___x_1572_ = lean_array_get_size(v_a_1563_);
lean_dec(v_a_1563_);
v___x_1573_ = lean_nat_mul(v___x_1572_, v___x_1565_);
v___x_1574_ = lean_mk_empty_array_with_capacity(v___x_1573_);
lean_dec(v___x_1573_);
v_sz_1575_ = lean_array_size(v_a_1571_);
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_a_1571_, v_sz_1575_, v___x_1576_, v___x_1574_);
lean_dec(v_a_1571_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = lean_compacted_region_read(v_fname_1538_, v_a_1578_);
lean_dec(v_a_1578_);
lean_dec_ref(v_fname_1538_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1588_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1588_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1588_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v_fst_1584_; lean_object* v___x_1586_; 
v_fst_1584_ = lean_ctor_get(v_a_1580_, 0);
lean_inc(v_fst_1584_);
lean_dec(v_a_1580_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v_fst_1584_);
v___x_1586_ = v___x_1582_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_fst_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
v_a_1589_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1579_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1579_);
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
lean_dec_ref(v_fname_1538_);
v_a_1597_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1577_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1577_);
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
else
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_a_1563_);
lean_dec_ref(v_fname_1538_);
v_a_1605_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1570_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1570_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
v___jp_1613_:
{
uint8_t v___x_1616_; 
v___x_1616_ = lean_nat_dec_le(v___y_1614_, v___y_1615_);
if (v___x_1616_ == 0)
{
lean_dec(v___y_1615_);
v___y_1567_ = v___y_1614_;
goto v___jp_1566_;
}
else
{
lean_dec(v___y_1614_);
v___y_1567_ = v___y_1615_;
goto v___jp_1566_;
}
}
v___jp_1617_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5));
v___x_1620_ = lean_io_getenv(v___x_1619_);
v___x_1621_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v___x_1620_) == 0)
{
v___y_1614_ = v___x_1621_;
v___y_1615_ = v___y_1618_;
goto v___jp_1613_;
}
else
{
lean_object* v_val_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v_val_1622_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_val_1622_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_string_utf8_byte_size(v_val_1622_);
v___x_1625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1625_, 0, v_val_1622_);
lean_ctor_set(v___x_1625_, 1, v___x_1623_);
lean_ctor_set(v___x_1625_, 2, v___x_1624_);
v___x_1626_ = l_String_Slice_toNat_x3f(v___x_1625_);
lean_dec_ref_known(v___x_1625_, 3);
if (lean_obj_tag(v___x_1626_) == 0)
{
v___y_1614_ = v___x_1621_;
v___y_1615_ = v___y_1618_;
goto v___jp_1613_;
}
else
{
lean_object* v_val_1627_; 
lean_dec(v___y_1618_);
v_val_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_val_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___y_1614_ = v___x_1621_;
v___y_1615_ = v_val_1627_;
goto v___jp_1613_;
}
}
}
}
}
v___jp_1547_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1549_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1));
v___x_1550_ = lean_string_append(v___x_1549_, v_depsFile_1541_);
lean_dec_ref(v_depsFile_1541_);
v___x_1551_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2));
v___x_1552_ = lean_string_append(v___x_1550_, v___x_1551_);
v___x_1553_ = lean_string_append(v___x_1552_, v_a_1548_);
lean_dec_ref(v_a_1548_);
v___x_1554_ = lean_mk_io_user_error(v___x_1553_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set_tag(v___x_1545_, 1);
lean_ctor_set(v___x_1545_, 0, v___x_1554_);
v___x_1556_ = v___x_1545_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v_depsFile_1541_);
lean_dec_ref(v_fname_1538_);
v_a_1630_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1542_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1542_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___boxed(lean_object* v_fname_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_fname_1638_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object* v_a_1641_, lean_object* v___y_1642_, lean_object* v_inst_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1641_, v___y_1642_, v_a_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object* v_a_1647_, lean_object* v___y_1648_, lean_object* v_inst_1649_, lean_object* v_a_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(v_a_1647_, v___y_1648_, v_inst_1649_, v_a_1650_);
lean_dec(v___y_1648_);
lean_dec_ref(v_a_1647_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object* v_upperBound_1653_, lean_object* v_a_1654_, lean_object* v___y_1655_, lean_object* v_inst_1656_, lean_object* v_R_1657_, lean_object* v_a_1658_, lean_object* v_b_1659_, lean_object* v_c_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1653_, v_a_1654_, v___y_1655_, v_a_1658_, v_b_1659_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object* v_upperBound_1663_, lean_object* v_a_1664_, lean_object* v___y_1665_, lean_object* v_inst_1666_, lean_object* v_R_1667_, lean_object* v_a_1668_, lean_object* v_b_1669_, lean_object* v_c_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(v_upperBound_1663_, v_a_1664_, v___y_1665_, v_inst_1666_, v_R_1667_, v_a_1668_, v_b_1669_, v_c_1670_);
lean_dec(v_upperBound_1663_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object* v_as_1673_, size_t v_sz_1674_, size_t v_i_1675_, lean_object* v_b_1676_){
_start:
{
uint8_t v___x_1678_; 
v___x_1678_ = lean_usize_dec_lt(v_i_1675_, v_sz_1674_);
if (v___x_1678_ == 0)
{
return v_b_1676_;
}
else
{
lean_object* v_a_1679_; lean_object* v_cancelTk_x3f_1680_; lean_object* v___x_1681_; 
v_a_1679_ = lean_array_uget_borrowed(v_as_1673_, v_i_1675_);
v_cancelTk_x3f_1680_ = lean_ctor_get(v_a_1679_, 2);
v___x_1681_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_1680_) == 1)
{
lean_object* v_val_1688_; lean_object* v___x_1689_; 
v_val_1688_ = lean_ctor_get(v_cancelTk_x3f_1680_, 0);
v___x_1689_ = l_IO_CancelToken_set(v_val_1688_);
goto v___jp_1682_;
}
else
{
goto v___jp_1682_;
}
v___jp_1682_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; size_t v___x_1685_; size_t v___x_1686_; 
lean_inc(v_a_1679_);
v___x_1683_ = l_Lean_Language_SnapshotTask_get___redArg(v_a_1679_);
v___x_1684_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___x_1683_);
lean_dec(v___x_1683_);
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1675_, v___x_1685_);
v_i_1675_ = v___x_1686_;
v_b_1676_ = v___x_1681_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object* v_s_1690_){
_start:
{
lean_object* v_children_1692_; lean_object* v___x_1693_; size_t v_sz_1694_; size_t v___x_1695_; lean_object* v___x_1696_; 
v_children_1692_ = lean_ctor_get(v_s_1690_, 1);
v___x_1693_ = lean_box(0);
v_sz_1694_ = lean_array_size(v_children_1692_);
v___x_1695_ = ((size_t)0ULL);
v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_children_1692_, v_sz_1694_, v___x_1695_, v___x_1693_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object* v_s_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v_s_1697_);
lean_dec_ref(v_s_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object* v_as_1700_, lean_object* v_sz_1701_, lean_object* v_i_1702_, lean_object* v_b_1703_, lean_object* v___y_1704_){
_start:
{
size_t v_sz_boxed_1705_; size_t v_i_boxed_1706_; lean_object* v_res_1707_; 
v_sz_boxed_1705_ = lean_unbox_usize(v_sz_1701_);
lean_dec(v_sz_1701_);
v_i_boxed_1706_ = lean_unbox_usize(v_i_1702_);
lean_dec(v_i_1702_);
v_res_1707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_as_1700_, v_sz_boxed_1705_, v_i_boxed_1706_, v_b_1703_);
lean_dec_ref(v_as_1700_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(lean_object* v_snap_1708_, lean_object* v_m_1709_){
_start:
{
lean_object* v_result_x3f_1710_; 
v_result_x3f_1710_ = lean_ctor_get(v_snap_1708_, 4);
lean_inc(v_result_x3f_1710_);
if (lean_obj_tag(v_result_x3f_1710_) == 1)
{
lean_object* v_val_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1811_; 
v_val_1711_ = lean_ctor_get(v_result_x3f_1710_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_result_x3f_1710_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1713_ = v_result_x3f_1710_;
v_isShared_1714_ = v_isSharedCheck_1811_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_val_1711_);
lean_dec(v_result_x3f_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1811_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_toSnapshot_1715_; lean_object* v_metaSnap_1716_; lean_object* v_ictx_1717_; lean_object* v_stx_1718_; lean_object* v_parserState_1719_; lean_object* v_processedSnap_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1810_; 
v_toSnapshot_1715_ = lean_ctor_get(v_snap_1708_, 0);
v_metaSnap_1716_ = lean_ctor_get(v_snap_1708_, 1);
v_ictx_1717_ = lean_ctor_get(v_snap_1708_, 2);
v_stx_1718_ = lean_ctor_get(v_snap_1708_, 3);
v_parserState_1719_ = lean_ctor_get(v_val_1711_, 0);
v_processedSnap_1720_ = lean_ctor_get(v_val_1711_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_val_1711_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1722_ = v_val_1711_;
v_isShared_1723_ = v_isSharedCheck_1810_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_processedSnap_1720_);
lean_inc(v_parserState_1719_);
lean_dec(v_val_1711_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1810_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v_processed_1724_; lean_object* v_result_x3f_1725_; 
v_processed_1724_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_1720_);
v_result_x3f_1725_ = lean_ctor_get(v_processed_1724_, 2);
lean_inc(v_result_x3f_1725_);
if (lean_obj_tag(v_result_x3f_1725_) == 1)
{
lean_object* v_val_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1809_; 
v_val_1726_ = lean_ctor_get(v_result_x3f_1725_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_result_x3f_1725_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1728_ = v_result_x3f_1725_;
v_isShared_1729_ = v_isSharedCheck_1809_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_val_1726_);
lean_dec(v_result_x3f_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1809_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v_cmdState_1730_; lean_object* v_toSnapshot_1731_; lean_object* v_metaSnap_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1807_; 
v_cmdState_1730_ = lean_ctor_get(v_val_1726_, 0);
lean_inc_ref(v_cmdState_1730_);
v_toSnapshot_1731_ = lean_ctor_get(v_processed_1724_, 0);
v_metaSnap_1732_ = lean_ctor_get(v_processed_1724_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_processed_1724_);
if (v_isSharedCheck_1807_ == 0)
{
lean_object* v_unused_1808_; 
v_unused_1808_ = lean_ctor_get(v_processed_1724_, 2);
lean_dec(v_unused_1808_);
v___x_1734_ = v_processed_1724_;
v_isShared_1735_ = v_isSharedCheck_1807_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_metaSnap_1732_);
lean_inc(v_toSnapshot_1731_);
lean_dec(v_processed_1724_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1807_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_firstCmdSnap_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1805_; 
v_firstCmdSnap_1736_ = lean_ctor_get(v_val_1726_, 1);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_val_1726_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; 
v_unused_1806_ = lean_ctor_get(v_val_1726_, 0);
lean_dec(v_unused_1806_);
v___x_1738_ = v_val_1726_;
v_isShared_1739_ = v_isSharedCheck_1805_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_firstCmdSnap_1736_);
lean_dec(v_val_1726_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1805_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v_env_1740_; lean_object* v_messages_1741_; lean_object* v_scopes_1742_; lean_object* v_usedQuotCtxts_1743_; lean_object* v_nextMacroScope_1744_; lean_object* v_maxRecDepth_1745_; lean_object* v_ngen_1746_; lean_object* v_auxDeclNGen_1747_; lean_object* v_infoState_1748_; lean_object* v_traceState_1749_; lean_object* v_snapshotTasks_1750_; lean_object* v_prevLinterStates_1751_; lean_object* v_codeQualityEntryTasks_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1804_; 
v_env_1740_ = lean_ctor_get(v_cmdState_1730_, 0);
v_messages_1741_ = lean_ctor_get(v_cmdState_1730_, 1);
v_scopes_1742_ = lean_ctor_get(v_cmdState_1730_, 2);
v_usedQuotCtxts_1743_ = lean_ctor_get(v_cmdState_1730_, 3);
v_nextMacroScope_1744_ = lean_ctor_get(v_cmdState_1730_, 4);
v_maxRecDepth_1745_ = lean_ctor_get(v_cmdState_1730_, 5);
v_ngen_1746_ = lean_ctor_get(v_cmdState_1730_, 6);
v_auxDeclNGen_1747_ = lean_ctor_get(v_cmdState_1730_, 7);
v_infoState_1748_ = lean_ctor_get(v_cmdState_1730_, 8);
v_traceState_1749_ = lean_ctor_get(v_cmdState_1730_, 9);
v_snapshotTasks_1750_ = lean_ctor_get(v_cmdState_1730_, 10);
v_prevLinterStates_1751_ = lean_ctor_get(v_cmdState_1730_, 11);
v_codeQualityEntryTasks_1752_ = lean_ctor_get(v_cmdState_1730_, 12);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_cmdState_1730_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1754_ = v_cmdState_1730_;
v_isShared_1755_ = v_isSharedCheck_1804_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1752_);
lean_inc(v_prevLinterStates_1751_);
lean_inc(v_snapshotTasks_1750_);
lean_inc(v_traceState_1749_);
lean_inc(v_infoState_1748_);
lean_inc(v_auxDeclNGen_1747_);
lean_inc(v_ngen_1746_);
lean_inc(v_maxRecDepth_1745_);
lean_inc(v_nextMacroScope_1744_);
lean_inc(v_usedQuotCtxts_1743_);
lean_inc(v_scopes_1742_);
lean_inc(v_messages_1741_);
lean_inc(v_env_1740_);
lean_dec(v_cmdState_1730_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1804_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v_mainModule_1757_; uint8_t v___x_1758_; 
v___x_1756_ = l_Lean_Environment_header(v_env_1740_);
v_mainModule_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_mainModule_1757_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = lean_name_eq(v_mainModule_1757_, v_m_1709_);
lean_dec(v_mainModule_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1798_; 
lean_inc(v_stx_1718_);
lean_inc_ref(v_ictx_1717_);
lean_inc_ref(v_metaSnap_1716_);
lean_inc_ref(v_toSnapshot_1715_);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_snap_1708_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; lean_object* v_unused_1800_; lean_object* v_unused_1801_; lean_object* v_unused_1802_; lean_object* v_unused_1803_; 
v_unused_1799_ = lean_ctor_get(v_snap_1708_, 4);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v_snap_1708_, 3);
lean_dec(v_unused_1800_);
v_unused_1801_ = lean_ctor_get(v_snap_1708_, 2);
lean_dec(v_unused_1801_);
v_unused_1802_ = lean_ctor_get(v_snap_1708_, 1);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_snap_1708_, 0);
lean_dec(v_unused_1803_);
v___x_1760_ = v_snap_1708_;
v_isShared_1761_ = v_isSharedCheck_1798_;
goto v_resetjp_1759_;
}
else
{
lean_dec(v_snap_1708_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1798_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_idx_1762_; lean_object* v_parentIdxs_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1796_; 
v_idx_1762_ = lean_ctor_get(v_auxDeclNGen_1747_, 1);
v_parentIdxs_1763_ = lean_ctor_get(v_auxDeclNGen_1747_, 2);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_auxDeclNGen_1747_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; 
v_unused_1797_ = lean_ctor_get(v_auxDeclNGen_1747_, 0);
lean_dec(v_unused_1797_);
v___x_1765_ = v_auxDeclNGen_1747_;
v_isShared_1766_ = v_isSharedCheck_1796_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_parentIdxs_1763_);
lean_inc(v_idx_1762_);
lean_dec(v_auxDeclNGen_1747_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1796_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v_newEnv_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v_newEnv_1767_ = l_Lean_Environment_setMainModule(v_env_1740_, v_m_1709_);
v___x_1768_ = lean_box(0);
v___x_1769_ = l_Lean_mkPrivateName(v_newEnv_1767_, v___x_1768_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1769_);
v___x_1771_ = v___x_1765_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_idx_1762_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v_parentIdxs_1763_);
v___x_1771_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v_newCmdState_1773_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 7, v___x_1771_);
lean_ctor_set(v___x_1754_, 0, v_newEnv_1767_);
v_newCmdState_1773_ = v___x_1754_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_newEnv_1767_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_messages_1741_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_scopes_1742_);
lean_ctor_set(v_reuseFailAlloc_1794_, 3, v_usedQuotCtxts_1743_);
lean_ctor_set(v_reuseFailAlloc_1794_, 4, v_nextMacroScope_1744_);
lean_ctor_set(v_reuseFailAlloc_1794_, 5, v_maxRecDepth_1745_);
lean_ctor_set(v_reuseFailAlloc_1794_, 6, v_ngen_1746_);
lean_ctor_set(v_reuseFailAlloc_1794_, 7, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1794_, 8, v_infoState_1748_);
lean_ctor_set(v_reuseFailAlloc_1794_, 9, v_traceState_1749_);
lean_ctor_set(v_reuseFailAlloc_1794_, 10, v_snapshotTasks_1750_);
lean_ctor_set(v_reuseFailAlloc_1794_, 11, v_prevLinterStates_1751_);
lean_ctor_set(v_reuseFailAlloc_1794_, 12, v_codeQualityEntryTasks_1752_);
v_newCmdState_1773_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1775_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v_newCmdState_1773_);
v___x_1775_ = v___x_1738_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_newCmdState_1773_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_firstCmdSnap_1736_);
v___x_1775_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1775_);
v___x_1777_ = v___x_1728_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v_newProcessed_1779_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 2, v___x_1777_);
v_newProcessed_1779_ = v___x_1734_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_toSnapshot_1731_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_metaSnap_1732_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v___x_1777_);
v_newProcessed_1779_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1783_; 
v___x_1780_ = lean_box(0);
v___x_1781_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1780_, v_newProcessed_1779_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 1, v___x_1781_);
v___x_1783_ = v___x_1722_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_parserState_1719_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1785_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1783_);
v___x_1785_ = v___x_1713_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1787_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 4, v___x_1785_);
v___x_1787_ = v___x_1760_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_toSnapshot_1715_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_metaSnap_1716_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_ictx_1717_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v_stx_1718_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
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
lean_del_object(v___x_1754_);
lean_dec_ref(v_codeQualityEntryTasks_1752_);
lean_dec(v_prevLinterStates_1751_);
lean_dec_ref(v_snapshotTasks_1750_);
lean_dec_ref(v_traceState_1749_);
lean_dec_ref(v_infoState_1748_);
lean_dec_ref(v_auxDeclNGen_1747_);
lean_dec_ref(v_ngen_1746_);
lean_dec(v_maxRecDepth_1745_);
lean_dec(v_nextMacroScope_1744_);
lean_dec(v_usedQuotCtxts_1743_);
lean_dec(v_scopes_1742_);
lean_dec_ref(v_messages_1741_);
lean_dec_ref(v_env_1740_);
lean_del_object(v___x_1738_);
lean_dec_ref(v_firstCmdSnap_1736_);
lean_del_object(v___x_1734_);
lean_dec_ref(v_metaSnap_1732_);
lean_dec_ref(v_toSnapshot_1731_);
lean_del_object(v___x_1728_);
lean_del_object(v___x_1722_);
lean_dec_ref(v_parserState_1719_);
lean_del_object(v___x_1713_);
lean_dec(v_m_1709_);
return v_snap_1708_;
}
}
}
}
}
}
else
{
lean_dec(v_result_x3f_1725_);
lean_dec(v_processed_1724_);
lean_del_object(v___x_1722_);
lean_dec_ref(v_parserState_1719_);
lean_del_object(v___x_1713_);
lean_dec(v_m_1709_);
return v_snap_1708_;
}
}
}
}
else
{
lean_dec(v_result_x3f_1710_);
lean_dec(v_m_1709_);
return v_snap_1708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object* v_incrFile_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_incrFile_1812_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object* v_incrFile_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(v_incrFile_1815_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object* v_opts_1818_, lean_object* v_incr_1819_, lean_object* v_res_1820_){
_start:
{
lean_object* v_cmdState_1822_; lean_object* v_env_1823_; lean_object* v_initModIdxs_1824_; lean_object* v___x_1825_; 
v_cmdState_1822_ = lean_ctor_get(v_res_1820_, 0);
lean_inc_ref(v_cmdState_1822_);
lean_dec_ref(v_res_1820_);
v_env_1823_ = lean_ctor_get(v_cmdState_1822_, 0);
lean_inc_ref(v_env_1823_);
lean_dec_ref(v_cmdState_1822_);
v_initModIdxs_1824_ = lean_ctor_get(v_incr_1819_, 1);
v___x_1825_ = l_Lean_runInitAttrsForModules(v_env_1823_, v_initModIdxs_1824_, v_opts_1818_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object* v_opts_1826_, lean_object* v_incr_1827_, lean_object* v_res_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(v_opts_1826_, v_incr_1827_, v_res_1828_);
lean_dec_ref(v_incr_1827_);
lean_dec_ref(v_opts_1826_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7(){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = lean_enable_initializer_execution();
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(lean_object* v_env_1838_, lean_object* v_incrFile_1839_, lean_object* v_toSave_1840_){
_start:
{
lean_object* v___x_1842_; lean_object* v_regions_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; 
v___x_1842_ = l_Lean_Environment_header(v_env_1838_);
v_regions_1843_ = lean_ctor_get(v___x_1842_, 2);
lean_inc_ref(v_regions_1843_);
lean_dec_ref(v___x_1842_);
v___x_1844_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1845_ = lean_box(0);
v___x_1846_ = 1;
v___x_1847_ = lean_compacted_region_save(v_incrFile_1839_, v___x_1844_, v_toSave_1840_, v_regions_1843_, v___x_1845_, v___x_1846_);
lean_dec_ref(v_regions_1843_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___boxed(lean_object* v_env_1848_, lean_object* v_incrFile_1849_, lean_object* v_toSave_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(v_env_1848_, v_incrFile_1849_, v_toSave_1850_);
lean_dec_ref(v_toSave_1850_);
lean_dec_ref(v_incrFile_1849_);
lean_dec_ref(v_env_1848_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_opts_1853_, lean_object* v_opt_1854_){
_start:
{
lean_object* v_name_1855_; lean_object* v_map_1856_; lean_object* v___x_1857_; 
v_name_1855_ = lean_ctor_get(v_opt_1854_, 0);
v_map_1856_ = lean_ctor_get(v_opts_1853_, 0);
v___x_1857_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1856_, v_name_1855_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_box(0);
return v___x_1858_;
}
else
{
lean_object* v_val_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1868_; 
v_val_1859_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1861_ = v___x_1857_;
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_val_1859_);
lean_dec(v___x_1857_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1868_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
if (lean_obj_tag(v_val_1859_) == 0)
{
lean_object* v_v_1863_; lean_object* v___x_1865_; 
v_v_1863_ = lean_ctor_get(v_val_1859_, 0);
lean_inc_ref(v_v_1863_);
lean_dec_ref_known(v_val_1859_, 1);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v_v_1863_);
v___x_1865_ = v___x_1861_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_v_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
else
{
lean_object* v___x_1867_; 
lean_del_object(v___x_1861_);
lean_dec(v_val_1859_);
v___x_1867_ = lean_box(0);
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_opts_1869_, lean_object* v_opt_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v_opts_1869_, v_opt_1870_);
lean_dec_ref(v_opt_1870_);
lean_dec_ref(v_opts_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_opts_1872_, lean_object* v_opt_1873_){
_start:
{
lean_object* v_name_1874_; lean_object* v_defValue_1875_; lean_object* v_map_1876_; lean_object* v___x_1877_; 
v_name_1874_ = lean_ctor_get(v_opt_1873_, 0);
v_defValue_1875_ = lean_ctor_get(v_opt_1873_, 1);
v_map_1876_ = lean_ctor_get(v_opts_1872_, 0);
v___x_1877_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1876_, v_name_1874_);
if (lean_obj_tag(v___x_1877_) == 0)
{
uint8_t v___x_1878_; 
v___x_1878_ = lean_unbox(v_defValue_1875_);
return v___x_1878_;
}
else
{
lean_object* v_val_1879_; 
v_val_1879_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_val_1879_);
lean_dec_ref_known(v___x_1877_, 1);
if (lean_obj_tag(v_val_1879_) == 1)
{
uint8_t v_v_1880_; 
v_v_1880_ = lean_ctor_get_uint8(v_val_1879_, 0);
lean_dec_ref_known(v_val_1879_, 0);
return v_v_1880_;
}
else
{
uint8_t v___x_1881_; 
lean_dec(v_val_1879_);
v___x_1881_ = lean_unbox(v_defValue_1875_);
return v___x_1881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_opts_1882_, lean_object* v_opt_1883_){
_start:
{
uint8_t v_res_1884_; lean_object* v_r_1885_; 
v_res_1884_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1882_, v_opt_1883_);
lean_dec_ref(v_opt_1883_);
lean_dec_ref(v_opts_1882_);
v_r_1885_ = lean_box(v_res_1884_);
return v_r_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_hOpt_1888_){
_start:
{
lean_inc_ref(v_hOpt_1888_);
return v_hOpt_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_hOpt_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_Elab_runFrontend___lam__0(v_x_1889_, v_x_1890_, v_hOpt_1891_);
lean_dec_ref(v_hOpt_1891_);
lean_dec_ref(v_x_1890_);
lean_dec(v_x_1889_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_x1_1893_, lean_object* v_x2_1894_){
_start:
{
lean_object* v_elabSnap_1895_; lean_object* v_resultSnap_1896_; lean_object* v___x_1897_; lean_object* v_codeQualityEntryTasks_1898_; lean_object* v___x_1899_; 
v_elabSnap_1895_ = lean_ctor_get(v_x2_1894_, 3);
lean_inc_ref(v_elabSnap_1895_);
lean_dec_ref(v_x2_1894_);
v_resultSnap_1896_ = lean_ctor_get(v_elabSnap_1895_, 2);
lean_inc_ref(v_resultSnap_1896_);
lean_dec_ref(v_elabSnap_1895_);
v___x_1897_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_1896_);
v_codeQualityEntryTasks_1898_ = lean_ctor_get(v___x_1897_, 2);
lean_inc_ref(v_codeQualityEntryTasks_1898_);
lean_dec(v___x_1897_);
v___x_1899_ = l_Array_append___redArg(v_x1_1893_, v_codeQualityEntryTasks_1898_);
lean_dec_ref(v_codeQualityEntryTasks_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(size_t v_sz_1900_, size_t v_i_1901_, lean_object* v_bs_1902_){
_start:
{
uint8_t v___x_1903_; 
v___x_1903_ = lean_usize_dec_lt(v_i_1901_, v_sz_1900_);
if (v___x_1903_ == 0)
{
return v_bs_1902_;
}
else
{
lean_object* v_v_1904_; lean_object* v___x_1905_; lean_object* v_bs_x27_1906_; lean_object* v___x_1907_; size_t v___x_1908_; size_t v___x_1909_; lean_object* v___x_1910_; 
v_v_1904_ = lean_array_uget(v_bs_1902_, v_i_1901_);
v___x_1905_ = lean_unsigned_to_nat(0u);
v_bs_x27_1906_ = lean_array_uset(v_bs_1902_, v_i_1901_, v___x_1905_);
v___x_1907_ = l_Lean_instToJsonModuleArtifacts_toJson(v_v_1904_);
v___x_1908_ = ((size_t)1ULL);
v___x_1909_ = lean_usize_add(v_i_1901_, v___x_1908_);
v___x_1910_ = lean_array_uset(v_bs_x27_1906_, v_i_1901_, v___x_1907_);
v_i_1901_ = v___x_1909_;
v_bs_1902_ = v___x_1910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11___boxed(lean_object* v_sz_1912_, lean_object* v_i_1913_, lean_object* v_bs_1914_){
_start:
{
size_t v_sz_boxed_1915_; size_t v_i_boxed_1916_; lean_object* v_res_1917_; 
v_sz_boxed_1915_ = lean_unbox_usize(v_sz_1912_);
lean_dec(v_sz_1912_);
v_i_boxed_1916_ = lean_unbox_usize(v_i_1913_);
lean_dec(v_i_1913_);
v_res_1917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(v_sz_boxed_1915_, v_i_boxed_1916_, v_bs_1914_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8(lean_object* v_a_1918_){
_start:
{
size_t v_sz_1919_; size_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_sz_1919_ = lean_array_size(v_a_1918_);
v___x_1920_ = ((size_t)0ULL);
v___x_1921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(v_sz_1919_, v___x_1920_, v_a_1918_);
v___x_1922_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_a_1923_, uint8_t v___x_1924_, lean_object* v_incrFile_1925_, lean_object* v_snapToSave_1926_){
_start:
{
lean_object* v___x_1928_; lean_object* v_regions_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1928_ = l_Lean_Environment_header(v_a_1923_);
v_regions_1929_ = lean_ctor_get(v___x_1928_, 2);
lean_inc_ref(v_regions_1929_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = l_Lean_getRegularInitAttrModIdxs(v_a_1923_);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v_snapToSave_1926_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_compacted_region_save(v_incrFile_1925_, v___x_1932_, v___x_1931_, v_regions_1929_, v___x_1933_, v___x_1924_);
lean_dec_ref_known(v___x_1931_, 2);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1936_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1929_);
lean_dec_ref(v_regions_1929_);
v___x_1937_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
v___x_1938_ = l_System_FilePath_addExtension(v_incrFile_1925_, v___x_1937_);
v___x_1939_ = l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8(v___x_1936_);
v___x_1940_ = l_Lean_Json_compress(v___x_1939_);
v___x_1941_ = l_IO_FS_writeFile(v___x_1938_, v___x_1940_);
lean_dec_ref(v___x_1940_);
lean_dec_ref(v___x_1938_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1949_; 
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v___x_1941_, 0);
lean_dec(v_unused_1950_);
v___x_1943_ = v___x_1941_;
v_isShared_1944_ = v_isSharedCheck_1949_;
goto v_resetjp_1942_;
}
else
{
lean_dec(v___x_1941_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1949_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1945_ = lean_runtime_forget(v_a_1935_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1945_);
v___x_1947_ = v___x_1943_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
else
{
lean_dec(v_a_1935_);
return v___x_1941_;
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref(v_regions_1929_);
lean_dec_ref(v_incrFile_1925_);
v_a_1951_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1934_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1934_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object* v_a_1959_, lean_object* v___x_1960_, lean_object* v_incrFile_1961_, lean_object* v_snapToSave_1962_, lean_object* v___y_1963_){
_start:
{
uint8_t v___x_6105__boxed_1964_; lean_object* v_res_1965_; 
v___x_6105__boxed_1964_ = lean_unbox(v___x_1960_);
v_res_1965_ = l_Lean_Elab_runFrontend___lam__2(v_a_1959_, v___x_6105__boxed_1964_, v_incrFile_1961_, v_snapToSave_1962_);
lean_dec_ref(v_a_1959_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_fileMap_1966_, lean_object* v_a_1967_, lean_object* v___x_1968_, lean_object* v_opts_1969_, lean_object* v_val_1970_, uint8_t v___x_1971_, uint8_t v_a_1972_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1974_ = l_Lean_Linter_recordLints(v_fileMap_1966_, v_a_1967_, v___x_1968_);
v___x_1975_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1976_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1969_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_writeModule(v___x_1974_, v_val_1970_, v___x_1971_);
return v___x_1977_;
}
else
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_writeModule(v___x_1974_, v_val_1970_, v_a_1972_);
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_fileMap_1979_, lean_object* v_a_1980_, lean_object* v___x_1981_, lean_object* v_opts_1982_, lean_object* v_val_1983_, lean_object* v___x_1984_, lean_object* v_a_1985_, lean_object* v___y_1986_){
_start:
{
uint8_t v___x_6179__boxed_1987_; uint8_t v_a_6180__boxed_1988_; lean_object* v_res_1989_; 
v___x_6179__boxed_1987_ = lean_unbox(v___x_1984_);
v_a_6180__boxed_1988_ = lean_unbox(v_a_1985_);
v_res_1989_ = l_Lean_Elab_runFrontend___lam__3(v_fileMap_1979_, v_a_1980_, v___x_1981_, v_opts_1982_, v_val_1983_, v___x_6179__boxed_1987_, v_a_6180__boxed_1988_);
lean_dec_ref(v_opts_1982_);
lean_dec_ref(v___x_1981_);
lean_dec_ref(v_fileMap_1979_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_1990_, size_t v_i_1991_, size_t v_stop_1992_, lean_object* v_b_1993_){
_start:
{
uint8_t v___x_1995_; 
v___x_1995_ = lean_usize_dec_eq(v_i_1991_, v_stop_1992_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_array_uget_borrowed(v_as_1990_, v_i_1991_);
lean_inc(v___x_1996_);
v___x_1997_ = lean_load_dynlib(v___x_1996_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; size_t v___x_1999_; size_t v___x_2000_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_1999_ = ((size_t)1ULL);
v___x_2000_ = lean_usize_add(v_i_1991_, v___x_1999_);
v_i_1991_ = v___x_2000_;
v_b_1993_ = v_a_1998_;
goto _start;
}
else
{
return v___x_1997_;
}
}
else
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v_b_1993_);
return v___x_2002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_2003_, lean_object* v_i_2004_, lean_object* v_stop_2005_, lean_object* v_b_2006_, lean_object* v___y_2007_){
_start:
{
size_t v_i_boxed_2008_; size_t v_stop_boxed_2009_; lean_object* v_res_2010_; 
v_i_boxed_2008_ = lean_unbox_usize(v_i_2004_);
lean_dec(v_i_2004_);
v_stop_boxed_2009_ = lean_unbox_usize(v_stop_2005_);
lean_dec(v_stop_2005_);
v_res_2010_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_2003_, v_i_boxed_2008_, v_stop_boxed_2009_, v_b_2006_);
lean_dec_ref(v_as_2003_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* v_setup_x3f_2011_, lean_object* v___f_2012_, lean_object* v___x_2013_, lean_object* v_plugins_2014_, uint32_t v_trustLevel_2015_, uint8_t v___x_2016_, lean_object* v_mainModuleName_2017_, lean_object* v_stx_2018_, lean_object* v___y_2019_){
_start:
{
uint8_t v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; 
if (lean_obj_tag(v_setup_x3f_2011_) == 1)
{
lean_object* v_val_2035_; lean_object* v_name_2036_; lean_object* v_package_x3f_2037_; uint8_t v_isModule_2038_; lean_object* v_imports_x3f_2039_; lean_object* v_importArts_2040_; lean_object* v_dynlibs_2041_; lean_object* v_plugins_2042_; lean_object* v_options_2043_; lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
lean_dec(v_mainModuleName_2017_);
v_val_2035_ = lean_ctor_get(v_setup_x3f_2011_, 0);
lean_inc(v_val_2035_);
lean_dec_ref_known(v_setup_x3f_2011_, 1);
v_name_2036_ = lean_ctor_get(v_val_2035_, 0);
lean_inc(v_name_2036_);
v_package_x3f_2037_ = lean_ctor_get(v_val_2035_, 1);
lean_inc(v_package_x3f_2037_);
v_isModule_2038_ = lean_ctor_get_uint8(v_val_2035_, sizeof(void*)*7);
v_imports_x3f_2039_ = lean_ctor_get(v_val_2035_, 2);
lean_inc(v_imports_x3f_2039_);
v_importArts_2040_ = lean_ctor_get(v_val_2035_, 3);
lean_inc(v_importArts_2040_);
v_dynlibs_2041_ = lean_ctor_get(v_val_2035_, 4);
lean_inc_ref(v_dynlibs_2041_);
v_plugins_2042_ = lean_ctor_get(v_val_2035_, 5);
lean_inc_ref(v_plugins_2042_);
v_options_2043_ = lean_ctor_get(v_val_2035_, 6);
lean_inc(v_options_2043_);
lean_dec(v_val_2035_);
v___x_2049_ = lean_unsigned_to_nat(0u);
v___x_2050_ = lean_array_get_size(v_dynlibs_2041_);
v___x_2051_ = lean_nat_dec_lt(v___x_2049_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_dec_ref(v_dynlibs_2041_);
goto v___jp_2044_;
}
else
{
lean_object* v___x_2052_; size_t v___x_2053_; size_t v___x_2054_; lean_object* v___x_2055_; 
v___x_2052_ = lean_box(0);
v___x_2053_ = ((size_t)0ULL);
v___x_2054_ = lean_usize_of_nat(v___x_2050_);
v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2041_, v___x_2053_, v___x_2054_, v___x_2052_);
lean_dec_ref(v_dynlibs_2041_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_dec_ref_known(v___x_2055_, 1);
goto v___jp_2044_;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_options_2043_);
lean_dec_ref(v_plugins_2042_);
lean_dec(v_importArts_2040_);
lean_dec(v_imports_x3f_2039_);
lean_dec(v_package_x3f_2037_);
lean_dec(v_name_2036_);
lean_dec(v_stx_2018_);
lean_dec_ref(v_plugins_2014_);
lean_dec_ref(v___x_2013_);
lean_dec_ref(v___f_2012_);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
v___jp_2044_:
{
uint8_t v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2018_);
v___x_2046_ = lean_strict_or(v_isModule_2038_, v___x_2045_);
if (lean_obj_tag(v_imports_x3f_2039_) == 0)
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2018_, v___x_2016_);
v___y_2022_ = v___x_2046_;
v___y_2023_ = v_plugins_2042_;
v___y_2024_ = v_name_2036_;
v___y_2025_ = v_options_2043_;
v___y_2026_ = v_importArts_2040_;
v___y_2027_ = v_package_x3f_2037_;
v___y_2028_ = v___x_2047_;
goto v___jp_2021_;
}
else
{
lean_object* v_val_2048_; 
lean_dec(v_stx_2018_);
v_val_2048_ = lean_ctor_get(v_imports_x3f_2039_, 0);
lean_inc(v_val_2048_);
lean_dec_ref_known(v_imports_x3f_2039_, 1);
v___y_2022_ = v___x_2046_;
v___y_2023_ = v_plugins_2042_;
v___y_2024_ = v_name_2036_;
v___y_2025_ = v_options_2043_;
v___y_2026_ = v_importArts_2040_;
v___y_2027_ = v_package_x3f_2037_;
v___y_2028_ = v_val_2048_;
goto v___jp_2021_;
}
}
}
else
{
lean_object* v___x_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_dec_ref(v___f_2012_);
lean_dec(v_setup_x3f_2011_);
v___x_2064_ = lean_box(0);
v___x_2065_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2018_);
v___x_2066_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2018_, v___x_2016_);
v___x_2067_ = lean_box(1);
v___x_2068_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2068_, 0, v_mainModuleName_2017_);
lean_ctor_set(v___x_2068_, 1, v___x_2064_);
lean_ctor_set(v___x_2068_, 2, v___x_2066_);
lean_ctor_set(v___x_2068_, 3, v___x_2013_);
lean_ctor_set(v___x_2068_, 4, v___x_2067_);
lean_ctor_set(v___x_2068_, 5, v_plugins_2014_);
lean_ctor_set_uint8(v___x_2068_, sizeof(void*)*6 + 4, v___x_2065_);
lean_ctor_set_uint32(v___x_2068_, sizeof(void*)*6, v_trustLevel_2015_);
v___x_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
v___jp_2021_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2029_ = l_Lean_LeanOptions_toOptions(v___y_2025_);
v___x_2030_ = l_Lean_Options_mergeBy(v___f_2012_, v___x_2013_, v___x_2029_);
v___x_2031_ = l_Array_append___redArg(v_plugins_2014_, v___y_2023_);
lean_dec_ref(v___y_2023_);
v___x_2032_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2032_, 0, v___y_2024_);
lean_ctor_set(v___x_2032_, 1, v___y_2027_);
lean_ctor_set(v___x_2032_, 2, v___y_2028_);
lean_ctor_set(v___x_2032_, 3, v___x_2030_);
lean_ctor_set(v___x_2032_, 4, v___y_2026_);
lean_ctor_set(v___x_2032_, 5, v___x_2031_);
lean_ctor_set_uint8(v___x_2032_, sizeof(void*)*6 + 4, v___y_2022_);
lean_ctor_set_uint32(v___x_2032_, sizeof(void*)*6, v_trustLevel_2015_);
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object* v_setup_x3f_2071_, lean_object* v___f_2072_, lean_object* v___x_2073_, lean_object* v_plugins_2074_, lean_object* v_trustLevel_2075_, lean_object* v___x_2076_, lean_object* v_mainModuleName_2077_, lean_object* v_stx_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
uint32_t v_trustLevel_boxed_2081_; uint8_t v___x_6226__boxed_2082_; lean_object* v_res_2083_; 
v_trustLevel_boxed_2081_ = lean_unbox_uint32(v_trustLevel_2075_);
lean_dec(v_trustLevel_2075_);
v___x_6226__boxed_2082_ = lean_unbox(v___x_2076_);
v_res_2083_ = l_Lean_Elab_runFrontend___lam__4(v_setup_x3f_2071_, v___f_2072_, v___x_2073_, v_plugins_2074_, v_trustLevel_boxed_2081_, v___x_6226__boxed_2082_, v_mainModuleName_2077_, v_stx_2078_, v___y_2079_);
lean_dec_ref(v___y_2079_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object* v_val_2084_, lean_object* v_initModIdxs_2085_, lean_object* v___x_2086_){
_start:
{
lean_object* v_cmdState_2088_; lean_object* v_env_2089_; lean_object* v___x_2090_; 
v_cmdState_2088_ = lean_ctor_get(v_val_2084_, 0);
lean_inc_ref(v_cmdState_2088_);
lean_dec_ref(v_val_2084_);
v_env_2089_ = lean_ctor_get(v_cmdState_2088_, 0);
lean_inc_ref(v_env_2089_);
lean_dec_ref(v_cmdState_2088_);
v___x_2090_ = l_Lean_runInitAttrsForModules(v_env_2089_, v_initModIdxs_2085_, v___x_2086_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5___boxed(lean_object* v_val_2091_, lean_object* v_initModIdxs_2092_, lean_object* v___x_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Elab_runFrontend___lam__5(v_val_2091_, v_initModIdxs_2092_, v___x_2093_);
lean_dec_ref(v___x_2093_);
lean_dec_ref(v_initModIdxs_2092_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(size_t v_sz_2096_, size_t v_i_2097_, lean_object* v_bs_2098_){
_start:
{
uint8_t v___x_2099_; 
v___x_2099_ = lean_usize_dec_lt(v_i_2097_, v_sz_2096_);
if (v___x_2099_ == 0)
{
return v_bs_2098_;
}
else
{
lean_object* v_v_2100_; lean_object* v_traces_2101_; lean_object* v___x_2102_; lean_object* v_bs_x27_2103_; size_t v___x_2104_; size_t v___x_2105_; lean_object* v___x_2106_; 
v_v_2100_ = lean_array_uget_borrowed(v_bs_2098_, v_i_2097_);
v_traces_2101_ = lean_ctor_get(v_v_2100_, 3);
lean_inc_ref(v_traces_2101_);
v___x_2102_ = lean_unsigned_to_nat(0u);
v_bs_x27_2103_ = lean_array_uset(v_bs_2098_, v_i_2097_, v___x_2102_);
v___x_2104_ = ((size_t)1ULL);
v___x_2105_ = lean_usize_add(v_i_2097_, v___x_2104_);
v___x_2106_ = lean_array_uset(v_bs_x27_2103_, v_i_2097_, v_traces_2101_);
v_i_2097_ = v___x_2105_;
v_bs_2098_ = v___x_2106_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_sz_2108_, lean_object* v_i_2109_, lean_object* v_bs_2110_){
_start:
{
size_t v_sz_boxed_2111_; size_t v_i_boxed_2112_; lean_object* v_res_2113_; 
v_sz_boxed_2111_ = lean_unbox_usize(v_sz_2108_);
lean_dec(v_sz_2108_);
v_i_boxed_2112_ = lean_unbox_usize(v_i_2109_);
lean_dec(v_i_2109_);
v_res_2113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_boxed_2111_, v_i_boxed_2112_, v_bs_2110_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_2114_, size_t v_i_2115_, size_t v_stop_2116_, lean_object* v_b_2117_){
_start:
{
lean_object* v___y_2119_; uint8_t v___x_2123_; 
v___x_2123_ = lean_usize_dec_eq(v_i_2115_, v_stop_2116_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v_infoTree_x3f_2125_; 
v___x_2124_ = lean_array_uget_borrowed(v_as_2114_, v_i_2115_);
v_infoTree_x3f_2125_ = lean_ctor_get(v___x_2124_, 2);
if (lean_obj_tag(v_infoTree_x3f_2125_) == 1)
{
lean_object* v_val_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_val_2126_ = lean_ctor_get(v_infoTree_x3f_2125_, 0);
v___x_2127_ = lean_unsigned_to_nat(1u);
v___x_2128_ = lean_mk_empty_array_with_capacity(v___x_2127_);
lean_inc(v_val_2126_);
v___x_2129_ = lean_array_push(v___x_2128_, v_val_2126_);
v___x_2130_ = l_Array_append___redArg(v_b_2117_, v___x_2129_);
lean_dec_ref(v___x_2129_);
v___y_2119_ = v___x_2130_;
goto v___jp_2118_;
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_2132_ = l_Array_append___redArg(v_b_2117_, v___x_2131_);
v___y_2119_ = v___x_2132_;
goto v___jp_2118_;
}
}
else
{
return v_b_2117_;
}
v___jp_2118_:
{
size_t v___x_2120_; size_t v___x_2121_; 
v___x_2120_ = ((size_t)1ULL);
v___x_2121_ = lean_usize_add(v_i_2115_, v___x_2120_);
v_i_2115_ = v___x_2121_;
v_b_2117_ = v___y_2119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_2133_, lean_object* v_i_2134_, lean_object* v_stop_2135_, lean_object* v_b_2136_){
_start:
{
size_t v_i_boxed_2137_; size_t v_stop_boxed_2138_; lean_object* v_res_2139_; 
v_i_boxed_2137_ = lean_unbox_usize(v_i_2134_);
lean_dec(v_i_2134_);
v_stop_boxed_2138_ = lean_unbox_usize(v_stop_2135_);
lean_dec(v_stop_2135_);
v_res_2139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_2133_, v_i_boxed_2137_, v_stop_boxed_2138_, v_b_2136_);
lean_dec_ref(v_as_2133_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(lean_object* v_as_2140_, size_t v_i_2141_, size_t v_stop_2142_, lean_object* v_b_2143_){
_start:
{
uint8_t v___x_2144_; 
v___x_2144_ = lean_usize_dec_eq(v_i_2141_, v_stop_2142_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; size_t v___x_2149_; size_t v___x_2150_; 
v___x_2145_ = lean_array_uget_borrowed(v_as_2140_, v_i_2141_);
v___x_2146_ = 2;
v___x_2147_ = lean_box(v___x_2146_);
lean_inc(v___x_2145_);
v___x_2148_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2145_, v___x_2147_, v_b_2143_);
v___x_2149_ = ((size_t)1ULL);
v___x_2150_ = lean_usize_add(v_i_2141_, v___x_2149_);
v_i_2141_ = v___x_2150_;
v_b_2143_ = v___x_2148_;
goto _start;
}
else
{
return v_b_2143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9___boxed(lean_object* v_as_2152_, lean_object* v_i_2153_, lean_object* v_stop_2154_, lean_object* v_b_2155_){
_start:
{
size_t v_i_boxed_2156_; size_t v_stop_boxed_2157_; lean_object* v_res_2158_; 
v_i_boxed_2156_ = lean_unbox_usize(v_i_2153_);
lean_dec(v_i_2153_);
v_stop_boxed_2157_ = lean_unbox_usize(v_stop_2154_);
lean_dec(v_stop_2154_);
v_res_2158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_as_2152_, v_i_boxed_2156_, v_stop_boxed_2157_, v_b_2155_);
lean_dec_ref(v_as_2152_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_2162_, lean_object* v_k_2163_, uint8_t v_v_2164_){
_start:
{
lean_object* v_map_2165_; uint8_t v_hasTrace_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2180_; 
v_map_2165_ = lean_ctor_get(v_o_2162_, 0);
v_hasTrace_2166_ = lean_ctor_get_uint8(v_o_2162_, sizeof(void*)*1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_o_2162_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2168_ = v_o_2162_;
v_isShared_2169_ = v_isSharedCheck_2180_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_map_2165_);
lean_dec(v_o_2162_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2180_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2170_, 0, v_v_2164_);
lean_inc(v_k_2163_);
v___x_2171_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2163_, v___x_2170_, v_map_2165_);
if (v_hasTrace_2166_ == 0)
{
lean_object* v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2175_; 
v___x_2172_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_2173_ = l_Lean_Name_isPrefixOf(v___x_2172_, v_k_2163_);
lean_dec(v_k_2163_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2171_);
v___x_2175_ = v___x_2168_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2171_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_ctor_set_uint8(v___x_2175_, sizeof(void*)*1, v___x_2173_);
return v___x_2175_;
}
}
else
{
lean_object* v___x_2178_; 
lean_dec(v_k_2163_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2171_);
v___x_2178_ = v___x_2168_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2179_, sizeof(void*)*1, v_hasTrace_2166_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_2181_, lean_object* v_k_2182_, lean_object* v_v_2183_){
_start:
{
uint8_t v_v_boxed_2184_; lean_object* v_res_2185_; 
v_v_boxed_2184_ = lean_unbox(v_v_2183_);
v_res_2185_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2181_, v_k_2182_, v_v_boxed_2184_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_2186_, lean_object* v_opt_2187_, uint8_t v_val_2188_){
_start:
{
lean_object* v_name_2189_; lean_object* v___x_2190_; 
v_name_2189_ = lean_ctor_get(v_opt_2187_, 0);
lean_inc(v_name_2189_);
lean_dec_ref(v_opt_2187_);
v___x_2190_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_2186_, v_name_2189_, v_val_2188_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_2191_, lean_object* v_opt_2192_, lean_object* v_val_2193_){
_start:
{
uint8_t v_val_boxed_2194_; lean_object* v_res_2195_; 
v_val_boxed_2194_ = lean_unbox(v_val_2193_);
v_res_2195_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2191_, v_opt_2192_, v_val_boxed_2194_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_2196_, lean_object* v_opt_2197_, uint8_t v_val_2198_){
_start:
{
lean_object* v_name_2199_; lean_object* v_map_2200_; uint8_t v___x_2201_; 
v_name_2199_ = lean_ctor_get(v_opt_2197_, 0);
v_map_2200_ = lean_ctor_get(v_opts_2196_, 0);
v___x_2201_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_2199_, v_map_2200_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2196_, v_opt_2197_, v_val_2198_);
return v___x_2202_;
}
else
{
lean_dec_ref(v_opt_2197_);
return v_opts_2196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_2203_, lean_object* v_opt_2204_, lean_object* v_val_2205_){
_start:
{
uint8_t v_val_boxed_2206_; lean_object* v_res_2207_; 
v_val_boxed_2206_ = lean_unbox(v_val_2205_);
v_res_2207_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2203_, v_opt_2204_, v_val_boxed_2206_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0(lean_object* v_a_2208_, lean_object* v_ps_2209_){
_start:
{
lean_object* v_importedEntries_2210_; lean_object* v_state_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2220_; 
v_importedEntries_2210_ = lean_ctor_get(v_ps_2209_, 0);
v_state_2211_ = lean_ctor_get(v_ps_2209_, 1);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_ps_2209_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2213_ = v_ps_2209_;
v_isShared_2214_ = v_isSharedCheck_2220_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_state_2211_);
lean_inc(v_importedEntries_2210_);
lean_dec(v_ps_2209_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2220_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2215_ = lean_task_get_own(v_a_2208_);
v___x_2216_ = l_Array_append___redArg(v_state_2211_, v___x_2215_);
lean_dec(v___x_2215_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 1, v___x_2216_);
v___x_2218_ = v___x_2213_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_importedEntries_2210_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(lean_object* v_as_2221_, size_t v_sz_2222_, size_t v_i_2223_, lean_object* v_b_2224_){
_start:
{
lean_object* v_a_2227_; uint8_t v___x_2231_; 
v___x_2231_ = lean_usize_dec_lt(v_i_2223_, v_sz_2222_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2232_, 0, v_b_2224_);
return v___x_2232_;
}
else
{
lean_object* v___x_2233_; lean_object* v_toEnvExtension_2234_; lean_object* v_asyncMode_2235_; uint8_t v_logWrites_2236_; lean_object* v_a_2237_; lean_object* v___f_2238_; lean_object* v___x_2239_; 
v___x_2233_ = l_Lean_Linter_codeQualityLogExt;
v_toEnvExtension_2234_ = lean_ctor_get(v___x_2233_, 0);
v_asyncMode_2235_ = lean_ctor_get(v_toEnvExtension_2234_, 2);
v_logWrites_2236_ = lean_ctor_get_uint8(v_toEnvExtension_2234_, sizeof(void*)*6);
v_a_2237_ = lean_array_uget_borrowed(v_as_2221_, v_i_2223_);
lean_inc(v_a_2237_);
v___f_2238_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2238_, 0, v_a_2237_);
v___x_2239_ = lean_box(0);
if (v_logWrites_2236_ == 0)
{
lean_object* v___x_2240_; 
lean_inc_ref(v_toEnvExtension_2234_);
v___x_2240_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2234_, v_b_2224_, v___f_2238_, v_asyncMode_2235_, v___x_2239_, v___x_2231_);
v_a_2227_ = v___x_2240_;
goto v___jp_2226_;
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_inc_ref_n(v_toEnvExtension_2234_, 2);
v___x_2241_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2234_, v_b_2224_);
lean_dec_ref(v_b_2224_);
v___x_2242_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2234_, v___x_2241_, v___f_2238_, v_asyncMode_2235_, v___x_2239_, v___x_2231_);
v_a_2227_ = v___x_2242_;
goto v___jp_2226_;
}
}
v___jp_2226_:
{
size_t v___x_2228_; size_t v___x_2229_; 
v___x_2228_ = ((size_t)1ULL);
v___x_2229_ = lean_usize_add(v_i_2223_, v___x_2228_);
v_i_2223_ = v___x_2229_;
v_b_2224_ = v_a_2227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object* v_as_2243_, lean_object* v_sz_2244_, lean_object* v_i_2245_, lean_object* v_b_2246_, lean_object* v___y_2247_){
_start:
{
size_t v_sz_boxed_2248_; size_t v_i_boxed_2249_; lean_object* v_res_2250_; 
v_sz_boxed_2248_ = lean_unbox_usize(v_sz_2244_);
lean_dec(v_sz_2244_);
v_i_boxed_2249_ = lean_unbox_usize(v_i_2245_);
lean_dec(v_i_2245_);
v_res_2250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v_as_2243_, v_sz_boxed_2248_, v_i_boxed_2249_, v_b_2246_);
lean_dec_ref(v_as_2243_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(lean_object* v_s_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = l_Lean_Language_Snapshot_transform(v_s_2253_, v___y_2254_);
v___x_2256_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___closed__0));
v___x_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___boxed(lean_object* v_s_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(v_s_2258_, v___y_2259_);
lean_dec_ref(v___y_2259_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(lean_object* v_t_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v___f_2264_; lean_object* v___x_2265_; 
v___f_2264_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___closed__0));
v___x_2265_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2262_, v___f_2264_, v_a_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object* v_t_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_t_2266_, v_a_2267_);
lean_dec_ref(v_a_2267_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(lean_object* v_t_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___closed__0));
v___x_2273_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2270_, v___x_2272_, v_a_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___boxed(lean_object* v_t_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_t_2274_, v_a_2275_);
lean_dec_ref(v_a_2275_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(lean_object* v_s_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_toSnapshot_2279_; lean_object* v_metaSnap_2280_; lean_object* v_result_x3f_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___y_2285_; 
v_toSnapshot_2279_ = lean_ctor_get(v_s_2277_, 0);
lean_inc_ref(v_toSnapshot_2279_);
v_metaSnap_2280_ = lean_ctor_get(v_s_2277_, 1);
lean_inc_ref(v_metaSnap_2280_);
v_result_x3f_2281_ = lean_ctor_get(v_s_2277_, 2);
lean_inc(v_result_x3f_2281_);
lean_dec_ref(v_s_2277_);
v___x_2282_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2279_, v___y_2278_);
v___x_2283_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2280_, v___y_2278_);
if (lean_obj_tag(v_result_x3f_2281_) == 0)
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_box(0);
v___y_2285_ = v___x_2291_;
goto v___jp_2284_;
}
else
{
lean_object* v_val_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2301_; 
v_val_2292_ = lean_ctor_get(v_result_x3f_2281_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_result_x3f_2281_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2294_ = v_result_x3f_2281_;
v_isShared_2295_ = v_isSharedCheck_2301_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_val_2292_);
lean_dec(v_result_x3f_2281_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2301_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v_firstCmdSnap_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v_firstCmdSnap_2296_ = lean_ctor_get(v_val_2292_, 1);
lean_inc_ref(v_firstCmdSnap_2296_);
lean_dec(v_val_2292_);
v___x_2297_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_firstCmdSnap_2296_, v___y_2278_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2297_);
v___x_2299_ = v___x_2294_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
v___y_2285_ = v___x_2299_;
goto v___jp_2284_;
}
}
}
v___jp_2284_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2286_ = lean_unsigned_to_nat(1u);
v___x_2287_ = lean_mk_empty_array_with_capacity(v___x_2286_);
v___x_2288_ = lean_array_push(v___x_2287_, v___x_2283_);
v___x_2289_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2285_, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2282_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
return v___x_2290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0___boxed(lean_object* v_s_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(v_s_2302_, v___y_2303_);
lean_dec_ref(v___y_2303_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(lean_object* v_t_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___f_2308_; lean_object* v___x_2309_; 
v___f_2308_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___closed__0));
v___x_2309_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2306_, v___f_2308_, v_a_2307_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___boxed(lean_object* v_t_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_t_2310_, v_a_2311_);
lean_dec_ref(v_a_2311_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_a_2313_){
_start:
{
lean_object* v_toSnapshot_2314_; lean_object* v_metaSnap_2315_; lean_object* v_result_x3f_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___y_2321_; 
v_toSnapshot_2314_ = lean_ctor_get(v_a_2313_, 0);
lean_inc_ref(v_toSnapshot_2314_);
v_metaSnap_2315_ = lean_ctor_get(v_a_2313_, 1);
lean_inc_ref(v_metaSnap_2315_);
v_result_x3f_2316_ = lean_ctor_get(v_a_2313_, 4);
lean_inc(v_result_x3f_2316_);
lean_dec_ref(v_a_2313_);
v___x_2317_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_2318_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2314_, v___x_2317_);
v___x_2319_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2315_, v___x_2317_);
if (lean_obj_tag(v_result_x3f_2316_) == 0)
{
lean_object* v___x_2327_; 
v___x_2327_ = lean_box(0);
v___y_2321_ = v___x_2327_;
goto v___jp_2320_;
}
else
{
lean_object* v_val_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2337_; 
v_val_2328_ = lean_ctor_get(v_result_x3f_2316_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_result_x3f_2316_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2330_ = v_result_x3f_2316_;
v_isShared_2331_ = v_isSharedCheck_2337_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_val_2328_);
lean_dec(v_result_x3f_2316_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2337_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v_processedSnap_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v_processedSnap_2332_ = lean_ctor_get(v_val_2328_, 1);
lean_inc_ref(v_processedSnap_2332_);
lean_dec(v_val_2328_);
v___x_2333_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_processedSnap_2332_, v___x_2317_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v___x_2333_);
v___x_2335_ = v___x_2330_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
v___y_2321_ = v___x_2335_;
goto v___jp_2320_;
}
}
}
v___jp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2322_ = lean_unsigned_to_nat(1u);
v___x_2323_ = lean_mk_empty_array_with_capacity(v___x_2322_);
v___x_2324_ = lean_array_push(v___x_2323_, v___x_2319_);
v___x_2325_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2321_, v___x_2324_);
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2318_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
return v___x_2326_;
}
}
}
static double _init_l_Lean_Elab_runFrontend___closed__2(void){
_start:
{
lean_object* v___x_2340_; double v___x_2341_; 
v___x_2340_ = lean_unsigned_to_nat(1000000000u);
v___x_2341_ = lean_float_of_nat(v___x_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_2343_, lean_object* v_opts_2344_, lean_object* v_fileName_2345_, lean_object* v_mainModuleName_2346_, uint32_t v_trustLevel_2347_, lean_object* v_oleanFileName_x3f_2348_, lean_object* v_ileanFileName_x3f_2349_, uint8_t v_jsonOutput_2350_, lean_object* v_errorOnKinds_2351_, lean_object* v_plugins_2352_, uint8_t v_printStats_2353_, lean_object* v_setup_x3f_2354_, lean_object* v_incrSaveFileName_x3f_2355_, lean_object* v_incrLoadFileName_x3f_2356_, lean_object* v_incrHeaderSaveFileName_x3f_2357_){
_start:
{
lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___f_2365_; lean_object* v___f_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; double v___x_2369_; double v___x_2370_; double v___x_2371_; uint8_t v___x_2372_; lean_object* v___y_2374_; size_t v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___y_2437_; size_t v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; uint8_t v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2477_; size_t v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; uint8_t v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; uint8_t v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; size_t v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; uint8_t v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; uint8_t v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; size_t v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; uint8_t v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; uint8_t v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; size_t v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; uint8_t v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; uint8_t v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; uint8_t v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v_a_2644_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v___y_2661_; 
v___f_2365_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___f_2366_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__1));
v___x_2367_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2368_ = lean_io_mono_nanos_now();
v___x_2369_ = lean_float_of_nat(v___x_2368_);
v___x_2370_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__2, &l_Lean_Elab_runFrontend___closed__2_once, _init_l_Lean_Elab_runFrontend___closed__2);
v___x_2371_ = lean_float_div(v___x_2369_, v___x_2370_);
v___x_2372_ = 1;
v___x_2434_ = lean_string_utf8_byte_size(v_input_2343_);
v___x_2435_ = l_Lean_Parser_mkInputContext___redArg(v_input_2343_, v_fileName_2345_, v___x_2372_, v___x_2434_);
v___x_2659_ = l_Lean_internal_cmdlineSnapshots;
if (lean_obj_tag(v_incrSaveFileName_x3f_2355_) == 0)
{
v___y_2661_ = v___x_2372_;
goto v___jp_2660_;
}
else
{
uint8_t v___x_2697_; 
v___x_2697_ = 0;
v___y_2661_ = v___x_2697_;
goto v___jp_2660_;
}
v___jp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2362_ = lean_runtime_forget(v___y_2360_);
v___x_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2363_, 0, v___y_2361_);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
v___jp_2373_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = l_Lean_trace_profiler_output;
v___x_2380_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v___y_2376_, v___x_2379_);
if (lean_obj_tag(v___x_2380_) == 1)
{
lean_object* v_val_2381_; lean_object* v___x_2382_; size_t v_sz_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec_ref(v___y_2377_);
v_val_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_val_2381_);
lean_dec_ref_known(v___x_2380_, 1);
lean_inc_ref(v___y_2374_);
v___x_2382_ = l_Lean_Language_SnapshotTree_getAll(v___y_2374_);
v_sz_2383_ = lean_array_size(v___x_2382_);
v___x_2384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2383_, v___y_2375_, v___x_2382_);
v___x_2385_ = l_Lean_Name_toString(v_mainModuleName_2346_, v___x_2372_);
v___x_2386_ = l_Lean_Firefox_Profile_export(v___x_2385_, v___x_2371_, v___x_2384_, v___y_2376_);
lean_dec_ref(v___y_2376_);
lean_dec_ref(v___x_2384_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2386_, 1);
v___x_2388_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2387_);
v___x_2389_ = l_Lean_Json_compress(v___x_2388_);
v___x_2390_ = l_IO_FS_writeFile(v_val_2381_, v___x_2389_);
lean_dec_ref(v___x_2389_);
lean_dec(v_val_2381_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_dec_ref_known(v___x_2390_, 1);
v___y_2360_ = v___y_2374_;
v___y_2361_ = v___y_2378_;
goto v___jp_2359_;
}
else
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
lean_dec_ref(v___y_2378_);
lean_dec_ref(v___y_2374_);
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec(v_val_2381_);
lean_dec_ref(v___y_2378_);
lean_dec_ref(v___y_2374_);
v_a_2399_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2386_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2386_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
else
{
lean_object* v___x_2407_; uint8_t v___x_2408_; 
lean_dec(v___x_2380_);
v___x_2407_ = l_Lean_trace_profiler_serve;
v___x_2408_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v___y_2377_, v___x_2407_);
lean_dec_ref(v___y_2377_);
if (v___x_2408_ == 0)
{
lean_dec_ref(v___y_2376_);
lean_dec(v_mainModuleName_2346_);
v___y_2360_ = v___y_2374_;
v___y_2361_ = v___y_2378_;
goto v___jp_2359_;
}
else
{
lean_object* v___x_2409_; size_t v_sz_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_inc_ref(v___y_2374_);
v___x_2409_ = l_Lean_Language_SnapshotTree_getAll(v___y_2374_);
v_sz_2410_ = lean_array_size(v___x_2409_);
v___x_2411_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2410_, v___y_2375_, v___x_2409_);
v___x_2412_ = l_Lean_Name_toString(v_mainModuleName_2346_, v___x_2372_);
v___x_2413_ = l_Lean_Firefox_Profile_export(v___x_2412_, v___x_2371_, v___x_2411_, v___y_2376_);
lean_dec_ref(v___y_2376_);
lean_dec_ref(v___x_2411_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2413_, 1);
v___x_2415_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2414_);
v___x_2416_ = l_Lean_Json_compress(v___x_2415_);
v___x_2417_ = l_Lean_Firefox_Profile_serve(v___x_2416_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_dec_ref_known(v___x_2417_, 1);
v___y_2360_ = v___y_2374_;
v___y_2361_ = v___y_2378_;
goto v___jp_2359_;
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_dec_ref(v___y_2378_);
lean_dec_ref(v___y_2374_);
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec_ref(v___y_2378_);
lean_dec_ref(v___y_2374_);
v_a_2426_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2413_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2413_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
}
v___jp_2436_:
{
lean_object* v_fileMap_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v_fst_2449_; lean_object* v_snd_2450_; lean_object* v_stx_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2471_; 
v_fileMap_2446_ = lean_ctor_get(v___x_2435_, 2);
lean_inc_ref(v_fileMap_2446_);
lean_dec_ref(v___x_2435_);
v___x_2447_ = l_Lean_Server_findModuleRefs(v_fileMap_2446_, v___y_2445_, v___y_2442_, v___y_2442_);
lean_dec_ref(v___y_2445_);
v___x_2448_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_2447_);
v_fst_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_fst_2449_);
v_snd_2450_ = lean_ctor_get(v___x_2448_, 1);
lean_inc(v_snd_2450_);
lean_dec_ref(v___x_2448_);
v_stx_2451_ = lean_ctor_get(v___y_2441_, 3);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___y_2441_);
if (v_isSharedCheck_2471_ == 0)
{
lean_object* v_unused_2472_; lean_object* v_unused_2473_; lean_object* v_unused_2474_; lean_object* v_unused_2475_; 
v_unused_2472_ = lean_ctor_get(v___y_2441_, 4);
lean_dec(v_unused_2472_);
v_unused_2473_ = lean_ctor_get(v___y_2441_, 2);
lean_dec(v_unused_2473_);
v_unused_2474_ = lean_ctor_get(v___y_2441_, 1);
lean_dec(v_unused_2474_);
v_unused_2475_ = lean_ctor_get(v___y_2441_, 0);
lean_dec(v_unused_2475_);
v___x_2453_ = v___y_2441_;
v_isShared_2454_ = v_isSharedCheck_2471_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_stx_2451_);
lean_dec(v___y_2441_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2471_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2458_; 
v___x_2455_ = lean_unsigned_to_nat(6u);
v___x_2456_ = l_Lean_Server_collectImports(v_stx_2451_);
lean_inc(v_mainModuleName_2346_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 4, v_snd_2450_);
lean_ctor_set(v___x_2453_, 3, v_fst_2449_);
lean_ctor_set(v___x_2453_, 2, v___x_2456_);
lean_ctor_set(v___x_2453_, 1, v_mainModuleName_2346_);
lean_ctor_set(v___x_2453_, 0, v___x_2455_);
v___x_2458_ = v___x_2453_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_mainModuleName_2346_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v___x_2456_);
lean_ctor_set(v_reuseFailAlloc_2470_, 3, v_fst_2449_);
lean_ctor_set(v_reuseFailAlloc_2470_, 4, v_snd_2450_);
v___x_2458_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = l_Lean_Server_instToJsonIlean_toJson(v___x_2458_);
v___x_2460_ = l_Lean_Json_compress(v___x_2459_);
v___x_2461_ = l_IO_FS_writeFile(v___y_2439_, v___x_2460_);
lean_dec_ref(v___x_2460_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_dec_ref_known(v___x_2461_, 1);
v___y_2374_ = v___y_2437_;
v___y_2375_ = v___y_2438_;
v___y_2376_ = v___y_2440_;
v___y_2377_ = v___y_2444_;
v___y_2378_ = v___y_2443_;
goto v___jp_2373_;
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v___y_2440_);
lean_dec_ref(v___y_2437_);
lean_dec(v_mainModuleName_2346_);
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
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
}
}
v___jp_2476_:
{
if (lean_obj_tag(v_ileanFileName_x3f_2349_) == 1)
{
lean_object* v_val_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
v_val_2485_ = lean_ctor_get(v_ileanFileName_x3f_2349_, 0);
lean_inc_ref(v___y_2477_);
v___x_2486_ = l_Lean_Language_SnapshotTree_getAll(v___y_2477_);
v___x_2487_ = lean_mk_empty_array_with_capacity(v___y_2484_);
v___x_2488_ = lean_array_get_size(v___x_2486_);
v___x_2489_ = lean_nat_dec_lt(v___y_2484_, v___x_2488_);
lean_dec(v___y_2484_);
if (v___x_2489_ == 0)
{
lean_dec_ref(v___x_2486_);
v___y_2437_ = v___y_2477_;
v___y_2438_ = v___y_2478_;
v___y_2439_ = v_val_2485_;
v___y_2440_ = v___y_2480_;
v___y_2441_ = v___y_2479_;
v___y_2442_ = v___y_2481_;
v___y_2443_ = v___y_2483_;
v___y_2444_ = v___y_2482_;
v___y_2445_ = v___x_2487_;
goto v___jp_2436_;
}
else
{
size_t v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = lean_usize_of_nat(v___x_2488_);
v___x_2491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v___x_2486_, v___y_2478_, v___x_2490_, v___x_2487_);
lean_dec_ref(v___x_2486_);
v___y_2437_ = v___y_2477_;
v___y_2438_ = v___y_2478_;
v___y_2439_ = v_val_2485_;
v___y_2440_ = v___y_2480_;
v___y_2441_ = v___y_2479_;
v___y_2442_ = v___y_2481_;
v___y_2443_ = v___y_2483_;
v___y_2444_ = v___y_2482_;
v___y_2445_ = v___x_2491_;
goto v___jp_2436_;
}
}
else
{
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v___x_2435_);
v___y_2374_ = v___y_2477_;
v___y_2375_ = v___y_2478_;
v___y_2376_ = v___y_2480_;
v___y_2377_ = v___y_2482_;
v___y_2378_ = v___y_2483_;
goto v___jp_2373_;
}
}
v___jp_2492_:
{
if (v___y_2500_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_2348_) == 1)
{
lean_object* v_val_2504_; lean_object* v_fileMap_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___f_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v_val_2504_ = lean_ctor_get(v_oleanFileName_x3f_2348_, 0);
lean_inc(v_val_2504_);
lean_dec_ref_known(v_oleanFileName_x3f_2348_, 1);
v_fileMap_2505_ = lean_ctor_get(v___x_2435_, 2);
v___x_2506_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__3));
v___x_2507_ = lean_box(0);
v___x_2508_ = lean_mk_empty_array_with_capacity(v___y_2503_);
lean_inc_ref(v___y_2496_);
v___x_2509_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___y_2496_, v___x_2507_, v___x_2508_);
v___x_2510_ = lean_box(v___x_2372_);
v___x_2511_ = lean_box(v___y_2493_);
lean_inc_ref(v_fileMap_2505_);
v___f_2512_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2512_, 0, v_fileMap_2505_);
lean_closure_set(v___f_2512_, 1, v___y_2495_);
lean_closure_set(v___f_2512_, 2, v___x_2509_);
lean_closure_set(v___f_2512_, 3, v___y_2494_);
lean_closure_set(v___f_2512_, 4, v_val_2504_);
lean_closure_set(v___f_2512_, 5, v___x_2510_);
lean_closure_set(v___f_2512_, 6, v___x_2511_);
v___x_2513_ = lean_box(0);
v___x_2514_ = l_Lean_profileitIOUnsafe___redArg(v___x_2506_, v___y_2502_, v___f_2512_, v___x_2513_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_dec_ref_known(v___x_2514_, 1);
v___y_2477_ = v___y_2496_;
v___y_2478_ = v___y_2497_;
v___y_2479_ = v___y_2499_;
v___y_2480_ = v___y_2498_;
v___y_2481_ = v___y_2500_;
v___y_2482_ = v___y_2502_;
v___y_2483_ = v___y_2501_;
v___y_2484_ = v___y_2503_;
goto v___jp_2476_;
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v___x_2435_);
lean_dec(v_mainModuleName_2346_);
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2514_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2514_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
else
{
lean_dec_ref(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v_oleanFileName_x3f_2348_);
v___y_2477_ = v___y_2496_;
v___y_2478_ = v___y_2497_;
v___y_2479_ = v___y_2499_;
v___y_2480_ = v___y_2498_;
v___y_2481_ = v___y_2500_;
v___y_2482_ = v___y_2502_;
v___y_2483_ = v___y_2501_;
v___y_2484_ = v___y_2503_;
goto v___jp_2476_;
}
}
else
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec_ref(v___x_2435_);
lean_dec(v_oleanFileName_x3f_2348_);
lean_dec(v_mainModuleName_2346_);
v___x_2523_ = lean_box(0);
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
return v___x_2524_;
}
}
v___jp_2525_:
{
if (v_printStats_2353_ == 0)
{
v___y_2493_ = v___y_2526_;
v___y_2494_ = v___y_2528_;
v___y_2495_ = v___y_2527_;
v___y_2496_ = v___y_2529_;
v___y_2497_ = v___y_2530_;
v___y_2498_ = v___y_2532_;
v___y_2499_ = v___y_2531_;
v___y_2500_ = v___y_2533_;
v___y_2501_ = v___y_2535_;
v___y_2502_ = v___y_2534_;
v___y_2503_ = v___y_2536_;
goto v___jp_2492_;
}
else
{
lean_object* v___x_2537_; 
lean_inc_ref(v___y_2535_);
v___x_2537_ = l_Lean_Environment_displayStats(v___y_2535_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_dec_ref_known(v___x_2537_, 1);
v___y_2493_ = v___y_2526_;
v___y_2494_ = v___y_2528_;
v___y_2495_ = v___y_2527_;
v___y_2496_ = v___y_2529_;
v___y_2497_ = v___y_2530_;
v___y_2498_ = v___y_2532_;
v___y_2499_ = v___y_2531_;
v___y_2500_ = v___y_2533_;
v___y_2501_ = v___y_2535_;
v___y_2502_ = v___y_2534_;
v___y_2503_ = v___y_2536_;
goto v___jp_2492_;
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec_ref(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v___x_2435_);
lean_dec(v_oleanFileName_x3f_2348_);
lean_dec(v_mainModuleName_2346_);
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
v___jp_2546_:
{
if (lean_obj_tag(v_incrHeaderSaveFileName_x3f_2357_) == 1)
{
lean_object* v_val_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v_val_2558_ = lean_ctor_get(v_incrHeaderSaveFileName_x3f_2357_, 0);
lean_inc(v_val_2558_);
lean_dec_ref_known(v_incrHeaderSaveFileName_x3f_2357_, 1);
lean_inc_ref(v___y_2554_);
v___x_2559_ = l_Lean_Language_Lean_truncateToHeader(v___y_2554_);
v___x_2560_ = lean_apply_3(v___y_2548_, v_val_2558_, v___x_2559_, lean_box(0));
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_dec_ref_known(v___x_2560_, 1);
lean_inc_ref(v___y_2550_);
v___y_2526_ = v___y_2547_;
v___y_2527_ = v___y_2550_;
v___y_2528_ = v___y_2549_;
v___y_2529_ = v___y_2551_;
v___y_2530_ = v___y_2552_;
v___y_2531_ = v___y_2554_;
v___y_2532_ = v___y_2553_;
v___y_2533_ = v___y_2555_;
v___y_2534_ = v___y_2556_;
v___y_2535_ = v___y_2550_;
v___y_2536_ = v___y_2557_;
goto v___jp_2525_;
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec_ref(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec_ref(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec_ref(v___x_2435_);
lean_dec(v_oleanFileName_x3f_2348_);
lean_dec(v_mainModuleName_2346_);
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2560_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2560_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
else
{
lean_dec_ref(v___y_2548_);
lean_dec(v_incrHeaderSaveFileName_x3f_2357_);
lean_inc_ref(v___y_2550_);
v___y_2526_ = v___y_2547_;
v___y_2527_ = v___y_2550_;
v___y_2528_ = v___y_2549_;
v___y_2529_ = v___y_2551_;
v___y_2530_ = v___y_2552_;
v___y_2531_ = v___y_2554_;
v___y_2532_ = v___y_2553_;
v___y_2533_ = v___y_2555_;
v___y_2534_ = v___y_2556_;
v___y_2535_ = v___y_2550_;
v___y_2536_ = v___y_2557_;
goto v___jp_2525_;
}
}
v___jp_2569_:
{
size_t v_sz_2579_; size_t v___x_2580_; lean_object* v___x_2581_; 
v_sz_2579_ = lean_array_size(v___y_2578_);
v___x_2580_ = ((size_t)0ULL);
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v___y_2578_, v_sz_2579_, v___x_2580_, v___y_2576_);
lean_dec_ref(v___y_2578_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2583_; lean_object* v___f_2584_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc_n(v_a_2582_, 2);
lean_dec_ref_known(v___x_2581_, 1);
v___x_2583_ = lean_box(v___x_2372_);
v___f_2584_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2584_, 0, v_a_2582_);
lean_closure_set(v___f_2584_, 1, v___x_2583_);
if (lean_obj_tag(v_incrSaveFileName_x3f_2355_) == 1)
{
lean_object* v_val_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v_val_2585_ = lean_ctor_get(v_incrSaveFileName_x3f_2355_, 0);
lean_inc(v_val_2585_);
lean_dec_ref_known(v_incrSaveFileName_x3f_2355_, 1);
v___x_2586_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___y_2572_);
lean_inc_ref(v___y_2573_);
v___x_2587_ = l_Lean_Elab_runFrontend___lam__2(v_a_2582_, v___x_2372_, v_val_2585_, v___y_2573_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_dec_ref_known(v___x_2587_, 1);
lean_inc_ref(v___y_2571_);
v___y_2547_ = v___y_2570_;
v___y_2548_ = v___f_2584_;
v___y_2549_ = v___y_2571_;
v___y_2550_ = v_a_2582_;
v___y_2551_ = v___y_2572_;
v___y_2552_ = v___x_2580_;
v___y_2553_ = v___y_2574_;
v___y_2554_ = v___y_2573_;
v___y_2555_ = v___y_2575_;
v___y_2556_ = v___y_2571_;
v___y_2557_ = v___y_2577_;
goto v___jp_2546_;
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v___f_2584_);
lean_dec(v_a_2582_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___x_2435_);
lean_dec(v_incrHeaderSaveFileName_x3f_2357_);
lean_dec(v_oleanFileName_x3f_2348_);
lean_dec(v_mainModuleName_2346_);
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2587_);
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
lean_dec(v_incrSaveFileName_x3f_2355_);
lean_inc_ref(v___y_2571_);
v___y_2547_ = v___y_2570_;
v___y_2548_ = v___f_2584_;
v___y_2549_ = v___y_2571_;
v___y_2550_ = v_a_2582_;
v___y_2551_ = v___y_2572_;
v___y_2552_ = v___x_2580_;
v___y_2553_ = v___y_2574_;
v___y_2554_ = v___y_2573_;
v___y_2555_ = v___y_2575_;
v___y_2556_ = v___y_2571_;
v___y_2557_ = v___y_2577_;
goto v___jp_2546_;
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___x_2435_);
lean_dec(v_incrHeaderSaveFileName_x3f_2357_);
lean_dec(v_incrSaveFileName_x3f_2355_);
lean_dec(v_oleanFileName_x3f_2348_);
lean_dec(v_mainModuleName_2346_);
v_a_2596_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2581_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2581_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
v___jp_2604_:
{
lean_object* v___x_2610_; 
lean_inc_ref(v___y_2605_);
v___x_2610_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_2605_, v___y_2607_, v_jsonOutput_2350_, v___y_2609_);
lean_dec(v___y_2609_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2632_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2632_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2632_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; 
lean_inc_ref(v___y_2606_);
v___x_2615_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___y_2606_);
if (lean_obj_tag(v___x_2615_) == 1)
{
lean_object* v_val_2616_; lean_object* v_env_2617_; lean_object* v_scopes_2618_; lean_object* v___x_2619_; lean_object* v_opts_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
lean_del_object(v___x_2613_);
v_val_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_val_2616_);
lean_dec_ref_known(v___x_2615_, 1);
v_env_2617_ = lean_ctor_get(v_val_2616_, 0);
lean_inc_ref(v_env_2617_);
v_scopes_2618_ = lean_ctor_get(v_val_2616_, 2);
lean_inc(v_scopes_2618_);
lean_dec(v_val_2616_);
lean_inc(v___y_2608_);
v___x_2619_ = l_List_get_x21Internal___redArg(v___x_2367_, v_scopes_2618_, v___y_2608_);
lean_dec(v_scopes_2618_);
v_opts_2620_ = lean_ctor_get(v___x_2619_, 1);
lean_inc_ref(v_opts_2620_);
lean_dec(v___x_2619_);
v___x_2621_ = lean_mk_empty_array_with_capacity(v___y_2608_);
lean_inc_ref(v___x_2621_);
lean_inc_ref(v___y_2606_);
v___x_2622_ = l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(v___y_2606_, v___x_2621_, v___f_2366_);
if (lean_obj_tag(v___x_2622_) == 0)
{
uint8_t v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = lean_unbox(v_a_2611_);
v___x_2624_ = lean_unbox(v_a_2611_);
lean_dec(v_a_2611_);
v___y_2570_ = v___x_2623_;
v___y_2571_ = v_opts_2620_;
v___y_2572_ = v___y_2605_;
v___y_2573_ = v___y_2606_;
v___y_2574_ = v___y_2607_;
v___y_2575_ = v___x_2624_;
v___y_2576_ = v_env_2617_;
v___y_2577_ = v___y_2608_;
v___y_2578_ = v___x_2621_;
goto v___jp_2569_;
}
else
{
lean_object* v_val_2625_; uint8_t v___x_2626_; uint8_t v___x_2627_; 
lean_dec_ref(v___x_2621_);
v_val_2625_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_val_2625_);
lean_dec_ref_known(v___x_2622_, 1);
v___x_2626_ = lean_unbox(v_a_2611_);
v___x_2627_ = lean_unbox(v_a_2611_);
lean_dec(v_a_2611_);
v___y_2570_ = v___x_2626_;
v___y_2571_ = v_opts_2620_;
v___y_2572_ = v___y_2605_;
v___y_2573_ = v___y_2606_;
v___y_2574_ = v___y_2607_;
v___y_2575_ = v___x_2627_;
v___y_2576_ = v_env_2617_;
v___y_2577_ = v___y_2608_;
v___y_2578_ = v_val_2625_;
goto v___jp_2569_;
}
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2630_; 
lean_dec(v___x_2615_);
lean_dec(v_a_2611_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___x_2435_);
lean_dec(v_incrHeaderSaveFileName_x3f_2357_);
lean_dec(v_incrSaveFileName_x3f_2355_);
lean_dec(v_oleanFileName_x3f_2348_);
lean_dec(v_mainModuleName_2346_);
v___x_2628_ = lean_box(0);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2628_);
v___x_2630_ = v___x_2613_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v___x_2435_);
lean_dec(v_incrHeaderSaveFileName_x3f_2357_);
lean_dec(v_incrSaveFileName_x3f_2355_);
lean_dec(v_oleanFileName_x3f_2348_);
lean_dec(v_mainModuleName_2346_);
v_a_2633_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2610_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2610_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
v___jp_2641_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2645_ = l_Lean_Language_Lean_process(v___y_2642_, v_a_2644_, v___x_2435_);
lean_inc_ref(v___x_2645_);
v___x_2646_ = l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(v___x_2645_);
v___x_2647_ = lean_box(1);
v___x_2648_ = lean_unsigned_to_nat(0u);
v___x_2649_ = lean_array_get_size(v_errorOnKinds_2351_);
v___x_2650_ = lean_nat_dec_lt(v___x_2648_, v___x_2649_);
if (v___x_2650_ == 0)
{
v___y_2605_ = v___x_2646_;
v___y_2606_ = v___x_2645_;
v___y_2607_ = v___y_2643_;
v___y_2608_ = v___x_2648_;
v___y_2609_ = v___x_2647_;
goto v___jp_2604_;
}
else
{
size_t v___x_2651_; size_t v___x_2652_; lean_object* v___x_2653_; 
v___x_2651_ = ((size_t)0ULL);
v___x_2652_ = lean_usize_of_nat(v___x_2649_);
v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_errorOnKinds_2351_, v___x_2651_, v___x_2652_, v___x_2647_);
v___y_2605_ = v___x_2646_;
v___y_2606_ = v___x_2645_;
v___y_2607_ = v___y_2643_;
v___y_2608_ = v___x_2648_;
v___y_2609_ = v___x_2653_;
goto v___jp_2604_;
}
}
v___jp_2654_:
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_a_2657_);
v___y_2642_ = v___y_2655_;
v___y_2643_ = v___y_2656_;
v_a_2644_ = v___x_2658_;
goto v___jp_2641_;
}
v___jp_2660_:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___f_2667_; 
v___x_2662_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2344_, v___x_2659_, v___y_2661_);
v___x_2663_ = l_Lean_Elab_async;
v___x_2664_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_2662_, v___x_2663_, v___x_2372_);
v___x_2665_ = lean_box_uint32(v_trustLevel_2347_);
v___x_2666_ = lean_box(v___x_2372_);
lean_inc(v_mainModuleName_2346_);
lean_inc_ref(v___x_2664_);
v___f_2667_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4___boxed), 10, 7);
lean_closure_set(v___f_2667_, 0, v_setup_x3f_2354_);
lean_closure_set(v___f_2667_, 1, v___f_2365_);
lean_closure_set(v___f_2667_, 2, v___x_2664_);
lean_closure_set(v___f_2667_, 3, v_plugins_2352_);
lean_closure_set(v___f_2667_, 4, v___x_2665_);
lean_closure_set(v___f_2667_, 5, v___x_2666_);
lean_closure_set(v___f_2667_, 6, v_mainModuleName_2346_);
if (lean_obj_tag(v_incrLoadFileName_x3f_2356_) == 0)
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_box(0);
v___y_2642_ = v___f_2667_;
v___y_2643_ = v___x_2664_;
v_a_2644_ = v___x_2668_;
goto v___jp_2641_;
}
else
{
lean_object* v_val_2669_; lean_object* v___x_2670_; 
v_val_2669_ = lean_ctor_get(v_incrLoadFileName_x3f_2356_, 0);
lean_inc(v_val_2669_);
lean_dec_ref_known(v_incrLoadFileName_x3f_2356_, 1);
v___x_2670_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_val_2669_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v_snap_2672_; lean_object* v_initModIdxs_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v_snap_2672_ = lean_ctor_get(v_a_2671_, 0);
lean_inc_ref(v_snap_2672_);
v_initModIdxs_2673_ = lean_ctor_get(v_a_2671_, 1);
lean_inc_ref(v_initModIdxs_2673_);
lean_dec(v_a_2671_);
lean_inc(v_mainModuleName_2346_);
v___x_2674_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(v_snap_2672_, v_mainModuleName_2346_);
lean_inc_ref(v___x_2674_);
v___x_2675_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v___x_2674_);
v___x_2676_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_2675_);
if (lean_obj_tag(v___x_2676_) == 1)
{
lean_object* v_val_2677_; lean_object* v___f_2678_; lean_object* v___x_2679_; 
v_val_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_val_2677_);
lean_dec_ref_known(v___x_2676_, 1);
lean_inc_ref(v___x_2664_);
v___f_2678_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__5___boxed), 4, 3);
lean_closure_set(v___f_2678_, 0, v_val_2677_);
lean_closure_set(v___f_2678_, 1, v_initModIdxs_2673_);
lean_closure_set(v___f_2678_, 2, v___x_2664_);
v___x_2679_ = l_Lean_withImporting___redArg(v___f_2678_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v___x_2680_; 
lean_dec_ref_known(v___x_2679_, 1);
v___x_2680_ = lean_enable_initializer_execution();
v___y_2655_ = v___f_2667_;
v___y_2656_ = v___x_2664_;
v_a_2657_ = v___x_2674_;
goto v___jp_2654_;
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec_ref(v___x_2674_);
lean_dec_ref(v___f_2667_);
lean_dec_ref(v___x_2664_);
lean_dec_ref(v___x_2435_);
lean_dec(v_incrHeaderSaveFileName_x3f_2357_);
lean_dec(v_incrSaveFileName_x3f_2355_);
lean_dec(v_oleanFileName_x3f_2348_);
lean_dec(v_mainModuleName_2346_);
v_a_2681_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2679_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2679_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
else
{
lean_dec(v___x_2676_);
lean_dec_ref(v_initModIdxs_2673_);
v___y_2655_ = v___f_2667_;
v___y_2656_ = v___x_2664_;
v_a_2657_ = v___x_2674_;
goto v___jp_2654_;
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec_ref(v___f_2667_);
lean_dec_ref(v___x_2664_);
lean_dec_ref(v___x_2435_);
lean_dec(v_incrHeaderSaveFileName_x3f_2357_);
lean_dec(v_incrSaveFileName_x3f_2355_);
lean_dec(v_oleanFileName_x3f_2348_);
lean_dec(v_mainModuleName_2346_);
v_a_2689_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2670_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2670_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_2698_, lean_object* v_opts_2699_, lean_object* v_fileName_2700_, lean_object* v_mainModuleName_2701_, lean_object* v_trustLevel_2702_, lean_object* v_oleanFileName_x3f_2703_, lean_object* v_ileanFileName_x3f_2704_, lean_object* v_jsonOutput_2705_, lean_object* v_errorOnKinds_2706_, lean_object* v_plugins_2707_, lean_object* v_printStats_2708_, lean_object* v_setup_x3f_2709_, lean_object* v_incrSaveFileName_x3f_2710_, lean_object* v_incrLoadFileName_x3f_2711_, lean_object* v_incrHeaderSaveFileName_x3f_2712_, lean_object* v_a_2713_){
_start:
{
uint32_t v_trustLevel_boxed_2714_; uint8_t v_jsonOutput_boxed_2715_; uint8_t v_printStats_boxed_2716_; lean_object* v_res_2717_; 
v_trustLevel_boxed_2714_ = lean_unbox_uint32(v_trustLevel_2702_);
lean_dec(v_trustLevel_2702_);
v_jsonOutput_boxed_2715_ = lean_unbox(v_jsonOutput_2705_);
v_printStats_boxed_2716_ = lean_unbox(v_printStats_2708_);
v_res_2717_ = l_Lean_Elab_runFrontend(v_input_2698_, v_opts_2699_, v_fileName_2700_, v_mainModuleName_2701_, v_trustLevel_boxed_2714_, v_oleanFileName_x3f_2703_, v_ileanFileName_x3f_2704_, v_jsonOutput_boxed_2715_, v_errorOnKinds_2706_, v_plugins_2707_, v_printStats_boxed_2716_, v_setup_x3f_2709_, v_incrSaveFileName_x3f_2710_, v_incrLoadFileName_x3f_2711_, v_incrHeaderSaveFileName_x3f_2712_);
lean_dec_ref(v_errorOnKinds_2706_);
lean_dec(v_ileanFileName_x3f_2704_);
return v_res_2717_;
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
