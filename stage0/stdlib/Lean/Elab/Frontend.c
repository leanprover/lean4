// Lean compiler output
// Module: Lean.Elab.Frontend
// Imports: public import Lean.Language.Lean public import Lean.Server.References public import Lean.Util.Profiler import Lean.Compiler.Options import Lean.Linter.PersistentLintLog import Lean.Util.ProfilerServer
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
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_load_dynlib(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* l_Lean_Options_mergeBy(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object*);
uint8_t lean_strict_or(uint8_t, uint8_t);
lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Language_Lean_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* l_Array_toPArray_x27___redArg(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
lean_object* l_Lean_Linter_recordLints(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Lean_writeModule(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Language_Lean_pushOpt___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_runtime_forget(lean_object*);
lean_object* lean_io_mono_nanos_now();
extern lean_object* l_Lean_internal_cmdlineSnapshots;
extern lean_object* l_Lean_Elab_async;
lean_object* l_Lean_Language_Lean_process(lean_object*, lean_object*, lean_object*);
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler_output;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Firefox_Profile_export(lean_object*, double, lean_object*, lean_object*);
lean_object* l_Lean_Firefox_instToJsonProfile_toJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_serve;
lean_object* l_Lean_Firefox_Profile_serve(lean_object*);
lean_object* l_Lean_Server_findModuleRefs(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs(lean_object*);
lean_object* l_Lean_Server_collectImports(lean_object*);
lean_object* l_Lean_Server_instToJsonIlean_toJson(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_runFrontend___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_runFrontend___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_runFrontend___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_runFrontend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__0_value;
static const lean_closure_object l_Lean_Elab_runFrontend___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__1 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__1_value;
static lean_once_cell_t l_Lean_Elab_runFrontend___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_runFrontend___closed__2;
static const lean_string_object l_Lean_Elab_runFrontend___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ".olean serialization"};
static const lean_object* l_Lean_Elab_runFrontend___closed__3 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__3_value;
static const lean_closure_object l_Lean_Elab_runFrontend___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__5, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_runFrontend___closed__1_value)} };
static const lean_object* l_Lean_Elab_runFrontend___closed__4 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_51_);
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
lean_dec_ref(v___x_99_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object* v_stx_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_134_; lean_object* v_commandState_135_; lean_object* v_cmdPos_136_; lean_object* v___x_137_; lean_object* v_fileName_138_; lean_object* v_fileMap_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_134_ = lean_st_ref_get(v_a_132_);
v_commandState_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_commandState_135_);
v_cmdPos_136_ = lean_ctor_get(v___x_134_, 2);
lean_inc(v_cmdPos_136_);
lean_dec(v___x_134_);
v___x_137_ = lean_st_mk_ref(v_commandState_135_);
v_fileName_138_ = lean_ctor_get(v_a_131_, 1);
v_fileMap_139_ = lean_ctor_get(v_a_131_, 2);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_box(0);
v___x_142_ = lean_box(0);
v___x_143_ = l_Lean_firstFrontendMacroScope;
v___x_144_ = lean_box(0);
v___x_145_ = 0;
lean_inc_ref(v_fileMap_139_);
lean_inc_ref(v_fileName_138_);
v___x_146_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_146_, 0, v_fileName_138_);
lean_ctor_set(v___x_146_, 1, v_fileMap_139_);
lean_ctor_set(v___x_146_, 2, v___x_140_);
lean_ctor_set(v___x_146_, 3, v_cmdPos_136_);
lean_ctor_set(v___x_146_, 4, v___x_141_);
lean_ctor_set(v___x_146_, 5, v___x_142_);
lean_ctor_set(v___x_146_, 6, v___x_143_);
lean_ctor_set(v___x_146_, 7, v___x_144_);
lean_ctor_set(v___x_146_, 8, v___x_142_);
lean_ctor_set(v___x_146_, 9, v___x_142_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*10, v___x_145_);
v___x_147_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_130_, v___x_146_, v___x_137_);
lean_dec_ref(v___x_146_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_148_);
lean_dec_ref(v___x_147_);
v___x_149_ = lean_st_ref_get(v___x_137_);
lean_dec(v___x_137_);
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
lean_dec(v___x_137_);
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
lean_object* v_pos_186_; lean_object* v___x_188_; 
v_pos_186_ = lean_ctor_get(v_parserState_180_, 0);
lean_inc(v_pos_186_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 2, v_pos_186_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_commandState_181_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_parserState_180_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_pos_186_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_commands_182_);
v___x_188_ = v_reuseFailAlloc_192_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_st_ref_set(v_a_177_, v___x_188_);
v___x_190_ = lean_box(0);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
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
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v_ps_238_);
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_commandState_242_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_ps_238_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_cmdPos_243_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v_commands_244_);
v___x_249_ = v_reuseFailAlloc_253_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_st_ref_set(v_a_239_, v___x_249_);
v___x_251_ = lean_box(0);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
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
lean_object* v___x_273_; lean_object* v_commandState_274_; lean_object* v_parserState_275_; lean_object* v_cmdPos_276_; lean_object* v_commands_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_306_; 
v___x_273_ = lean_st_ref_take(v_a_271_);
v_commandState_274_ = lean_ctor_get(v___x_273_, 0);
v_parserState_275_ = lean_ctor_get(v___x_273_, 1);
v_cmdPos_276_ = lean_ctor_get(v___x_273_, 2);
v_commands_277_ = lean_ctor_get(v___x_273_, 3);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_306_ == 0)
{
v___x_279_ = v___x_273_;
v_isShared_280_ = v_isSharedCheck_306_;
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
v_isShared_280_ = v_isSharedCheck_306_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v_env_281_; lean_object* v_scopes_282_; lean_object* v_usedQuotCtxts_283_; lean_object* v_nextMacroScope_284_; lean_object* v_maxRecDepth_285_; lean_object* v_ngen_286_; lean_object* v_auxDeclNGen_287_; lean_object* v_infoState_288_; lean_object* v_traceState_289_; lean_object* v_snapshotTasks_290_; lean_object* v_newDecls_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_304_; 
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
v_newDecls_291_ = lean_ctor_get(v_commandState_274_, 11);
v_isSharedCheck_304_ = !lean_is_exclusive(v_commandState_274_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v_commandState_274_, 1);
lean_dec(v_unused_305_);
v___x_293_ = v_commandState_274_;
v_isShared_294_ = v_isSharedCheck_304_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_newDecls_291_);
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
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_304_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_msgs_270_);
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_env_281_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_msgs_270_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_scopes_282_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_usedQuotCtxts_283_);
lean_ctor_set(v_reuseFailAlloc_303_, 4, v_nextMacroScope_284_);
lean_ctor_set(v_reuseFailAlloc_303_, 5, v_maxRecDepth_285_);
lean_ctor_set(v_reuseFailAlloc_303_, 6, v_ngen_286_);
lean_ctor_set(v_reuseFailAlloc_303_, 7, v_auxDeclNGen_287_);
lean_ctor_set(v_reuseFailAlloc_303_, 8, v_infoState_288_);
lean_ctor_set(v_reuseFailAlloc_303_, 9, v_traceState_289_);
lean_ctor_set(v_reuseFailAlloc_303_, 10, v_snapshotTasks_290_);
lean_ctor_set(v_reuseFailAlloc_303_, 11, v_newDecls_291_);
v___x_296_ = v_reuseFailAlloc_303_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_298_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_296_);
v___x_298_ = v___x_279_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_parserState_275_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_cmdPos_276_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v_commands_277_);
v___x_298_ = v_reuseFailAlloc_302_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_st_ref_set(v_a_271_, v___x_298_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg___boxed(lean_object* v_msgs_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_307_, v_a_308_);
lean_dec(v_a_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object* v_msgs_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_311_, v_a_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___boxed(lean_object* v_msgs_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Elab_Frontend_setMessages(v_msgs_316_, v_a_317_, v_a_318_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg(lean_object* v_a_321_){
_start:
{
lean_object* v___x_323_; 
lean_inc_ref(v_a_321_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v_a_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg___boxed(lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Elab_Frontend_getInputContext___redArg(v_a_324_);
lean_dec_ref(v_a_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; 
lean_inc_ref(v_a_327_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v_a_327_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Elab_Frontend_getInputContext(v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0(lean_object* v_a_335_, lean_object* v___x_336_, lean_object* v_a_337_, lean_object* v_messages_338_, lean_object* v_x_339_){
_start:
{
lean_object* v___x_340_; 
lean_inc_ref(v_a_335_);
v___x_340_ = l_Lean_Parser_parseCommand(v_a_335_, v___x_336_, v_a_337_, v_messages_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0___boxed(lean_object* v_a_341_, lean_object* v___x_342_, lean_object* v_a_343_, lean_object* v_messages_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Elab_Frontend_processCommand___lam__0(v_a_341_, v___x_342_, v_a_343_, v_messages_344_, v_x_345_);
lean_dec_ref(v_a_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_a_353_; lean_object* v___x_354_; lean_object* v_a_355_; lean_object* v_env_356_; lean_object* v_messages_357_; lean_object* v_scopes_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_opts_361_; lean_object* v_currNamespace_362_; lean_object* v_openDecls_363_; lean_object* v___x_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v_snd_369_; lean_object* v_fst_370_; lean_object* v_fst_371_; lean_object* v_snd_372_; lean_object* v___x_373_; lean_object* v_commandState_374_; lean_object* v_parserState_375_; lean_object* v_cmdPos_376_; lean_object* v_commands_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_407_; 
v___x_351_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_349_);
lean_dec_ref(v___x_351_);
v___x_352_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_349_);
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref(v___x_352_);
v___x_354_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_349_);
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref(v___x_354_);
v_env_356_ = lean_ctor_get(v_a_353_, 0);
lean_inc_ref(v_env_356_);
v_messages_357_ = lean_ctor_get(v_a_353_, 1);
lean_inc_ref(v_messages_357_);
v_scopes_358_ = lean_ctor_get(v_a_353_, 2);
lean_inc(v_scopes_358_);
lean_dec(v_a_353_);
v___x_359_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_360_ = l_List_head_x21___redArg(v___x_359_, v_scopes_358_);
lean_dec(v_scopes_358_);
v_opts_361_ = lean_ctor_get(v___x_360_, 1);
lean_inc_ref_n(v_opts_361_, 2);
v_currNamespace_362_ = lean_ctor_get(v___x_360_, 2);
lean_inc(v_currNamespace_362_);
v_openDecls_363_ = lean_ctor_get(v___x_360_, 3);
lean_inc(v_openDecls_363_);
lean_dec(v___x_360_);
v___x_364_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_364_, 0, v_env_356_);
lean_ctor_set(v___x_364_, 1, v_opts_361_);
lean_ctor_set(v___x_364_, 2, v_currNamespace_362_);
lean_ctor_set(v___x_364_, 3, v_openDecls_363_);
lean_inc_ref(v_a_348_);
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommand___lam__0___boxed), 5, 4);
lean_closure_set(v___f_365_, 0, v_a_348_);
lean_closure_set(v___f_365_, 1, v___x_364_);
lean_closure_set(v___f_365_, 2, v_a_355_);
lean_closure_set(v___f_365_, 3, v_messages_357_);
v___x_366_ = ((lean_object*)(l_Lean_Elab_Frontend_processCommand___closed__0));
v___x_367_ = lean_box(0);
v___x_368_ = lean_profileit(v___x_366_, v_opts_361_, v___f_365_, v___x_367_);
lean_dec_ref(v_opts_361_);
v_snd_369_ = lean_ctor_get(v___x_368_, 1);
lean_inc(v_snd_369_);
v_fst_370_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_fst_370_);
lean_dec(v___x_368_);
v_fst_371_ = lean_ctor_get(v_snd_369_, 0);
lean_inc(v_fst_371_);
v_snd_372_ = lean_ctor_get(v_snd_369_, 1);
lean_inc(v_snd_372_);
lean_dec(v_snd_369_);
v___x_373_ = lean_st_ref_take(v_a_349_);
v_commandState_374_ = lean_ctor_get(v___x_373_, 0);
v_parserState_375_ = lean_ctor_get(v___x_373_, 1);
v_cmdPos_376_ = lean_ctor_get(v___x_373_, 2);
v_commands_377_ = lean_ctor_get(v___x_373_, 3);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_407_ == 0)
{
v___x_379_ = v___x_373_;
v_isShared_380_ = v_isSharedCheck_407_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_commands_377_);
lean_inc(v_cmdPos_376_);
lean_inc(v_parserState_375_);
lean_inc(v_commandState_374_);
lean_dec(v___x_373_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_407_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
lean_inc(v_fst_370_);
v___x_381_ = lean_array_push(v_commands_377_, v_fst_370_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 3, v___x_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_commandState_374_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_parserState_375_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_cmdPos_376_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v___x_381_);
v___x_383_ = v_reuseFailAlloc_406_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = lean_st_ref_set(v_a_349_, v___x_383_);
v___x_385_ = l_Lean_Elab_Frontend_setParserState___redArg(v_fst_371_, v_a_349_);
lean_dec_ref(v___x_385_);
v___x_386_ = l_Lean_Elab_Frontend_setMessages___redArg(v_snd_372_, v_a_349_);
lean_dec_ref(v___x_386_);
lean_inc(v_fst_370_);
v___x_387_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_fst_370_, v_a_348_, v_a_349_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_396_; 
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v___x_387_, 0);
lean_dec(v_unused_397_);
v___x_389_ = v___x_387_;
v_isShared_390_ = v_isSharedCheck_396_;
goto v_resetjp_388_;
}
else
{
lean_dec(v___x_387_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_396_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint8_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = l_Lean_Parser_isTerminalCommand(v_fst_370_);
v___x_392_ = lean_box(v___x_391_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec(v_fst_370_);
v_a_398_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_387_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_387_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Elab_Frontend_processCommand(v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Elab_Frontend_processCommand(v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_426_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_426_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_426_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_426_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
uint8_t v___x_420_; 
v___x_420_ = lean_unbox(v_a_416_);
lean_dec(v_a_416_);
if (v___x_420_ == 0)
{
lean_del_object(v___x_418_);
goto _start;
}
else
{
lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_422_ = lean_box(0);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_422_);
v___x_424_ = v___x_418_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
v_a_427_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_415_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_415_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands___boxed(lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Elab_Frontend_processCommands(v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object* v_as_439_, size_t v_i_440_, size_t v_stop_441_, lean_object* v_b_442_){
_start:
{
lean_object* v___y_444_; uint8_t v___x_448_; 
v___x_448_ = lean_usize_dec_eq(v_i_440_, v_stop_441_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
v___x_449_ = lean_array_uget_borrowed(v_as_439_, v_i_440_);
if (lean_obj_tag(v___x_449_) == 0)
{
v___y_444_ = v_b_442_;
goto v___jp_443_;
}
else
{
lean_object* v_val_450_; lean_object* v___x_451_; 
v_val_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_val_450_);
v___x_451_ = lean_array_push(v_b_442_, v_val_450_);
v___y_444_ = v___x_451_;
goto v___jp_443_;
}
}
else
{
return v_b_442_;
}
v___jp_443_:
{
size_t v___x_445_; size_t v___x_446_; 
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_add(v_i_440_, v___x_445_);
v_i_440_ = v___x_446_;
v_b_442_ = v___y_444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object* v_as_452_, lean_object* v_i_453_, lean_object* v_stop_454_, lean_object* v_b_455_){
_start:
{
size_t v_i_boxed_456_; size_t v_stop_boxed_457_; lean_object* v_res_458_; 
v_i_boxed_456_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_stop_boxed_457_ = lean_unbox_usize(v_stop_454_);
lean_dec(v_stop_454_);
v_res_458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_452_, v_i_boxed_456_, v_stop_boxed_457_, v_b_455_);
lean_dec_ref(v_as_452_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object* v_as_461_, lean_object* v_start_462_, lean_object* v_stop_463_){
_start:
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_465_ = lean_nat_dec_lt(v_start_462_, v_stop_463_);
if (v___x_465_ == 0)
{
return v___x_464_;
}
else
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_array_get_size(v_as_461_);
v___x_467_ = lean_nat_dec_le(v_stop_463_, v___x_466_);
if (v___x_467_ == 0)
{
uint8_t v___x_468_; 
v___x_468_ = lean_nat_dec_lt(v_start_462_, v___x_466_);
if (v___x_468_ == 0)
{
return v___x_464_;
}
else
{
size_t v___x_469_; size_t v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_usize_of_nat(v_start_462_);
v___x_470_ = lean_usize_of_nat(v___x_466_);
v___x_471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_461_, v___x_469_, v___x_470_, v___x_464_);
return v___x_471_;
}
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_usize_of_nat(v_start_462_);
v___x_473_ = lean_usize_of_nat(v_stop_463_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_461_, v___x_472_, v___x_473_, v___x_464_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object* v_as_475_, lean_object* v_start_476_, lean_object* v_stop_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v_as_475_, v_start_476_, v_stop_477_);
lean_dec(v_stop_477_);
lean_dec(v_start_476_);
lean_dec_ref(v_as_475_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t v_sz_479_, size_t v_i_480_, lean_object* v_bs_481_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = lean_usize_dec_lt(v_i_480_, v_sz_479_);
if (v___x_482_ == 0)
{
return v_bs_481_;
}
else
{
lean_object* v_v_483_; lean_object* v_elabSnap_484_; lean_object* v_infoTreeSnap_485_; lean_object* v___x_486_; lean_object* v_infoTree_x3f_487_; lean_object* v___x_488_; lean_object* v_bs_x27_489_; size_t v___x_490_; size_t v___x_491_; lean_object* v___x_492_; 
v_v_483_ = lean_array_uget_borrowed(v_bs_481_, v_i_480_);
v_elabSnap_484_ = lean_ctor_get(v_v_483_, 3);
v_infoTreeSnap_485_ = lean_ctor_get(v_elabSnap_484_, 3);
lean_inc_ref(v_infoTreeSnap_485_);
v___x_486_ = l_Lean_Language_SnapshotTask_get___redArg(v_infoTreeSnap_485_);
v_infoTree_x3f_487_ = lean_ctor_get(v___x_486_, 2);
lean_inc(v_infoTree_x3f_487_);
lean_dec(v___x_486_);
v___x_488_ = lean_unsigned_to_nat(0u);
v_bs_x27_489_ = lean_array_uset(v_bs_481_, v_i_480_, v___x_488_);
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_add(v_i_480_, v___x_490_);
v___x_492_ = lean_array_uset(v_bs_x27_489_, v_i_480_, v_infoTree_x3f_487_);
v_i_480_ = v___x_491_;
v_bs_481_ = v___x_492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object* v_sz_494_, lean_object* v_i_495_, lean_object* v_bs_496_){
_start:
{
size_t v_sz_boxed_497_; size_t v_i_boxed_498_; lean_object* v_res_499_; 
v_sz_boxed_497_ = lean_unbox_usize(v_sz_494_);
lean_dec(v_sz_494_);
v_i_boxed_498_ = lean_unbox_usize(v_i_495_);
lean_dec(v_i_495_);
v_res_499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_boxed_497_, v_i_boxed_498_, v_bs_496_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(lean_object* v_as_500_, size_t v_i_501_, size_t v_stop_502_, lean_object* v_b_503_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_eq(v_i_501_, v_stop_502_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; size_t v___x_507_; size_t v___x_508_; 
v___x_505_ = lean_array_uget_borrowed(v_as_500_, v_i_501_);
lean_inc(v___x_505_);
v___x_506_ = l_Lean_MessageLog_append(v_b_503_, v___x_505_);
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_add(v_i_501_, v___x_507_);
v_i_501_ = v___x_508_;
v_b_503_ = v___x_506_;
goto _start;
}
else
{
return v_b_503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object* v_as_510_, lean_object* v_i_511_, lean_object* v_stop_512_, lean_object* v_b_513_){
_start:
{
size_t v_i_boxed_514_; size_t v_stop_boxed_515_; lean_object* v_res_516_; 
v_i_boxed_514_ = lean_unbox_usize(v_i_511_);
lean_dec(v_i_511_);
v_stop_boxed_515_ = lean_unbox_usize(v_stop_512_);
lean_dec(v_stop_512_);
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_as_510_, v_i_boxed_514_, v_stop_boxed_515_, v_b_513_);
lean_dec_ref(v_as_510_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t v_sz_517_, size_t v_i_518_, lean_object* v_bs_519_){
_start:
{
uint8_t v___x_520_; 
v___x_520_ = lean_usize_dec_lt(v_i_518_, v_sz_517_);
if (v___x_520_ == 0)
{
return v_bs_519_;
}
else
{
lean_object* v_v_521_; lean_object* v_stx_522_; lean_object* v___x_523_; lean_object* v_bs_x27_524_; size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v_v_521_ = lean_array_uget_borrowed(v_bs_519_, v_i_518_);
v_stx_522_ = lean_ctor_get(v_v_521_, 1);
lean_inc(v_stx_522_);
v___x_523_ = lean_unsigned_to_nat(0u);
v_bs_x27_524_ = lean_array_uset(v_bs_519_, v_i_518_, v___x_523_);
v___x_525_ = ((size_t)1ULL);
v___x_526_ = lean_usize_add(v_i_518_, v___x_525_);
v___x_527_ = lean_array_uset(v_bs_x27_524_, v_i_518_, v_stx_522_);
v_i_518_ = v___x_526_;
v_bs_519_ = v___x_527_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object* v_sz_529_, lean_object* v_i_530_, lean_object* v_bs_531_){
_start:
{
size_t v_sz_boxed_532_; size_t v_i_boxed_533_; lean_object* v_res_534_; 
v_sz_boxed_532_ = lean_unbox_usize(v_sz_529_);
lean_dec(v_sz_529_);
v_i_boxed_533_ = lean_unbox_usize(v_i_530_);
lean_dec(v_i_530_);
v_res_534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_boxed_532_, v_i_boxed_533_, v_bs_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(size_t v_sz_535_, size_t v_i_536_, lean_object* v_bs_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = lean_usize_dec_lt(v_i_536_, v_sz_535_);
if (v___x_538_ == 0)
{
return v_bs_537_;
}
else
{
lean_object* v_v_539_; lean_object* v_diagnostics_540_; lean_object* v_msgLog_541_; lean_object* v___x_542_; lean_object* v_bs_x27_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v_v_539_ = lean_array_uget_borrowed(v_bs_537_, v_i_536_);
v_diagnostics_540_ = lean_ctor_get(v_v_539_, 1);
v_msgLog_541_ = lean_ctor_get(v_diagnostics_540_, 0);
lean_inc_ref(v_msgLog_541_);
v___x_542_ = lean_unsigned_to_nat(0u);
v_bs_x27_543_ = lean_array_uset(v_bs_537_, v_i_536_, v___x_542_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_i_536_, v___x_544_);
v___x_546_ = lean_array_uset(v_bs_x27_543_, v_i_536_, v_msgLog_541_);
v_i_536_ = v___x_545_;
v_bs_537_ = v___x_546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3___boxed(lean_object* v_sz_548_, lean_object* v_i_549_, lean_object* v_bs_550_){
_start:
{
size_t v_sz_boxed_551_; size_t v_i_boxed_552_; lean_object* v_res_553_; 
v_sz_boxed_551_ = lean_unbox_usize(v_sz_548_);
lean_dec(v_sz_548_);
v_i_boxed_552_ = lean_unbox_usize(v_i_549_);
lean_dec(v_i_549_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_sz_boxed_551_, v_i_boxed_552_, v_bs_550_);
return v_res_553_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_unsigned_to_nat(32u);
v___x_555_ = lean_mk_empty_array_with_capacity(v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1(void){
_start:
{
size_t v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_557_ = ((size_t)5ULL);
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_unsigned_to_nat(32u);
v___x_560_ = lean_mk_empty_array_with_capacity(v___x_559_);
v___x_561_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0);
v___x_562_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
lean_ctor_set(v___x_562_, 2, v___x_558_);
lean_ctor_set(v___x_562_, 3, v___x_558_);
lean_ctor_set_usize(v___x_562_, 4, v___x_557_);
return v___x_562_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2(void){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_563_ = l_Lean_NameSet_empty;
v___x_564_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1);
v___x_565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
lean_ctor_set(v___x_565_, 2, v___x_563_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(lean_object* v_inputCtx_566_, lean_object* v_initialSnap_567_, lean_object* v_t_568_, lean_object* v_commands_569_){
_start:
{
lean_object* v_snap_571_; lean_object* v_parserState_572_; lean_object* v_elabSnap_573_; lean_object* v_nextCmdSnap_x3f_574_; lean_object* v_commands_575_; 
v_snap_571_ = lean_task_get_own(v_t_568_);
v_parserState_572_ = lean_ctor_get(v_snap_571_, 2);
lean_inc_ref(v_parserState_572_);
v_elabSnap_573_ = lean_ctor_get(v_snap_571_, 3);
lean_inc_ref(v_elabSnap_573_);
v_nextCmdSnap_x3f_574_ = lean_ctor_get(v_snap_571_, 4);
lean_inc(v_nextCmdSnap_x3f_574_);
v_commands_575_ = lean_array_push(v_commands_569_, v_snap_571_);
if (lean_obj_tag(v_nextCmdSnap_x3f_574_) == 1)
{
lean_object* v_val_576_; lean_object* v_task_577_; 
lean_dec_ref(v_elabSnap_573_);
lean_dec_ref(v_parserState_572_);
v_val_576_ = lean_ctor_get(v_nextCmdSnap_x3f_574_, 0);
lean_inc(v_val_576_);
lean_dec_ref(v_nextCmdSnap_x3f_574_);
v_task_577_ = lean_ctor_get(v_val_576_, 3);
lean_inc_ref(v_task_577_);
lean_dec(v_val_576_);
v_t_568_ = v_task_577_;
v_commands_569_ = v_commands_575_;
goto _start;
}
else
{
lean_object* v___x_579_; lean_object* v___y_581_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; size_t v_sz_628_; size_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
lean_dec(v_nextCmdSnap_x3f_574_);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
lean_inc_ref(v_initialSnap_567_);
v___x_626_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_initialSnap_567_);
v___x_627_ = l_Lean_Language_SnapshotTree_getAll(v___x_626_);
v_sz_628_ = lean_array_size(v___x_627_);
v___x_629_ = ((size_t)0ULL);
v___x_630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_sz_628_, v___x_629_, v___x_627_);
v___x_631_ = lean_array_get_size(v___x_630_);
v___x_632_ = lean_nat_dec_lt(v___x_579_, v___x_631_);
if (v___x_632_ == 0)
{
lean_dec_ref(v___x_630_);
v___y_581_ = v___x_625_;
goto v___jp_580_;
}
else
{
uint8_t v___x_633_; 
v___x_633_ = lean_nat_dec_le(v___x_631_, v___x_631_);
if (v___x_633_ == 0)
{
if (v___x_632_ == 0)
{
lean_dec_ref(v___x_630_);
v___y_581_ = v___x_625_;
goto v___jp_580_;
}
else
{
size_t v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_usize_of_nat(v___x_631_);
v___x_635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v___x_630_, v___x_629_, v___x_634_, v___x_625_);
lean_dec_ref(v___x_630_);
v___y_581_ = v___x_635_;
goto v___jp_580_;
}
}
else
{
size_t v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_usize_of_nat(v___x_631_);
v___x_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v___x_630_, v___x_629_, v___x_636_, v___x_625_);
lean_dec_ref(v___x_630_);
v___y_581_ = v___x_637_;
goto v___jp_580_;
}
}
v___jp_580_:
{
size_t v_sz_582_; lean_object* v_resultSnap_583_; lean_object* v___x_584_; lean_object* v_cmdState_585_; lean_object* v_infoState_586_; lean_object* v_env_587_; lean_object* v_scopes_588_; lean_object* v_usedQuotCtxts_589_; lean_object* v_nextMacroScope_590_; lean_object* v_maxRecDepth_591_; lean_object* v_ngen_592_; lean_object* v_auxDeclNGen_593_; lean_object* v_traceState_594_; lean_object* v_snapshotTasks_595_; lean_object* v_newDecls_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_623_; 
v_sz_582_ = lean_array_size(v_commands_575_);
v_resultSnap_583_ = lean_ctor_get(v_elabSnap_573_, 2);
lean_inc_ref(v_resultSnap_583_);
lean_dec_ref(v_elabSnap_573_);
v___x_584_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_583_);
v_cmdState_585_ = lean_ctor_get(v___x_584_, 1);
lean_inc_ref(v_cmdState_585_);
lean_dec(v___x_584_);
v_infoState_586_ = lean_ctor_get(v_cmdState_585_, 8);
v_env_587_ = lean_ctor_get(v_cmdState_585_, 0);
v_scopes_588_ = lean_ctor_get(v_cmdState_585_, 2);
v_usedQuotCtxts_589_ = lean_ctor_get(v_cmdState_585_, 3);
v_nextMacroScope_590_ = lean_ctor_get(v_cmdState_585_, 4);
v_maxRecDepth_591_ = lean_ctor_get(v_cmdState_585_, 5);
v_ngen_592_ = lean_ctor_get(v_cmdState_585_, 6);
v_auxDeclNGen_593_ = lean_ctor_get(v_cmdState_585_, 7);
v_traceState_594_ = lean_ctor_get(v_cmdState_585_, 9);
v_snapshotTasks_595_ = lean_ctor_get(v_cmdState_585_, 10);
v_newDecls_596_ = lean_ctor_get(v_cmdState_585_, 11);
v_isSharedCheck_623_ = !lean_is_exclusive(v_cmdState_585_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; 
v_unused_624_ = lean_ctor_get(v_cmdState_585_, 1);
lean_dec(v_unused_624_);
v___x_598_ = v_cmdState_585_;
v_isShared_599_ = v_isSharedCheck_623_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_newDecls_596_);
lean_inc(v_snapshotTasks_595_);
lean_inc(v_traceState_594_);
lean_inc(v_infoState_586_);
lean_inc(v_auxDeclNGen_593_);
lean_inc(v_ngen_592_);
lean_inc(v_maxRecDepth_591_);
lean_inc(v_nextMacroScope_590_);
lean_inc(v_usedQuotCtxts_589_);
lean_inc(v_scopes_588_);
lean_inc(v_env_587_);
lean_dec(v_cmdState_585_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_623_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
uint8_t v_enabled_600_; lean_object* v_assignment_601_; lean_object* v_lazyAssignment_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_621_; 
v_enabled_600_ = lean_ctor_get_uint8(v_infoState_586_, sizeof(void*)*3);
v_assignment_601_ = lean_ctor_get(v_infoState_586_, 0);
v_lazyAssignment_602_ = lean_ctor_get(v_infoState_586_, 1);
v_isSharedCheck_621_ = !lean_is_exclusive(v_infoState_586_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v_infoState_586_, 2);
lean_dec(v_unused_622_);
v___x_604_ = v_infoState_586_;
v_isShared_605_ = v_isSharedCheck_621_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_lazyAssignment_602_);
lean_inc(v_assignment_601_);
lean_dec(v_infoState_586_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_621_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_pos_606_; size_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_trees_611_; lean_object* v___x_613_; 
v_pos_606_ = lean_ctor_get(v_parserState_572_, 0);
lean_inc(v_pos_606_);
v___x_607_ = ((size_t)0ULL);
lean_inc_ref(v_commands_575_);
v___x_608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_582_, v___x_607_, v_commands_575_);
v___x_609_ = lean_array_get_size(v___x_608_);
v___x_610_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v___x_608_, v___x_579_, v___x_609_);
lean_dec_ref(v___x_608_);
v_trees_611_ = l_Array_toPArray_x27___redArg(v___x_610_);
lean_dec_ref(v___x_610_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 2, v_trees_611_);
v___x_613_ = v___x_604_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_assignment_601_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_lazyAssignment_602_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_trees_611_);
lean_ctor_set_uint8(v_reuseFailAlloc_620_, sizeof(void*)*3, v_enabled_600_);
v___x_613_ = v_reuseFailAlloc_620_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 8, v___x_613_);
lean_ctor_set(v___x_598_, 1, v___y_581_);
v___x_615_ = v___x_598_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_env_587_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___y_581_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_scopes_588_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_usedQuotCtxts_589_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v_nextMacroScope_590_);
lean_ctor_set(v_reuseFailAlloc_619_, 5, v_maxRecDepth_591_);
lean_ctor_set(v_reuseFailAlloc_619_, 6, v_ngen_592_);
lean_ctor_set(v_reuseFailAlloc_619_, 7, v_auxDeclNGen_593_);
lean_ctor_set(v_reuseFailAlloc_619_, 8, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_619_, 9, v_traceState_594_);
lean_ctor_set(v_reuseFailAlloc_619_, 10, v_snapshotTasks_595_);
lean_ctor_set(v_reuseFailAlloc_619_, 11, v_newDecls_596_);
v___x_615_ = v_reuseFailAlloc_619_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_582_, v___x_607_, v_commands_575_);
v___x_617_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v_parserState_572_);
lean_ctor_set(v___x_617_, 2, v_pos_606_);
lean_ctor_set(v___x_617_, 3, v___x_616_);
v___x_618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v_inputCtx_566_);
lean_ctor_set(v___x_618_, 2, v_initialSnap_567_);
return v___x_618_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___boxed(lean_object* v_inputCtx_638_, lean_object* v_initialSnap_639_, lean_object* v_t_640_, lean_object* v_commands_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_638_, v_initialSnap_639_, v_t_640_, v_commands_641_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object* v_inputCtx_646_, lean_object* v_parserState_647_, lean_object* v_commandState_648_, lean_object* v_old_x3f_649_){
_start:
{
lean_object* v___y_652_; 
if (lean_obj_tag(v_old_x3f_649_) == 0)
{
lean_object* v___x_657_; 
v___x_657_ = lean_box(0);
v___y_652_ = v___x_657_;
goto v___jp_651_;
}
else
{
lean_object* v_val_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_668_; 
v_val_658_ = lean_ctor_get(v_old_x3f_649_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v_old_x3f_649_);
if (v_isSharedCheck_668_ == 0)
{
v___x_660_ = v_old_x3f_649_;
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_val_658_);
lean_dec(v_old_x3f_649_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_668_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_inputCtx_662_; lean_object* v_initialSnap_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v_inputCtx_662_ = lean_ctor_get(v_val_658_, 1);
lean_inc_ref(v_inputCtx_662_);
v_initialSnap_663_ = lean_ctor_get(v_val_658_, 2);
lean_inc_ref(v_initialSnap_663_);
lean_dec(v_val_658_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v_inputCtx_662_);
lean_ctor_set(v___x_664_, 1, v_initialSnap_663_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_664_);
v___x_666_ = v___x_660_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
v___y_652_ = v___x_666_;
goto v___jp_651_;
}
}
}
v___jp_651_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = l_Lean_Language_Lean_processCommands(v_inputCtx_646_, v_parserState_647_, v_commandState_648_, v___y_652_);
lean_inc_ref(v___x_653_);
v___x_654_ = lean_task_get_own(v___x_653_);
v___x_655_ = ((lean_object*)(l_Lean_Elab_IO_processCommandsIncrementally___closed__0));
v___x_656_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_646_, v___x_654_, v___x_653_, v___x_655_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally___boxed(lean_object* v_inputCtx_669_, lean_object* v_parserState_670_, lean_object* v_commandState_671_, lean_object* v_old_x3f_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_669_, v_parserState_670_, v_commandState_671_, v_old_x3f_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object* v_inputCtx_675_, lean_object* v_parserState_676_, lean_object* v_commandState_677_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v_toState_681_; lean_object* v___x_682_; 
v___x_679_ = lean_box(0);
v___x_680_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_675_, v_parserState_676_, v_commandState_677_, v___x_679_);
v_toState_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc_ref(v_toState_681_);
lean_dec_ref(v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v_toState_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands___boxed(lean_object* v_inputCtx_683_, lean_object* v_parserState_684_, lean_object* v_commandState_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Elab_IO_processCommands(v_inputCtx_683_, v_parserState_684_, v_commandState_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object* v_input_693_, lean_object* v_env_694_, lean_object* v_opts_695_, lean_object* v_fileName_696_){
_start:
{
lean_object* v___y_699_; 
if (lean_obj_tag(v_fileName_696_) == 0)
{
lean_object* v___x_719_; 
v___x_719_ = ((lean_object*)(l_Lean_Elab_process___closed__1));
v___y_699_ = v___x_719_;
goto v___jp_698_;
}
else
{
lean_object* v_val_720_; 
v_val_720_ = lean_ctor_get(v_fileName_696_, 0);
lean_inc(v_val_720_);
lean_dec_ref(v_fileName_696_);
v___y_699_ = v_val_720_;
goto v___jp_698_;
}
v___jp_698_:
{
uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v_inputCtx_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_718_; 
v___x_700_ = 1;
v___x_701_ = lean_string_utf8_byte_size(v_input_693_);
v_inputCtx_702_ = l_Lean_Parser_mkInputContext___redArg(v_input_693_, v___y_699_, v___x_700_, v___x_701_);
v___x_703_ = ((lean_object*)(l_Lean_Elab_process___closed__0));
v___x_704_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
v___x_705_ = l_Lean_Elab_Command_mkState(v_env_694_, v___x_704_, v_opts_695_);
v___x_706_ = l_Lean_Elab_IO_processCommands(v_inputCtx_702_, v___x_703_, v___x_705_);
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_718_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_718_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_718_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_commandState_711_; lean_object* v_env_712_; lean_object* v_messages_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v_commandState_711_ = lean_ctor_get(v_a_707_, 0);
lean_inc_ref(v_commandState_711_);
lean_dec(v_a_707_);
v_env_712_ = lean_ctor_get(v_commandState_711_, 0);
lean_inc_ref(v_env_712_);
v_messages_713_ = lean_ctor_get(v_commandState_711_, 1);
lean_inc_ref(v_messages_713_);
lean_dec_ref(v_commandState_711_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v_env_712_);
lean_ctor_set(v___x_714_, 1, v_messages_713_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_714_);
v___x_716_ = v___x_709_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process___boxed(lean_object* v_input_721_, lean_object* v_env_722_, lean_object* v_opts_723_, lean_object* v_fileName_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Elab_process(v_input_721_, v_env_722_, v_opts_723_, v_fileName_724_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_opts_727_, lean_object* v_opt_728_){
_start:
{
lean_object* v_name_729_; lean_object* v_map_730_; lean_object* v___x_731_; 
v_name_729_ = lean_ctor_get(v_opt_728_, 0);
v_map_730_ = lean_ctor_get(v_opts_727_, 0);
v___x_731_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_730_, v_name_729_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_box(0);
return v___x_732_;
}
else
{
lean_object* v_val_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_742_; 
v_val_733_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_742_ == 0)
{
v___x_735_ = v___x_731_;
v_isShared_736_ = v_isSharedCheck_742_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_val_733_);
lean_dec(v___x_731_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_742_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
if (lean_obj_tag(v_val_733_) == 0)
{
lean_object* v_v_737_; lean_object* v___x_739_; 
v_v_737_ = lean_ctor_get(v_val_733_, 0);
lean_inc_ref(v_v_737_);
lean_dec_ref(v_val_733_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v_v_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_v_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
else
{
lean_object* v___x_741_; 
lean_del_object(v___x_735_);
lean_dec(v_val_733_);
v___x_741_ = lean_box(0);
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2___boxed(lean_object* v_opts_743_, lean_object* v_opt_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(v_opts_743_, v_opt_744_);
lean_dec_ref(v_opt_744_);
lean_dec_ref(v_opts_743_);
return v_res_745_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_opts_746_, lean_object* v_opt_747_){
_start:
{
lean_object* v_name_748_; lean_object* v_defValue_749_; lean_object* v_map_750_; lean_object* v___x_751_; 
v_name_748_ = lean_ctor_get(v_opt_747_, 0);
v_defValue_749_ = lean_ctor_get(v_opt_747_, 1);
v_map_750_ = lean_ctor_get(v_opts_746_, 0);
v___x_751_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_750_, v_name_748_);
if (lean_obj_tag(v___x_751_) == 0)
{
uint8_t v___x_752_; 
v___x_752_ = lean_unbox(v_defValue_749_);
return v___x_752_;
}
else
{
lean_object* v_val_753_; 
v_val_753_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_val_753_);
lean_dec_ref(v___x_751_);
if (lean_obj_tag(v_val_753_) == 1)
{
uint8_t v_v_754_; 
v_v_754_ = lean_ctor_get_uint8(v_val_753_, 0);
lean_dec_ref(v_val_753_);
return v_v_754_;
}
else
{
uint8_t v___x_755_; 
lean_dec(v_val_753_);
v___x_755_ = lean_unbox(v_defValue_749_);
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_opts_756_, lean_object* v_opt_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(v_opts_756_, v_opt_757_);
lean_dec_ref(v_opt_757_);
lean_dec_ref(v_opts_756_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_hOpt_762_){
_start:
{
lean_inc_ref(v_hOpt_762_);
return v_hOpt_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_hOpt_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_Elab_runFrontend___lam__0(v_x_763_, v_x_764_, v_hOpt_765_);
lean_dec_ref(v_hOpt_765_);
lean_dec_ref(v_x_764_);
lean_dec(v_x_763_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_767_, size_t v_i_768_, size_t v_stop_769_, lean_object* v_b_770_){
_start:
{
uint8_t v___x_772_; 
v___x_772_ = lean_usize_dec_eq(v_i_768_, v_stop_769_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_array_uget_borrowed(v_as_767_, v_i_768_);
lean_inc(v___x_773_);
v___x_774_ = lean_load_dynlib(v___x_773_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; size_t v___x_776_; size_t v___x_777_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref(v___x_774_);
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_add(v_i_768_, v___x_776_);
v_i_768_ = v___x_777_;
v_b_770_ = v_a_775_;
goto _start;
}
else
{
return v___x_774_;
}
}
else
{
lean_object* v___x_779_; 
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v_b_770_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_780_, lean_object* v_i_781_, lean_object* v_stop_782_, lean_object* v_b_783_, lean_object* v___y_784_){
_start:
{
size_t v_i_boxed_785_; size_t v_stop_boxed_786_; lean_object* v_res_787_; 
v_i_boxed_785_ = lean_unbox_usize(v_i_781_);
lean_dec(v_i_781_);
v_stop_boxed_786_ = lean_unbox_usize(v_stop_782_);
lean_dec(v_stop_782_);
v_res_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_780_, v_i_boxed_785_, v_stop_boxed_786_, v_b_783_);
lean_dec_ref(v_as_780_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_setup_x3f_788_, lean_object* v___f_789_, lean_object* v___x_790_, lean_object* v_plugins_791_, uint32_t v_trustLevel_792_, uint8_t v___x_793_, lean_object* v_mainModuleName_794_, lean_object* v_stx_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___y_799_; lean_object* v___y_800_; uint8_t v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; 
if (lean_obj_tag(v_setup_x3f_788_) == 1)
{
lean_object* v_val_812_; lean_object* v_name_813_; lean_object* v_package_x3f_814_; uint8_t v_isModule_815_; lean_object* v_imports_x3f_816_; lean_object* v_importArts_817_; lean_object* v_dynlibs_818_; lean_object* v_plugins_819_; lean_object* v_options_820_; lean_object* v___y_827_; lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
lean_dec(v_mainModuleName_794_);
v_val_812_ = lean_ctor_get(v_setup_x3f_788_, 0);
lean_inc(v_val_812_);
lean_dec_ref(v_setup_x3f_788_);
v_name_813_ = lean_ctor_get(v_val_812_, 0);
lean_inc(v_name_813_);
v_package_x3f_814_ = lean_ctor_get(v_val_812_, 1);
lean_inc(v_package_x3f_814_);
v_isModule_815_ = lean_ctor_get_uint8(v_val_812_, sizeof(void*)*7);
v_imports_x3f_816_ = lean_ctor_get(v_val_812_, 2);
lean_inc(v_imports_x3f_816_);
v_importArts_817_ = lean_ctor_get(v_val_812_, 3);
lean_inc(v_importArts_817_);
v_dynlibs_818_ = lean_ctor_get(v_val_812_, 4);
lean_inc_ref(v_dynlibs_818_);
v_plugins_819_ = lean_ctor_get(v_val_812_, 5);
lean_inc_ref(v_plugins_819_);
v_options_820_ = lean_ctor_get(v_val_812_, 6);
lean_inc(v_options_820_);
lean_dec(v_val_812_);
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_array_get_size(v_dynlibs_818_);
v___x_838_ = lean_nat_dec_lt(v___x_836_, v___x_837_);
if (v___x_838_ == 0)
{
lean_dec_ref(v_dynlibs_818_);
goto v___jp_821_;
}
else
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = lean_box(0);
v___x_840_ = lean_nat_dec_le(v___x_837_, v___x_837_);
if (v___x_840_ == 0)
{
if (v___x_838_ == 0)
{
lean_dec_ref(v_dynlibs_818_);
goto v___jp_821_;
}
else
{
size_t v___x_841_; size_t v___x_842_; lean_object* v___x_843_; 
v___x_841_ = ((size_t)0ULL);
v___x_842_ = lean_usize_of_nat(v___x_837_);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_818_, v___x_841_, v___x_842_, v___x_839_);
lean_dec_ref(v_dynlibs_818_);
v___y_827_ = v___x_843_;
goto v___jp_826_;
}
}
else
{
size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; 
v___x_844_ = ((size_t)0ULL);
v___x_845_ = lean_usize_of_nat(v___x_837_);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_818_, v___x_844_, v___x_845_, v___x_839_);
lean_dec_ref(v_dynlibs_818_);
v___y_827_ = v___x_846_;
goto v___jp_826_;
}
}
v___jp_821_:
{
uint8_t v___x_822_; uint8_t v___x_823_; 
v___x_822_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_795_);
v___x_823_ = lean_strict_or(v_isModule_815_, v___x_822_);
if (lean_obj_tag(v_imports_x3f_816_) == 0)
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_795_, v___x_793_);
v___y_799_ = v_name_813_;
v___y_800_ = v_package_x3f_814_;
v___y_801_ = v___x_823_;
v___y_802_ = v_plugins_819_;
v___y_803_ = v_options_820_;
v___y_804_ = v_importArts_817_;
v___y_805_ = v___x_824_;
goto v___jp_798_;
}
else
{
lean_object* v_val_825_; 
lean_dec(v_stx_795_);
v_val_825_ = lean_ctor_get(v_imports_x3f_816_, 0);
lean_inc(v_val_825_);
lean_dec_ref(v_imports_x3f_816_);
v___y_799_ = v_name_813_;
v___y_800_ = v_package_x3f_814_;
v___y_801_ = v___x_823_;
v___y_802_ = v_plugins_819_;
v___y_803_ = v_options_820_;
v___y_804_ = v_importArts_817_;
v___y_805_ = v_val_825_;
goto v___jp_798_;
}
}
v___jp_826_:
{
if (lean_obj_tag(v___y_827_) == 0)
{
lean_dec_ref(v___y_827_);
goto v___jp_821_;
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec(v_options_820_);
lean_dec_ref(v_plugins_819_);
lean_dec(v_importArts_817_);
lean_dec(v_imports_x3f_816_);
lean_dec(v_package_x3f_814_);
lean_dec(v_name_813_);
lean_dec(v_stx_795_);
lean_dec_ref(v_plugins_791_);
lean_dec_ref(v___x_790_);
lean_dec_ref(v___f_789_);
v_a_828_ = lean_ctor_get(v___y_827_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___y_827_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___y_827_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___y_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
else
{
lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec_ref(v___f_789_);
lean_dec(v_setup_x3f_788_);
v___x_847_ = lean_box(0);
v___x_848_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_795_);
v___x_849_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_795_, v___x_793_);
v___x_850_ = lean_box(1);
v___x_851_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_851_, 0, v_mainModuleName_794_);
lean_ctor_set(v___x_851_, 1, v___x_847_);
lean_ctor_set(v___x_851_, 2, v___x_849_);
lean_ctor_set(v___x_851_, 3, v___x_790_);
lean_ctor_set(v___x_851_, 4, v___x_850_);
lean_ctor_set(v___x_851_, 5, v_plugins_791_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*6 + 4, v___x_848_);
lean_ctor_set_uint32(v___x_851_, sizeof(void*)*6, v_trustLevel_792_);
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
v___jp_798_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_806_ = l_Lean_LeanOptions_toOptions(v___y_803_);
v___x_807_ = l_Lean_Options_mergeBy(v___f_789_, v___x_790_, v___x_806_);
v___x_808_ = l_Array_append___redArg(v_plugins_791_, v___y_802_);
lean_dec_ref(v___y_802_);
v___x_809_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_809_, 0, v___y_799_);
lean_ctor_set(v___x_809_, 1, v___y_800_);
lean_ctor_set(v___x_809_, 2, v___y_805_);
lean_ctor_set(v___x_809_, 3, v___x_807_);
lean_ctor_set(v___x_809_, 4, v___y_804_);
lean_ctor_set(v___x_809_, 5, v___x_808_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*6 + 4, v___y_801_);
lean_ctor_set_uint32(v___x_809_, sizeof(void*)*6, v_trustLevel_792_);
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object* v_setup_x3f_854_, lean_object* v___f_855_, lean_object* v___x_856_, lean_object* v_plugins_857_, lean_object* v_trustLevel_858_, lean_object* v___x_859_, lean_object* v_mainModuleName_860_, lean_object* v_stx_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
uint32_t v_trustLevel_boxed_864_; uint8_t v___x_4824__boxed_865_; lean_object* v_res_866_; 
v_trustLevel_boxed_864_ = lean_unbox_uint32(v_trustLevel_858_);
lean_dec(v_trustLevel_858_);
v___x_4824__boxed_865_ = lean_unbox(v___x_859_);
v_res_866_ = l_Lean_Elab_runFrontend___lam__1(v_setup_x3f_854_, v___f_855_, v___x_856_, v_plugins_857_, v_trustLevel_boxed_864_, v___x_4824__boxed_865_, v_mainModuleName_860_, v_stx_861_, v___y_862_);
lean_dec_ref(v___y_862_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_s_869_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lean_Elab_runFrontend___lam__2___closed__0));
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v_s_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_env_872_, lean_object* v___y_873_, lean_object* v_opts_874_, lean_object* v_val_875_, uint8_t v___x_876_, uint8_t v_a_877_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v___x_879_ = l_Lean_Linter_recordLints(v_env_872_, v___y_873_);
v___x_880_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_881_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(v_opts_874_, v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_writeModule(v___x_879_, v_val_875_, v___x_876_);
return v___x_882_;
}
else
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_writeModule(v___x_879_, v_val_875_, v_a_877_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_env_884_, lean_object* v___y_885_, lean_object* v_opts_886_, lean_object* v_val_887_, lean_object* v___x_888_, lean_object* v_a_889_, lean_object* v___y_890_){
_start:
{
uint8_t v___x_4946__boxed_891_; uint8_t v_a_4947__boxed_892_; lean_object* v_res_893_; 
v___x_4946__boxed_891_ = lean_unbox(v___x_888_);
v_a_4947__boxed_892_ = lean_unbox(v_a_889_);
v_res_893_ = l_Lean_Elab_runFrontend___lam__3(v_env_884_, v___y_885_, v_opts_886_, v_val_887_, v___x_4946__boxed_891_, v_a_4947__boxed_892_);
lean_dec_ref(v_opts_886_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object* v___f_895_, lean_object* v_s_896_){
_start:
{
lean_object* v_toSnapshot_897_; lean_object* v_metaSnap_898_; lean_object* v_result_x3f_899_; lean_object* v___y_901_; 
v_toSnapshot_897_ = lean_ctor_get(v_s_896_, 0);
lean_inc_ref(v_toSnapshot_897_);
v_metaSnap_898_ = lean_ctor_get(v_s_896_, 1);
lean_inc_ref(v_metaSnap_898_);
v_result_x3f_899_ = lean_ctor_get(v_s_896_, 2);
lean_inc(v_result_x3f_899_);
lean_dec_ref(v_s_896_);
if (lean_obj_tag(v_result_x3f_899_) == 0)
{
lean_object* v___x_911_; 
v___x_911_ = lean_box(0);
v___y_901_ = v___x_911_;
goto v___jp_900_;
}
else
{
lean_object* v_val_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_925_; 
v_val_912_ = lean_ctor_get(v_result_x3f_899_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v_result_x3f_899_);
if (v_isSharedCheck_925_ == 0)
{
v___x_914_ = v_result_x3f_899_;
v_isShared_915_ = v_isSharedCheck_925_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_val_912_);
lean_dec(v_result_x3f_899_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_925_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_firstCmdSnap_916_; lean_object* v_stx_x3f_917_; lean_object* v_reportingRange_918_; lean_object* v___x_919_; uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v_firstCmdSnap_916_ = lean_ctor_get(v_val_912_, 1);
lean_inc_ref(v_firstCmdSnap_916_);
lean_dec(v_val_912_);
v_stx_x3f_917_ = lean_ctor_get(v_firstCmdSnap_916_, 0);
lean_inc(v_stx_x3f_917_);
v_reportingRange_918_ = lean_ctor_get(v_firstCmdSnap_916_, 1);
lean_inc(v_reportingRange_918_);
v___x_919_ = ((lean_object*)(l_Lean_Elab_runFrontend___lam__5___closed__0));
v___x_920_ = 1;
v___x_921_ = l_Lean_Language_SnapshotTask_map___redArg(v_firstCmdSnap_916_, v___x_919_, v_stx_x3f_917_, v_reportingRange_918_, v___x_920_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_921_);
v___x_923_ = v___x_914_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
v___y_901_ = v___x_923_;
goto v___jp_900_;
}
}
}
v___jp_900_:
{
lean_object* v_stx_x3f_902_; lean_object* v_reportingRange_903_; uint8_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_stx_x3f_902_ = lean_ctor_get(v_metaSnap_898_, 0);
lean_inc(v_stx_x3f_902_);
v_reportingRange_903_ = lean_ctor_get(v_metaSnap_898_, 1);
lean_inc(v_reportingRange_903_);
v___x_904_ = 1;
v___x_905_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_898_, v___f_895_, v_stx_x3f_902_, v_reportingRange_903_, v___x_904_);
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_mk_empty_array_with_capacity(v___x_906_);
v___x_908_ = lean_array_push(v___x_907_, v___x_905_);
v___x_909_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_901_, v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v_toSnapshot_897_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_929_, lean_object* v_k_930_, uint8_t v_v_931_){
_start:
{
lean_object* v_map_932_; uint8_t v_hasTrace_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_947_; 
v_map_932_ = lean_ctor_get(v_o_929_, 0);
v_hasTrace_933_ = lean_ctor_get_uint8(v_o_929_, sizeof(void*)*1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_o_929_);
if (v_isSharedCheck_947_ == 0)
{
v___x_935_ = v_o_929_;
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_map_932_);
lean_dec(v_o_929_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_947_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_937_, 0, v_v_931_);
lean_inc(v_k_930_);
v___x_938_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_930_, v___x_937_, v_map_932_);
if (v_hasTrace_933_ == 0)
{
lean_object* v___x_939_; uint8_t v___x_940_; lean_object* v___x_942_; 
v___x_939_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_940_ = l_Lean_Name_isPrefixOf(v___x_939_, v_k_930_);
lean_dec(v_k_930_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_938_);
v___x_942_ = v___x_935_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_938_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*1, v___x_940_);
return v___x_942_;
}
}
else
{
lean_object* v___x_945_; 
lean_dec(v_k_930_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_938_);
v___x_945_ = v___x_935_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*1, v_hasTrace_933_);
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
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_948_, lean_object* v_k_949_, lean_object* v_v_950_){
_start:
{
uint8_t v_v_boxed_951_; lean_object* v_res_952_; 
v_v_boxed_951_ = lean_unbox(v_v_950_);
v_res_952_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_948_, v_k_949_, v_v_boxed_951_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_953_, lean_object* v_opt_954_, uint8_t v_val_955_){
_start:
{
lean_object* v_name_956_; lean_object* v___x_957_; 
v_name_956_ = lean_ctor_get(v_opt_954_, 0);
lean_inc(v_name_956_);
lean_dec_ref(v_opt_954_);
v___x_957_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_953_, v_name_956_, v_val_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_958_, lean_object* v_opt_959_, lean_object* v_val_960_){
_start:
{
uint8_t v_val_boxed_961_; lean_object* v_res_962_; 
v_val_boxed_961_ = lean_unbox(v_val_960_);
v_res_962_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_958_, v_opt_959_, v_val_boxed_961_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_963_, lean_object* v_opt_964_, uint8_t v_val_965_){
_start:
{
lean_object* v_name_966_; lean_object* v_map_967_; uint8_t v___x_968_; 
v_name_966_ = lean_ctor_get(v_opt_964_, 0);
v_map_967_ = lean_ctor_get(v_opts_963_, 0);
v___x_968_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_966_, v_map_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_963_, v_opt_964_, v_val_965_);
return v___x_969_;
}
else
{
lean_dec_ref(v_opt_964_);
return v_opts_963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_970_, lean_object* v_opt_971_, lean_object* v_val_972_){
_start:
{
uint8_t v_val_boxed_973_; lean_object* v_res_974_; 
v_val_boxed_973_ = lean_unbox(v_val_972_);
v_res_974_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_970_, v_opt_971_, v_val_boxed_973_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(lean_object* v_as_975_, size_t v_i_976_, size_t v_stop_977_, lean_object* v_b_978_){
_start:
{
lean_object* v___y_980_; uint8_t v___x_984_; 
v___x_984_ = lean_usize_dec_eq(v_i_976_, v_stop_977_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v_infoTree_x3f_986_; 
v___x_985_ = lean_array_uget_borrowed(v_as_975_, v_i_976_);
v_infoTree_x3f_986_ = lean_ctor_get(v___x_985_, 2);
if (lean_obj_tag(v_infoTree_x3f_986_) == 1)
{
lean_object* v_val_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_val_987_ = lean_ctor_get(v_infoTree_x3f_986_, 0);
v___x_988_ = lean_unsigned_to_nat(1u);
v___x_989_ = lean_mk_empty_array_with_capacity(v___x_988_);
lean_inc(v_val_987_);
v___x_990_ = lean_array_push(v___x_989_, v_val_987_);
v___x_991_ = l_Array_append___redArg(v_b_978_, v___x_990_);
lean_dec_ref(v___x_990_);
v___y_980_ = v___x_991_;
goto v___jp_979_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_993_ = l_Array_append___redArg(v_b_978_, v___x_992_);
v___y_980_ = v___x_993_;
goto v___jp_979_;
}
}
else
{
return v_b_978_;
}
v___jp_979_:
{
size_t v___x_981_; size_t v___x_982_; 
v___x_981_ = ((size_t)1ULL);
v___x_982_ = lean_usize_add(v_i_976_, v___x_981_);
v_i_976_ = v___x_982_;
v_b_978_ = v___y_980_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_as_994_, lean_object* v_i_995_, lean_object* v_stop_996_, lean_object* v_b_997_){
_start:
{
size_t v_i_boxed_998_; size_t v_stop_boxed_999_; lean_object* v_res_1000_; 
v_i_boxed_998_ = lean_unbox_usize(v_i_995_);
lean_dec(v_i_995_);
v_stop_boxed_999_ = lean_unbox_usize(v_stop_996_);
lean_dec(v_stop_996_);
v_res_1000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(v_as_994_, v_i_boxed_998_, v_stop_boxed_999_, v_b_997_);
lean_dec_ref(v_as_994_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_as_1001_, size_t v_i_1002_, size_t v_stop_1003_, lean_object* v_b_1004_){
_start:
{
uint8_t v___x_1005_; 
v___x_1005_ = lean_usize_dec_eq(v_i_1002_, v_stop_1003_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v_diagnostics_1007_; lean_object* v_msgLog_1008_; lean_object* v___x_1009_; size_t v___x_1010_; size_t v___x_1011_; 
v___x_1006_ = lean_array_uget_borrowed(v_as_1001_, v_i_1002_);
v_diagnostics_1007_ = lean_ctor_get(v___x_1006_, 1);
v_msgLog_1008_ = lean_ctor_get(v_diagnostics_1007_, 0);
lean_inc_ref(v_msgLog_1008_);
v___x_1009_ = l_Lean_MessageLog_append(v_b_1004_, v_msgLog_1008_);
v___x_1010_ = ((size_t)1ULL);
v___x_1011_ = lean_usize_add(v_i_1002_, v___x_1010_);
v_i_1002_ = v___x_1011_;
v_b_1004_ = v___x_1009_;
goto _start;
}
else
{
return v_b_1004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_as_1013_, lean_object* v_i_1014_, lean_object* v_stop_1015_, lean_object* v_b_1016_){
_start:
{
size_t v_i_boxed_1017_; size_t v_stop_boxed_1018_; lean_object* v_res_1019_; 
v_i_boxed_1017_ = lean_unbox_usize(v_i_1014_);
lean_dec(v_i_1014_);
v_stop_boxed_1018_ = lean_unbox_usize(v_stop_1015_);
lean_dec(v_stop_1015_);
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v_as_1013_, v_i_boxed_1017_, v_stop_boxed_1018_, v_b_1016_);
lean_dec_ref(v_as_1013_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(size_t v_sz_1020_, size_t v_i_1021_, lean_object* v_bs_1022_){
_start:
{
uint8_t v___x_1023_; 
v___x_1023_ = lean_usize_dec_lt(v_i_1021_, v_sz_1020_);
if (v___x_1023_ == 0)
{
return v_bs_1022_;
}
else
{
lean_object* v_v_1024_; lean_object* v_traces_1025_; lean_object* v___x_1026_; lean_object* v_bs_x27_1027_; size_t v___x_1028_; size_t v___x_1029_; lean_object* v___x_1030_; 
v_v_1024_ = lean_array_uget_borrowed(v_bs_1022_, v_i_1021_);
v_traces_1025_ = lean_ctor_get(v_v_1024_, 3);
lean_inc_ref(v_traces_1025_);
v___x_1026_ = lean_unsigned_to_nat(0u);
v_bs_x27_1027_ = lean_array_uset(v_bs_1022_, v_i_1021_, v___x_1026_);
v___x_1028_ = ((size_t)1ULL);
v___x_1029_ = lean_usize_add(v_i_1021_, v___x_1028_);
v___x_1030_ = lean_array_uset(v_bs_x27_1027_, v_i_1021_, v_traces_1025_);
v_i_1021_ = v___x_1029_;
v_bs_1022_ = v___x_1030_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object* v_sz_1032_, lean_object* v_i_1033_, lean_object* v_bs_1034_){
_start:
{
size_t v_sz_boxed_1035_; size_t v_i_boxed_1036_; lean_object* v_res_1037_; 
v_sz_boxed_1035_ = lean_unbox_usize(v_sz_1032_);
lean_dec(v_sz_1032_);
v_i_boxed_1036_ = lean_unbox_usize(v_i_1033_);
lean_dec(v_i_1033_);
v_res_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_boxed_1035_, v_i_boxed_1036_, v_bs_1034_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_1038_, size_t v_i_1039_, size_t v_stop_1040_, lean_object* v_b_1041_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_usize_dec_eq(v_i_1039_, v_stop_1040_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; 
v___x_1043_ = lean_array_uget_borrowed(v_as_1038_, v_i_1039_);
v___x_1044_ = 2;
v___x_1045_ = lean_box(v___x_1044_);
lean_inc(v___x_1043_);
v___x_1046_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1043_, v___x_1045_, v_b_1041_);
v___x_1047_ = ((size_t)1ULL);
v___x_1048_ = lean_usize_add(v_i_1039_, v___x_1047_);
v_i_1039_ = v___x_1048_;
v_b_1041_ = v___x_1046_;
goto _start;
}
else
{
return v_b_1041_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_1050_, lean_object* v_i_1051_, lean_object* v_stop_1052_, lean_object* v_b_1053_){
_start:
{
size_t v_i_boxed_1054_; size_t v_stop_boxed_1055_; lean_object* v_res_1056_; 
v_i_boxed_1054_ = lean_unbox_usize(v_i_1051_);
lean_dec(v_i_1051_);
v_stop_boxed_1055_ = lean_unbox_usize(v_stop_1052_);
lean_dec(v_stop_1052_);
v_res_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_1050_, v_i_boxed_1054_, v_stop_boxed_1055_, v_b_1053_);
lean_dec_ref(v_as_1050_);
return v_res_1056_;
}
}
static double _init_l_Lean_Elab_runFrontend___closed__2(void){
_start:
{
lean_object* v___x_1059_; double v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(1000000000u);
v___x_1060_ = lean_float_of_nat(v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_1064_, lean_object* v_opts_1065_, lean_object* v_fileName_1066_, lean_object* v_mainModuleName_1067_, uint32_t v_trustLevel_1068_, lean_object* v_oleanFileName_x3f_1069_, lean_object* v_ileanFileName_x3f_1070_, uint8_t v_jsonOutput_1071_, lean_object* v_errorOnKinds_1072_, lean_object* v_plugins_1073_, uint8_t v_printStats_1074_, lean_object* v_setup_x3f_1075_){
_start:
{
lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___x_1083_; lean_object* v___f_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v_toSnapshot_1097_; lean_object* v_metaSnap_1098_; lean_object* v_stx_1099_; lean_object* v_result_x3f_1100_; lean_object* v___f_1101_; lean_object* v___x_1102_; double v___x_1103_; double v___x_1104_; double v___x_1105_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1211_; lean_object* v___y_1212_; uint8_t v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1235_; uint8_t v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; uint8_t v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1298_; 
v___x_1083_ = lean_io_mono_nanos_now();
v___f_1084_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___x_1085_ = 1;
v___x_1086_ = lean_string_utf8_byte_size(v_input_1064_);
v___x_1087_ = l_Lean_Parser_mkInputContext___redArg(v_input_1064_, v_fileName_1066_, v___x_1085_, v___x_1086_);
v___x_1088_ = l_Lean_internal_cmdlineSnapshots;
v___x_1089_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_1065_, v___x_1088_, v___x_1085_);
v___x_1090_ = l_Lean_Elab_async;
v___x_1091_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_1089_, v___x_1090_, v___x_1085_);
v___x_1092_ = lean_box_uint32(v_trustLevel_1068_);
v___x_1093_ = lean_box(v___x_1085_);
lean_inc(v_mainModuleName_1067_);
lean_inc_ref(v___x_1091_);
v___f_1094_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__1___boxed), 10, 7);
lean_closure_set(v___f_1094_, 0, v_setup_x3f_1075_);
lean_closure_set(v___f_1094_, 1, v___f_1084_);
lean_closure_set(v___f_1094_, 2, v___x_1091_);
lean_closure_set(v___f_1094_, 3, v_plugins_1073_);
lean_closure_set(v___f_1094_, 4, v___x_1092_);
lean_closure_set(v___f_1094_, 5, v___x_1093_);
lean_closure_set(v___f_1094_, 6, v_mainModuleName_1067_);
v___x_1095_ = lean_box(0);
v___x_1096_ = l_Lean_Language_Lean_process(v___f_1094_, v___x_1095_, v___x_1087_);
v_toSnapshot_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc_ref(v_toSnapshot_1097_);
v_metaSnap_1098_ = lean_ctor_get(v___x_1096_, 1);
lean_inc_ref(v_metaSnap_1098_);
v_stx_1099_ = lean_ctor_get(v___x_1096_, 3);
lean_inc(v_stx_1099_);
v_result_x3f_1100_ = lean_ctor_get(v___x_1096_, 4);
lean_inc(v_result_x3f_1100_);
v___f_1101_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__1));
v___x_1102_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1103_ = lean_float_of_nat(v___x_1083_);
v___x_1104_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__2, &l_Lean_Elab_runFrontend___closed__2_once, _init_l_Lean_Elab_runFrontend___closed__2);
v___x_1105_ = lean_float_div(v___x_1103_, v___x_1104_);
if (lean_obj_tag(v_result_x3f_1100_) == 0)
{
v___y_1298_ = v___x_1095_;
goto v___jp_1297_;
}
else
{
lean_object* v_val_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1330_; 
v_val_1318_ = lean_ctor_get(v_result_x3f_1100_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_result_x3f_1100_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1320_ = v_result_x3f_1100_;
v_isShared_1321_ = v_isSharedCheck_1330_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_val_1318_);
lean_dec(v_result_x3f_1100_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1330_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v_processedSnap_1322_; lean_object* v_stx_x3f_1323_; lean_object* v_reportingRange_1324_; lean_object* v___f_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v_processedSnap_1322_ = lean_ctor_get(v_val_1318_, 1);
lean_inc_ref(v_processedSnap_1322_);
lean_dec(v_val_1318_);
v_stx_x3f_1323_ = lean_ctor_get(v_processedSnap_1322_, 0);
lean_inc(v_stx_x3f_1323_);
v_reportingRange_1324_ = lean_ctor_get(v_processedSnap_1322_, 1);
lean_inc(v_reportingRange_1324_);
v___f_1325_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__4));
v___x_1326_ = l_Lean_Language_SnapshotTask_map___redArg(v_processedSnap_1322_, v___f_1325_, v_stx_x3f_1323_, v_reportingRange_1324_, v___x_1085_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1326_);
v___x_1328_ = v___x_1320_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
v___y_1298_ = v___x_1328_;
goto v___jp_1297_;
}
}
}
v___jp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_runtime_forget(v___y_1078_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___y_1079_);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
v___jp_1106_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = l_Lean_trace_profiler_output;
v___x_1111_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(v___x_1091_, v___x_1110_);
if (lean_obj_tag(v___x_1111_) == 1)
{
lean_object* v_val_1112_; lean_object* v___x_1113_; size_t v_sz_1114_; size_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec_ref(v___y_1107_);
v_val_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_val_1112_);
lean_dec_ref(v___x_1111_);
lean_inc_ref(v___y_1108_);
v___x_1113_ = l_Lean_Language_SnapshotTree_getAll(v___y_1108_);
v_sz_1114_ = lean_array_size(v___x_1113_);
v___x_1115_ = ((size_t)0ULL);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_1114_, v___x_1115_, v___x_1113_);
v___x_1117_ = l_Lean_Name_toString(v_mainModuleName_1067_, v___x_1085_);
v___x_1118_ = l_Lean_Firefox_Profile_export(v___x_1117_, v___x_1105_, v___x_1116_, v___x_1091_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v___x_1116_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_1119_);
v___x_1121_ = l_Lean_Json_compress(v___x_1120_);
v___x_1122_ = l_IO_FS_writeFile(v_val_1112_, v___x_1121_);
lean_dec_ref(v___x_1121_);
lean_dec(v_val_1112_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_dec_ref(v___x_1122_);
v___y_1078_ = v___y_1108_;
v___y_1079_ = v___y_1109_;
goto v___jp_1077_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v___y_1109_);
lean_dec_ref(v___y_1108_);
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_val_1112_);
lean_dec_ref(v___y_1109_);
lean_dec_ref(v___y_1108_);
v_a_1131_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1118_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1118_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
lean_dec(v___x_1111_);
v___x_1139_ = l_Lean_trace_profiler_serve;
v___x_1140_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(v___y_1107_, v___x_1139_);
lean_dec_ref(v___y_1107_);
if (v___x_1140_ == 0)
{
lean_dec_ref(v___x_1091_);
lean_dec(v_mainModuleName_1067_);
v___y_1078_ = v___y_1108_;
v___y_1079_ = v___y_1109_;
goto v___jp_1077_;
}
else
{
lean_object* v___x_1141_; size_t v_sz_1142_; size_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_inc_ref(v___y_1108_);
v___x_1141_ = l_Lean_Language_SnapshotTree_getAll(v___y_1108_);
v_sz_1142_ = lean_array_size(v___x_1141_);
v___x_1143_ = ((size_t)0ULL);
v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_1142_, v___x_1143_, v___x_1141_);
v___x_1145_ = l_Lean_Name_toString(v_mainModuleName_1067_, v___x_1085_);
v___x_1146_ = l_Lean_Firefox_Profile_export(v___x_1145_, v___x_1105_, v___x_1144_, v___x_1091_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v___x_1144_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref(v___x_1146_);
v___x_1148_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_1147_);
v___x_1149_ = l_Lean_Json_compress(v___x_1148_);
v___x_1150_ = l_Lean_Firefox_Profile_serve(v___x_1149_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_dec_ref(v___x_1150_);
v___y_1078_ = v___y_1108_;
v___y_1079_ = v___y_1109_;
goto v___jp_1077_;
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec_ref(v___y_1109_);
lean_dec_ref(v___y_1108_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v___y_1109_);
lean_dec_ref(v___y_1108_);
v_a_1159_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1146_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1146_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
v___jp_1167_:
{
lean_object* v_fileMap_1173_; uint8_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_fst_1177_; lean_object* v_snd_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_fileMap_1173_ = lean_ctor_get(v___x_1087_, 2);
lean_inc_ref(v_fileMap_1173_);
lean_dec_ref(v___x_1087_);
v___x_1174_ = 0;
v___x_1175_ = l_Lean_Server_findModuleRefs(v_fileMap_1173_, v___y_1172_, v___x_1174_, v___x_1174_);
lean_dec_ref(v___y_1172_);
v___x_1176_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_1175_);
v_fst_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_fst_1177_);
v_snd_1178_ = lean_ctor_get(v___x_1176_, 1);
lean_inc(v_snd_1178_);
lean_dec_ref(v___x_1176_);
v___x_1179_ = lean_unsigned_to_nat(5u);
v___x_1180_ = l_Lean_Server_collectImports(v_stx_1099_);
lean_inc(v_mainModuleName_1067_);
v___x_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v_mainModuleName_1067_);
lean_ctor_set(v___x_1181_, 2, v___x_1180_);
lean_ctor_set(v___x_1181_, 3, v_fst_1177_);
lean_ctor_set(v___x_1181_, 4, v_snd_1178_);
v___x_1182_ = l_Lean_Server_instToJsonIlean_toJson(v___x_1181_);
v___x_1183_ = l_Lean_Json_compress(v___x_1182_);
v___x_1184_ = l_IO_FS_writeFile(v___y_1168_, v___x_1183_);
lean_dec_ref(v___x_1183_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_dec_ref(v___x_1184_);
v___y_1107_ = v___y_1169_;
v___y_1108_ = v___y_1170_;
v___y_1109_ = v___y_1171_;
goto v___jp_1106_;
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec_ref(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec_ref(v___x_1091_);
lean_dec(v_mainModuleName_1067_);
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
v___jp_1193_:
{
if (lean_obj_tag(v_ileanFileName_x3f_1070_) == 1)
{
lean_object* v_val_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_val_1198_ = lean_ctor_get(v_ileanFileName_x3f_1070_, 0);
lean_inc_ref(v___y_1195_);
v___x_1199_ = l_Lean_Language_SnapshotTree_getAll(v___y_1195_);
v___x_1200_ = lean_mk_empty_array_with_capacity(v___y_1196_);
v___x_1201_ = lean_array_get_size(v___x_1199_);
v___x_1202_ = lean_nat_dec_lt(v___y_1196_, v___x_1201_);
lean_dec(v___y_1196_);
if (v___x_1202_ == 0)
{
lean_dec_ref(v___x_1199_);
v___y_1168_ = v_val_1198_;
v___y_1169_ = v___y_1194_;
v___y_1170_ = v___y_1195_;
v___y_1171_ = v___y_1197_;
v___y_1172_ = v___x_1200_;
goto v___jp_1167_;
}
else
{
uint8_t v___x_1203_; 
v___x_1203_ = lean_nat_dec_le(v___x_1201_, v___x_1201_);
if (v___x_1203_ == 0)
{
if (v___x_1202_ == 0)
{
lean_dec_ref(v___x_1199_);
v___y_1168_ = v_val_1198_;
v___y_1169_ = v___y_1194_;
v___y_1170_ = v___y_1195_;
v___y_1171_ = v___y_1197_;
v___y_1172_ = v___x_1200_;
goto v___jp_1167_;
}
else
{
size_t v___x_1204_; size_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = ((size_t)0ULL);
v___x_1205_ = lean_usize_of_nat(v___x_1201_);
v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(v___x_1199_, v___x_1204_, v___x_1205_, v___x_1200_);
lean_dec_ref(v___x_1199_);
v___y_1168_ = v_val_1198_;
v___y_1169_ = v___y_1194_;
v___y_1170_ = v___y_1195_;
v___y_1171_ = v___y_1197_;
v___y_1172_ = v___x_1206_;
goto v___jp_1167_;
}
}
else
{
size_t v___x_1207_; size_t v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = ((size_t)0ULL);
v___x_1208_ = lean_usize_of_nat(v___x_1201_);
v___x_1209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(v___x_1199_, v___x_1207_, v___x_1208_, v___x_1200_);
lean_dec_ref(v___x_1199_);
v___y_1168_ = v_val_1198_;
v___y_1169_ = v___y_1194_;
v___y_1170_ = v___y_1195_;
v___y_1171_ = v___y_1197_;
v___y_1172_ = v___x_1209_;
goto v___jp_1167_;
}
}
}
else
{
lean_dec(v___y_1196_);
lean_dec(v_stx_1099_);
lean_dec_ref(v___x_1087_);
v___y_1107_ = v___y_1194_;
v___y_1108_ = v___y_1195_;
v___y_1109_ = v___y_1197_;
goto v___jp_1106_;
}
}
v___jp_1210_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1221_ = lean_box(v___x_1085_);
v___x_1222_ = lean_box(v___y_1213_);
v___f_1223_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1223_, 0, v___y_1214_);
lean_closure_set(v___f_1223_, 1, v___y_1220_);
lean_closure_set(v___f_1223_, 2, v___y_1211_);
lean_closure_set(v___f_1223_, 3, v___y_1212_);
lean_closure_set(v___f_1223_, 4, v___x_1221_);
lean_closure_set(v___f_1223_, 5, v___x_1222_);
v___x_1224_ = lean_box(0);
v___x_1225_ = l_Lean_profileitIOUnsafe___redArg(v___y_1218_, v___y_1215_, v___f_1223_, v___x_1224_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_dec_ref(v___x_1225_);
v___y_1194_ = v___y_1215_;
v___y_1195_ = v___y_1216_;
v___y_1196_ = v___y_1217_;
v___y_1197_ = v___y_1219_;
goto v___jp_1193_;
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v_stx_1099_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v___x_1087_);
lean_dec(v_mainModuleName_1067_);
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
v___jp_1234_:
{
if (v___y_1240_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_1069_) == 1)
{
lean_object* v_val_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v_val_1242_ = lean_ctor_get(v_oleanFileName_x3f_1069_, 0);
lean_inc(v_val_1242_);
lean_dec_ref(v_oleanFileName_x3f_1069_);
v___x_1243_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__3));
v___x_1244_ = l_Lean_MessageLog_empty;
lean_inc_ref(v___y_1238_);
v___x_1245_ = l_Lean_Language_SnapshotTree_getAll(v___y_1238_);
v___x_1246_ = lean_array_get_size(v___x_1245_);
v___x_1247_ = lean_nat_dec_lt(v___y_1239_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_dec_ref(v___x_1245_);
lean_inc_ref(v___y_1235_);
v___y_1211_ = v___y_1235_;
v___y_1212_ = v_val_1242_;
v___y_1213_ = v___y_1236_;
v___y_1214_ = v___y_1237_;
v___y_1215_ = v___y_1235_;
v___y_1216_ = v___y_1238_;
v___y_1217_ = v___y_1239_;
v___y_1218_ = v___x_1243_;
v___y_1219_ = v___y_1241_;
v___y_1220_ = v___x_1244_;
goto v___jp_1210_;
}
else
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_nat_dec_le(v___x_1246_, v___x_1246_);
if (v___x_1248_ == 0)
{
if (v___x_1247_ == 0)
{
lean_dec_ref(v___x_1245_);
lean_inc_ref(v___y_1235_);
v___y_1211_ = v___y_1235_;
v___y_1212_ = v_val_1242_;
v___y_1213_ = v___y_1236_;
v___y_1214_ = v___y_1237_;
v___y_1215_ = v___y_1235_;
v___y_1216_ = v___y_1238_;
v___y_1217_ = v___y_1239_;
v___y_1218_ = v___x_1243_;
v___y_1219_ = v___y_1241_;
v___y_1220_ = v___x_1244_;
goto v___jp_1210_;
}
else
{
size_t v___x_1249_; size_t v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = ((size_t)0ULL);
v___x_1250_ = lean_usize_of_nat(v___x_1246_);
v___x_1251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v___x_1245_, v___x_1249_, v___x_1250_, v___x_1244_);
lean_dec_ref(v___x_1245_);
lean_inc_ref(v___y_1235_);
v___y_1211_ = v___y_1235_;
v___y_1212_ = v_val_1242_;
v___y_1213_ = v___y_1236_;
v___y_1214_ = v___y_1237_;
v___y_1215_ = v___y_1235_;
v___y_1216_ = v___y_1238_;
v___y_1217_ = v___y_1239_;
v___y_1218_ = v___x_1243_;
v___y_1219_ = v___y_1241_;
v___y_1220_ = v___x_1251_;
goto v___jp_1210_;
}
}
else
{
size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = ((size_t)0ULL);
v___x_1253_ = lean_usize_of_nat(v___x_1246_);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v___x_1245_, v___x_1252_, v___x_1253_, v___x_1244_);
lean_dec_ref(v___x_1245_);
lean_inc_ref(v___y_1235_);
v___y_1211_ = v___y_1235_;
v___y_1212_ = v_val_1242_;
v___y_1213_ = v___y_1236_;
v___y_1214_ = v___y_1237_;
v___y_1215_ = v___y_1235_;
v___y_1216_ = v___y_1238_;
v___y_1217_ = v___y_1239_;
v___y_1218_ = v___x_1243_;
v___y_1219_ = v___y_1241_;
v___y_1220_ = v___x_1254_;
goto v___jp_1210_;
}
}
}
else
{
lean_dec_ref(v___y_1237_);
lean_dec(v_oleanFileName_x3f_1069_);
v___y_1194_ = v___y_1235_;
v___y_1195_ = v___y_1238_;
v___y_1196_ = v___y_1239_;
v___y_1197_ = v___y_1241_;
goto v___jp_1193_;
}
}
else
{
lean_object* v___x_1255_; 
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1235_);
lean_dec(v_stx_1099_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v___x_1087_);
lean_dec(v_oleanFileName_x3f_1069_);
lean_dec(v_mainModuleName_1067_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1095_);
return v___x_1255_;
}
}
v___jp_1256_:
{
lean_object* v___x_1260_; 
lean_inc_ref(v___y_1257_);
v___x_1260_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_1257_, v___x_1091_, v_jsonOutput_1071_, v___y_1259_);
lean_dec(v___y_1259_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1288_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1288_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1288_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___x_1096_);
if (lean_obj_tag(v___x_1265_) == 1)
{
lean_object* v_val_1266_; lean_object* v_env_1267_; lean_object* v_scopes_1268_; lean_object* v___x_1269_; 
lean_del_object(v___x_1263_);
v_val_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_val_1266_);
lean_dec_ref(v___x_1265_);
v_env_1267_ = lean_ctor_get(v_val_1266_, 0);
lean_inc_ref(v_env_1267_);
v_scopes_1268_ = lean_ctor_get(v_val_1266_, 2);
lean_inc(v_scopes_1268_);
lean_dec(v_val_1266_);
lean_inc(v___y_1258_);
v___x_1269_ = l_List_get_x21Internal___redArg(v___x_1102_, v_scopes_1268_, v___y_1258_);
lean_dec(v_scopes_1268_);
if (v_printStats_1074_ == 0)
{
lean_object* v_opts_1270_; uint8_t v___x_1271_; uint8_t v___x_1272_; 
v_opts_1270_ = lean_ctor_get(v___x_1269_, 1);
lean_inc_ref(v_opts_1270_);
lean_dec(v___x_1269_);
v___x_1271_ = lean_unbox(v_a_1261_);
v___x_1272_ = lean_unbox(v_a_1261_);
lean_dec(v_a_1261_);
lean_inc_ref(v_env_1267_);
v___y_1235_ = v_opts_1270_;
v___y_1236_ = v___x_1271_;
v___y_1237_ = v_env_1267_;
v___y_1238_ = v___y_1257_;
v___y_1239_ = v___y_1258_;
v___y_1240_ = v___x_1272_;
v___y_1241_ = v_env_1267_;
goto v___jp_1234_;
}
else
{
lean_object* v_opts_1273_; lean_object* v___x_1274_; 
v_opts_1273_ = lean_ctor_get(v___x_1269_, 1);
lean_inc_ref(v_opts_1273_);
lean_dec(v___x_1269_);
lean_inc_ref(v_env_1267_);
v___x_1274_ = l_Lean_Environment_displayStats(v_env_1267_);
if (lean_obj_tag(v___x_1274_) == 0)
{
uint8_t v___x_1275_; uint8_t v___x_1276_; 
lean_dec_ref(v___x_1274_);
v___x_1275_ = lean_unbox(v_a_1261_);
v___x_1276_ = lean_unbox(v_a_1261_);
lean_dec(v_a_1261_);
lean_inc_ref(v_env_1267_);
v___y_1235_ = v_opts_1273_;
v___y_1236_ = v___x_1275_;
v___y_1237_ = v_env_1267_;
v___y_1238_ = v___y_1257_;
v___y_1239_ = v___y_1258_;
v___y_1240_ = v___x_1276_;
v___y_1241_ = v_env_1267_;
goto v___jp_1234_;
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_opts_1273_);
lean_dec_ref(v_env_1267_);
lean_dec(v_a_1261_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v_stx_1099_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v___x_1087_);
lean_dec(v_oleanFileName_x3f_1069_);
lean_dec(v_mainModuleName_1067_);
v_a_1277_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1274_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1274_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
else
{
lean_object* v___x_1286_; 
lean_dec(v___x_1265_);
lean_dec(v_a_1261_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v_stx_1099_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v___x_1087_);
lean_dec(v_oleanFileName_x3f_1069_);
lean_dec(v_mainModuleName_1067_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1095_);
v___x_1286_ = v___x_1263_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1095_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v_stx_1099_);
lean_dec_ref(v___x_1096_);
lean_dec_ref(v___x_1091_);
lean_dec_ref(v___x_1087_);
lean_dec(v_oleanFileName_x3f_1069_);
lean_dec(v_mainModuleName_1067_);
v_a_1289_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1260_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1260_);
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
v___jp_1297_:
{
lean_object* v_stx_x3f_1299_; lean_object* v_reportingRange_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_stx_x3f_1299_ = lean_ctor_get(v_metaSnap_1098_, 0);
lean_inc(v_stx_x3f_1299_);
v_reportingRange_1300_ = lean_ctor_get(v_metaSnap_1098_, 1);
lean_inc(v_reportingRange_1300_);
v___x_1301_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_1098_, v___f_1101_, v_stx_x3f_1299_, v_reportingRange_1300_, v___x_1085_);
v___x_1302_ = lean_unsigned_to_nat(1u);
v___x_1303_ = lean_mk_empty_array_with_capacity(v___x_1302_);
v___x_1304_ = lean_array_push(v___x_1303_, v___x_1301_);
v___x_1305_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_1298_, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v_toSnapshot_1097_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_box(1);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_array_get_size(v_errorOnKinds_1072_);
v___x_1310_ = lean_nat_dec_lt(v___x_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
v___y_1257_ = v___x_1306_;
v___y_1258_ = v___x_1308_;
v___y_1259_ = v___x_1307_;
goto v___jp_1256_;
}
else
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_nat_dec_le(v___x_1309_, v___x_1309_);
if (v___x_1311_ == 0)
{
if (v___x_1310_ == 0)
{
v___y_1257_ = v___x_1306_;
v___y_1258_ = v___x_1308_;
v___y_1259_ = v___x_1307_;
goto v___jp_1256_;
}
else
{
size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = lean_usize_of_nat(v___x_1309_);
v___x_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_errorOnKinds_1072_, v___x_1312_, v___x_1313_, v___x_1307_);
v___y_1257_ = v___x_1306_;
v___y_1258_ = v___x_1308_;
v___y_1259_ = v___x_1314_;
goto v___jp_1256_;
}
}
else
{
size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = lean_usize_of_nat(v___x_1309_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_errorOnKinds_1072_, v___x_1315_, v___x_1316_, v___x_1307_);
v___y_1257_ = v___x_1306_;
v___y_1258_ = v___x_1308_;
v___y_1259_ = v___x_1317_;
goto v___jp_1256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_1331_, lean_object* v_opts_1332_, lean_object* v_fileName_1333_, lean_object* v_mainModuleName_1334_, lean_object* v_trustLevel_1335_, lean_object* v_oleanFileName_x3f_1336_, lean_object* v_ileanFileName_x3f_1337_, lean_object* v_jsonOutput_1338_, lean_object* v_errorOnKinds_1339_, lean_object* v_plugins_1340_, lean_object* v_printStats_1341_, lean_object* v_setup_x3f_1342_, lean_object* v_a_1343_){
_start:
{
uint32_t v_trustLevel_boxed_1344_; uint8_t v_jsonOutput_boxed_1345_; uint8_t v_printStats_boxed_1346_; lean_object* v_res_1347_; 
v_trustLevel_boxed_1344_ = lean_unbox_uint32(v_trustLevel_1335_);
lean_dec(v_trustLevel_1335_);
v_jsonOutput_boxed_1345_ = lean_unbox(v_jsonOutput_1338_);
v_printStats_boxed_1346_ = lean_unbox(v_printStats_1341_);
v_res_1347_ = l_Lean_Elab_runFrontend(v_input_1331_, v_opts_1332_, v_fileName_1333_, v_mainModuleName_1334_, v_trustLevel_boxed_1344_, v_oleanFileName_x3f_1336_, v_ileanFileName_x3f_1337_, v_jsonOutput_boxed_1345_, v_errorOnKinds_1339_, v_plugins_1340_, v_printStats_boxed_1346_, v_setup_x3f_1342_);
lean_dec_ref(v_errorOnKinds_1339_);
lean_dec(v_ileanFileName_x3f_1337_);
return v_res_1347_;
}
}
lean_object* runtime_initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_References(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Profiler(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_PersistentLintLog(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ProfilerServer(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
lean_object* initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* initialize_Lean_Server_References(uint8_t builtin);
lean_object* initialize_Lean_Util_Profiler(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* initialize_Lean_Linter_PersistentLintLog(uint8_t builtin);
lean_object* initialize_Lean_Util_ProfilerServer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
