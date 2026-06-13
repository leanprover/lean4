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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_load_dynlib(lean_object*);
size_t lean_usize_add(size_t, size_t);
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
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_opts_728_, lean_object* v_opt_729_){
_start:
{
lean_object* v_name_730_; lean_object* v_map_731_; lean_object* v___x_732_; 
v_name_730_ = lean_ctor_get(v_opt_729_, 0);
v_map_731_ = lean_ctor_get(v_opts_728_, 0);
v___x_732_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_731_, v_name_730_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v___x_733_; 
v___x_733_ = lean_box(0);
return v___x_733_;
}
else
{
lean_object* v_val_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_743_; 
v_val_734_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_743_ == 0)
{
v___x_736_ = v___x_732_;
v_isShared_737_ = v_isSharedCheck_743_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_val_734_);
lean_dec(v___x_732_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_743_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
if (lean_obj_tag(v_val_734_) == 0)
{
lean_object* v_v_738_; lean_object* v___x_740_; 
v_v_738_ = lean_ctor_get(v_val_734_, 0);
lean_inc_ref(v_v_738_);
lean_dec_ref_known(v_val_734_, 1);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v_v_738_);
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_v_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
else
{
lean_object* v___x_742_; 
lean_del_object(v___x_736_);
lean_dec(v_val_734_);
v___x_742_ = lean_box(0);
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2___boxed(lean_object* v_opts_744_, lean_object* v_opt_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(v_opts_744_, v_opt_745_);
lean_dec_ref(v_opt_745_);
lean_dec_ref(v_opts_744_);
return v_res_746_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_opts_747_, lean_object* v_opt_748_){
_start:
{
lean_object* v_name_749_; lean_object* v_defValue_750_; lean_object* v_map_751_; lean_object* v___x_752_; 
v_name_749_ = lean_ctor_get(v_opt_748_, 0);
v_defValue_750_ = lean_ctor_get(v_opt_748_, 1);
v_map_751_ = lean_ctor_get(v_opts_747_, 0);
v___x_752_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_751_, v_name_749_);
if (lean_obj_tag(v___x_752_) == 0)
{
uint8_t v___x_753_; 
v___x_753_ = lean_unbox(v_defValue_750_);
return v___x_753_;
}
else
{
lean_object* v_val_754_; 
v_val_754_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_val_754_);
lean_dec_ref_known(v___x_752_, 1);
if (lean_obj_tag(v_val_754_) == 1)
{
uint8_t v_v_755_; 
v_v_755_ = lean_ctor_get_uint8(v_val_754_, 0);
lean_dec_ref_known(v_val_754_, 0);
return v_v_755_;
}
else
{
uint8_t v___x_756_; 
lean_dec(v_val_754_);
v___x_756_ = lean_unbox(v_defValue_750_);
return v___x_756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_opts_757_, lean_object* v_opt_758_){
_start:
{
uint8_t v_res_759_; lean_object* v_r_760_; 
v_res_759_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(v_opts_757_, v_opt_758_);
lean_dec_ref(v_opt_758_);
lean_dec_ref(v_opts_757_);
v_r_760_ = lean_box(v_res_759_);
return v_r_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_hOpt_763_){
_start:
{
lean_inc_ref(v_hOpt_763_);
return v_hOpt_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_hOpt_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Elab_runFrontend___lam__0(v_x_764_, v_x_765_, v_hOpt_766_);
lean_dec_ref(v_hOpt_766_);
lean_dec_ref(v_x_765_);
lean_dec(v_x_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_768_, size_t v_i_769_, size_t v_stop_770_, lean_object* v_b_771_){
_start:
{
uint8_t v___x_773_; 
v___x_773_ = lean_usize_dec_eq(v_i_769_, v_stop_770_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_array_uget_borrowed(v_as_768_, v_i_769_);
lean_inc(v___x_774_);
v___x_775_ = lean_load_dynlib(v___x_774_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; size_t v___x_777_; size_t v___x_778_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = ((size_t)1ULL);
v___x_778_ = lean_usize_add(v_i_769_, v___x_777_);
v_i_769_ = v___x_778_;
v_b_771_ = v_a_776_;
goto _start;
}
else
{
return v___x_775_;
}
}
else
{
lean_object* v___x_780_; 
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_b_771_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_781_, lean_object* v_i_782_, lean_object* v_stop_783_, lean_object* v_b_784_, lean_object* v___y_785_){
_start:
{
size_t v_i_boxed_786_; size_t v_stop_boxed_787_; lean_object* v_res_788_; 
v_i_boxed_786_ = lean_unbox_usize(v_i_782_);
lean_dec(v_i_782_);
v_stop_boxed_787_ = lean_unbox_usize(v_stop_783_);
lean_dec(v_stop_783_);
v_res_788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_781_, v_i_boxed_786_, v_stop_boxed_787_, v_b_784_);
lean_dec_ref(v_as_781_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_setup_x3f_789_, lean_object* v___f_790_, lean_object* v___x_791_, lean_object* v_plugins_792_, uint32_t v_trustLevel_793_, uint8_t v___x_794_, lean_object* v_mainModuleName_795_, lean_object* v_stx_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___y_800_; lean_object* v___y_801_; uint8_t v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; 
if (lean_obj_tag(v_setup_x3f_789_) == 1)
{
lean_object* v_val_813_; lean_object* v_name_814_; lean_object* v_package_x3f_815_; uint8_t v_isModule_816_; lean_object* v_imports_x3f_817_; lean_object* v_importArts_818_; lean_object* v_dynlibs_819_; lean_object* v_plugins_820_; lean_object* v_options_821_; lean_object* v___y_828_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
lean_dec(v_mainModuleName_795_);
v_val_813_ = lean_ctor_get(v_setup_x3f_789_, 0);
lean_inc(v_val_813_);
lean_dec_ref_known(v_setup_x3f_789_, 1);
v_name_814_ = lean_ctor_get(v_val_813_, 0);
lean_inc(v_name_814_);
v_package_x3f_815_ = lean_ctor_get(v_val_813_, 1);
lean_inc(v_package_x3f_815_);
v_isModule_816_ = lean_ctor_get_uint8(v_val_813_, sizeof(void*)*7);
v_imports_x3f_817_ = lean_ctor_get(v_val_813_, 2);
lean_inc(v_imports_x3f_817_);
v_importArts_818_ = lean_ctor_get(v_val_813_, 3);
lean_inc(v_importArts_818_);
v_dynlibs_819_ = lean_ctor_get(v_val_813_, 4);
lean_inc_ref(v_dynlibs_819_);
v_plugins_820_ = lean_ctor_get(v_val_813_, 5);
lean_inc_ref(v_plugins_820_);
v_options_821_ = lean_ctor_get(v_val_813_, 6);
lean_inc(v_options_821_);
lean_dec(v_val_813_);
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = lean_array_get_size(v_dynlibs_819_);
v___x_839_ = lean_nat_dec_lt(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
lean_dec_ref(v_dynlibs_819_);
goto v___jp_822_;
}
else
{
lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_840_ = lean_box(0);
v___x_841_ = lean_nat_dec_le(v___x_838_, v___x_838_);
if (v___x_841_ == 0)
{
if (v___x_839_ == 0)
{
lean_dec_ref(v_dynlibs_819_);
goto v___jp_822_;
}
else
{
size_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((size_t)0ULL);
v___x_843_ = lean_usize_of_nat(v___x_838_);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_819_, v___x_842_, v___x_843_, v___x_840_);
lean_dec_ref(v_dynlibs_819_);
v___y_828_ = v___x_844_;
goto v___jp_827_;
}
}
else
{
size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
v___x_845_ = ((size_t)0ULL);
v___x_846_ = lean_usize_of_nat(v___x_838_);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_819_, v___x_845_, v___x_846_, v___x_840_);
lean_dec_ref(v_dynlibs_819_);
v___y_828_ = v___x_847_;
goto v___jp_827_;
}
}
v___jp_822_:
{
uint8_t v___x_823_; uint8_t v___x_824_; 
v___x_823_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_796_);
v___x_824_ = lean_strict_or(v_isModule_816_, v___x_823_);
if (lean_obj_tag(v_imports_x3f_817_) == 0)
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_796_, v___x_794_);
v___y_800_ = v_package_x3f_815_;
v___y_801_ = v_options_821_;
v___y_802_ = v___x_824_;
v___y_803_ = v_plugins_820_;
v___y_804_ = v_name_814_;
v___y_805_ = v_importArts_818_;
v___y_806_ = v___x_825_;
goto v___jp_799_;
}
else
{
lean_object* v_val_826_; 
lean_dec(v_stx_796_);
v_val_826_ = lean_ctor_get(v_imports_x3f_817_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v_imports_x3f_817_, 1);
v___y_800_ = v_package_x3f_815_;
v___y_801_ = v_options_821_;
v___y_802_ = v___x_824_;
v___y_803_ = v_plugins_820_;
v___y_804_ = v_name_814_;
v___y_805_ = v_importArts_818_;
v___y_806_ = v_val_826_;
goto v___jp_799_;
}
}
v___jp_827_:
{
if (lean_obj_tag(v___y_828_) == 0)
{
lean_dec_ref_known(v___y_828_, 1);
goto v___jp_822_;
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_options_821_);
lean_dec_ref(v_plugins_820_);
lean_dec(v_importArts_818_);
lean_dec(v_imports_x3f_817_);
lean_dec(v_package_x3f_815_);
lean_dec(v_name_814_);
lean_dec(v_stx_796_);
lean_dec_ref(v_plugins_792_);
lean_dec_ref(v___x_791_);
lean_dec_ref(v___f_790_);
v_a_829_ = lean_ctor_get(v___y_828_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___y_828_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___y_828_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___y_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
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
}
else
{
lean_object* v___x_848_; uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec_ref(v___f_790_);
lean_dec(v_setup_x3f_789_);
v___x_848_ = lean_box(0);
v___x_849_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_796_);
v___x_850_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_796_, v___x_794_);
v___x_851_ = lean_box(1);
v___x_852_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_852_, 0, v_mainModuleName_795_);
lean_ctor_set(v___x_852_, 1, v___x_848_);
lean_ctor_set(v___x_852_, 2, v___x_850_);
lean_ctor_set(v___x_852_, 3, v___x_791_);
lean_ctor_set(v___x_852_, 4, v___x_851_);
lean_ctor_set(v___x_852_, 5, v_plugins_792_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*6 + 4, v___x_849_);
lean_ctor_set_uint32(v___x_852_, sizeof(void*)*6, v_trustLevel_793_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
v___jp_799_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_807_ = l_Lean_LeanOptions_toOptions(v___y_801_);
v___x_808_ = l_Lean_Options_mergeBy(v___f_790_, v___x_791_, v___x_807_);
v___x_809_ = l_Array_append___redArg(v_plugins_792_, v___y_803_);
lean_dec_ref(v___y_803_);
v___x_810_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_810_, 0, v___y_804_);
lean_ctor_set(v___x_810_, 1, v___y_800_);
lean_ctor_set(v___x_810_, 2, v___y_806_);
lean_ctor_set(v___x_810_, 3, v___x_808_);
lean_ctor_set(v___x_810_, 4, v___y_805_);
lean_ctor_set(v___x_810_, 5, v___x_809_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*6 + 4, v___y_802_);
lean_ctor_set_uint32(v___x_810_, sizeof(void*)*6, v_trustLevel_793_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object* v_setup_x3f_855_, lean_object* v___f_856_, lean_object* v___x_857_, lean_object* v_plugins_858_, lean_object* v_trustLevel_859_, lean_object* v___x_860_, lean_object* v_mainModuleName_861_, lean_object* v_stx_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
uint32_t v_trustLevel_boxed_865_; uint8_t v___x_4824__boxed_866_; lean_object* v_res_867_; 
v_trustLevel_boxed_865_ = lean_unbox_uint32(v_trustLevel_859_);
lean_dec(v_trustLevel_859_);
v___x_4824__boxed_866_ = lean_unbox(v___x_860_);
v_res_867_ = l_Lean_Elab_runFrontend___lam__1(v_setup_x3f_855_, v___f_856_, v___x_857_, v_plugins_858_, v_trustLevel_boxed_865_, v___x_4824__boxed_866_, v_mainModuleName_861_, v_stx_862_, v___y_863_);
lean_dec_ref(v___y_863_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_s_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l_Lean_Elab_runFrontend___lam__2___closed__0));
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_s_870_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_env_873_, lean_object* v___y_874_, lean_object* v_opts_875_, lean_object* v_val_876_, uint8_t v___x_877_, uint8_t v_a_878_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_880_ = l_Lean_Linter_recordLints(v_env_873_, v___y_874_);
v___x_881_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_882_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(v_opts_875_, v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_writeModule(v___x_880_, v_val_876_, v___x_877_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_writeModule(v___x_880_, v_val_876_, v_a_878_);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_env_885_, lean_object* v___y_886_, lean_object* v_opts_887_, lean_object* v_val_888_, lean_object* v___x_889_, lean_object* v_a_890_, lean_object* v___y_891_){
_start:
{
uint8_t v___x_4946__boxed_892_; uint8_t v_a_4947__boxed_893_; lean_object* v_res_894_; 
v___x_4946__boxed_892_ = lean_unbox(v___x_889_);
v_a_4947__boxed_893_ = lean_unbox(v_a_890_);
v_res_894_ = l_Lean_Elab_runFrontend___lam__3(v_env_885_, v___y_886_, v_opts_887_, v_val_888_, v___x_4946__boxed_892_, v_a_4947__boxed_893_);
lean_dec_ref(v_opts_887_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object* v___f_896_, lean_object* v_s_897_){
_start:
{
lean_object* v_toSnapshot_898_; lean_object* v_metaSnap_899_; lean_object* v_result_x3f_900_; lean_object* v___y_902_; 
v_toSnapshot_898_ = lean_ctor_get(v_s_897_, 0);
lean_inc_ref(v_toSnapshot_898_);
v_metaSnap_899_ = lean_ctor_get(v_s_897_, 1);
lean_inc_ref(v_metaSnap_899_);
v_result_x3f_900_ = lean_ctor_get(v_s_897_, 2);
lean_inc(v_result_x3f_900_);
lean_dec_ref(v_s_897_);
if (lean_obj_tag(v_result_x3f_900_) == 0)
{
lean_object* v___x_912_; 
v___x_912_ = lean_box(0);
v___y_902_ = v___x_912_;
goto v___jp_901_;
}
else
{
lean_object* v_val_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_926_; 
v_val_913_ = lean_ctor_get(v_result_x3f_900_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v_result_x3f_900_);
if (v_isSharedCheck_926_ == 0)
{
v___x_915_ = v_result_x3f_900_;
v_isShared_916_ = v_isSharedCheck_926_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_val_913_);
lean_dec(v_result_x3f_900_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_926_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v_firstCmdSnap_917_; lean_object* v_stx_x3f_918_; lean_object* v_reportingRange_919_; lean_object* v___x_920_; uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v_firstCmdSnap_917_ = lean_ctor_get(v_val_913_, 1);
lean_inc_ref(v_firstCmdSnap_917_);
lean_dec(v_val_913_);
v_stx_x3f_918_ = lean_ctor_get(v_firstCmdSnap_917_, 0);
lean_inc(v_stx_x3f_918_);
v_reportingRange_919_ = lean_ctor_get(v_firstCmdSnap_917_, 1);
lean_inc(v_reportingRange_919_);
v___x_920_ = ((lean_object*)(l_Lean_Elab_runFrontend___lam__5___closed__0));
v___x_921_ = 1;
v___x_922_ = l_Lean_Language_SnapshotTask_map___redArg(v_firstCmdSnap_917_, v___x_920_, v_stx_x3f_918_, v_reportingRange_919_, v___x_921_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_922_);
v___x_924_ = v___x_915_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
v___y_902_ = v___x_924_;
goto v___jp_901_;
}
}
}
v___jp_901_:
{
lean_object* v_stx_x3f_903_; lean_object* v_reportingRange_904_; uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_stx_x3f_903_ = lean_ctor_get(v_metaSnap_899_, 0);
lean_inc(v_stx_x3f_903_);
v_reportingRange_904_ = lean_ctor_get(v_metaSnap_899_, 1);
lean_inc(v_reportingRange_904_);
v___x_905_ = 1;
v___x_906_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_899_, v___f_896_, v_stx_x3f_903_, v_reportingRange_904_, v___x_905_);
v___x_907_ = lean_unsigned_to_nat(1u);
v___x_908_ = lean_mk_empty_array_with_capacity(v___x_907_);
v___x_909_ = lean_array_push(v___x_908_, v___x_906_);
v___x_910_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_902_, v___x_909_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_toSnapshot_898_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_930_, lean_object* v_k_931_, uint8_t v_v_932_){
_start:
{
lean_object* v_map_933_; uint8_t v_hasTrace_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_948_; 
v_map_933_ = lean_ctor_get(v_o_930_, 0);
v_hasTrace_934_ = lean_ctor_get_uint8(v_o_930_, sizeof(void*)*1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_o_930_);
if (v_isSharedCheck_948_ == 0)
{
v___x_936_ = v_o_930_;
v_isShared_937_ = v_isSharedCheck_948_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_map_933_);
lean_dec(v_o_930_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_948_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_938_, 0, v_v_932_);
lean_inc(v_k_931_);
v___x_939_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_931_, v___x_938_, v_map_933_);
if (v_hasTrace_934_ == 0)
{
lean_object* v___x_940_; uint8_t v___x_941_; lean_object* v___x_943_; 
v___x_940_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_941_ = l_Lean_Name_isPrefixOf(v___x_940_, v_k_931_);
lean_dec(v_k_931_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_939_);
v___x_943_ = v___x_936_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_939_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*1, v___x_941_);
return v___x_943_;
}
}
else
{
lean_object* v___x_946_; 
lean_dec(v_k_931_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_939_);
v___x_946_ = v___x_936_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*1, v_hasTrace_934_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_949_, lean_object* v_k_950_, lean_object* v_v_951_){
_start:
{
uint8_t v_v_boxed_952_; lean_object* v_res_953_; 
v_v_boxed_952_ = lean_unbox(v_v_951_);
v_res_953_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_949_, v_k_950_, v_v_boxed_952_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_954_, lean_object* v_opt_955_, uint8_t v_val_956_){
_start:
{
lean_object* v_name_957_; lean_object* v___x_958_; 
v_name_957_ = lean_ctor_get(v_opt_955_, 0);
lean_inc(v_name_957_);
lean_dec_ref(v_opt_955_);
v___x_958_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_954_, v_name_957_, v_val_956_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_959_, lean_object* v_opt_960_, lean_object* v_val_961_){
_start:
{
uint8_t v_val_boxed_962_; lean_object* v_res_963_; 
v_val_boxed_962_ = lean_unbox(v_val_961_);
v_res_963_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_959_, v_opt_960_, v_val_boxed_962_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_964_, lean_object* v_opt_965_, uint8_t v_val_966_){
_start:
{
lean_object* v_name_967_; lean_object* v_map_968_; uint8_t v___x_969_; 
v_name_967_ = lean_ctor_get(v_opt_965_, 0);
v_map_968_ = lean_ctor_get(v_opts_964_, 0);
v___x_969_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_967_, v_map_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_964_, v_opt_965_, v_val_966_);
return v___x_970_;
}
else
{
lean_dec_ref(v_opt_965_);
return v_opts_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_971_, lean_object* v_opt_972_, lean_object* v_val_973_){
_start:
{
uint8_t v_val_boxed_974_; lean_object* v_res_975_; 
v_val_boxed_974_ = lean_unbox(v_val_973_);
v_res_975_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_971_, v_opt_972_, v_val_boxed_974_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(lean_object* v_as_976_, size_t v_i_977_, size_t v_stop_978_, lean_object* v_b_979_){
_start:
{
lean_object* v___y_981_; uint8_t v___x_985_; 
v___x_985_ = lean_usize_dec_eq(v_i_977_, v_stop_978_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v_infoTree_x3f_987_; 
v___x_986_ = lean_array_uget_borrowed(v_as_976_, v_i_977_);
v_infoTree_x3f_987_ = lean_ctor_get(v___x_986_, 2);
if (lean_obj_tag(v_infoTree_x3f_987_) == 1)
{
lean_object* v_val_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_val_988_ = lean_ctor_get(v_infoTree_x3f_987_, 0);
v___x_989_ = lean_unsigned_to_nat(1u);
v___x_990_ = lean_mk_empty_array_with_capacity(v___x_989_);
lean_inc(v_val_988_);
v___x_991_ = lean_array_push(v___x_990_, v_val_988_);
v___x_992_ = l_Array_append___redArg(v_b_979_, v___x_991_);
lean_dec_ref(v___x_991_);
v___y_981_ = v___x_992_;
goto v___jp_980_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_994_ = l_Array_append___redArg(v_b_979_, v___x_993_);
v___y_981_ = v___x_994_;
goto v___jp_980_;
}
}
else
{
return v_b_979_;
}
v___jp_980_:
{
size_t v___x_982_; size_t v___x_983_; 
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_add(v_i_977_, v___x_982_);
v_i_977_ = v___x_983_;
v_b_979_ = v___y_981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_as_995_, lean_object* v_i_996_, lean_object* v_stop_997_, lean_object* v_b_998_){
_start:
{
size_t v_i_boxed_999_; size_t v_stop_boxed_1000_; lean_object* v_res_1001_; 
v_i_boxed_999_ = lean_unbox_usize(v_i_996_);
lean_dec(v_i_996_);
v_stop_boxed_1000_ = lean_unbox_usize(v_stop_997_);
lean_dec(v_stop_997_);
v_res_1001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(v_as_995_, v_i_boxed_999_, v_stop_boxed_1000_, v_b_998_);
lean_dec_ref(v_as_995_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_as_1002_, size_t v_i_1003_, size_t v_stop_1004_, lean_object* v_b_1005_){
_start:
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_eq(v_i_1003_, v_stop_1004_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v_diagnostics_1008_; lean_object* v_msgLog_1009_; lean_object* v___x_1010_; size_t v___x_1011_; size_t v___x_1012_; 
v___x_1007_ = lean_array_uget_borrowed(v_as_1002_, v_i_1003_);
v_diagnostics_1008_ = lean_ctor_get(v___x_1007_, 1);
v_msgLog_1009_ = lean_ctor_get(v_diagnostics_1008_, 0);
lean_inc_ref(v_msgLog_1009_);
v___x_1010_ = l_Lean_MessageLog_append(v_b_1005_, v_msgLog_1009_);
v___x_1011_ = ((size_t)1ULL);
v___x_1012_ = lean_usize_add(v_i_1003_, v___x_1011_);
v_i_1003_ = v___x_1012_;
v_b_1005_ = v___x_1010_;
goto _start;
}
else
{
return v_b_1005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_as_1014_, lean_object* v_i_1015_, lean_object* v_stop_1016_, lean_object* v_b_1017_){
_start:
{
size_t v_i_boxed_1018_; size_t v_stop_boxed_1019_; lean_object* v_res_1020_; 
v_i_boxed_1018_ = lean_unbox_usize(v_i_1015_);
lean_dec(v_i_1015_);
v_stop_boxed_1019_ = lean_unbox_usize(v_stop_1016_);
lean_dec(v_stop_1016_);
v_res_1020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v_as_1014_, v_i_boxed_1018_, v_stop_boxed_1019_, v_b_1017_);
lean_dec_ref(v_as_1014_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(size_t v_sz_1021_, size_t v_i_1022_, lean_object* v_bs_1023_){
_start:
{
uint8_t v___x_1024_; 
v___x_1024_ = lean_usize_dec_lt(v_i_1022_, v_sz_1021_);
if (v___x_1024_ == 0)
{
return v_bs_1023_;
}
else
{
lean_object* v_v_1025_; lean_object* v_traces_1026_; lean_object* v___x_1027_; lean_object* v_bs_x27_1028_; size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v_v_1025_ = lean_array_uget_borrowed(v_bs_1023_, v_i_1022_);
v_traces_1026_ = lean_ctor_get(v_v_1025_, 3);
lean_inc_ref(v_traces_1026_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v_bs_x27_1028_ = lean_array_uset(v_bs_1023_, v_i_1022_, v___x_1027_);
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_add(v_i_1022_, v___x_1029_);
v___x_1031_ = lean_array_uset(v_bs_x27_1028_, v_i_1022_, v_traces_1026_);
v_i_1022_ = v___x_1030_;
v_bs_1023_ = v___x_1031_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object* v_sz_1033_, lean_object* v_i_1034_, lean_object* v_bs_1035_){
_start:
{
size_t v_sz_boxed_1036_; size_t v_i_boxed_1037_; lean_object* v_res_1038_; 
v_sz_boxed_1036_ = lean_unbox_usize(v_sz_1033_);
lean_dec(v_sz_1033_);
v_i_boxed_1037_ = lean_unbox_usize(v_i_1034_);
lean_dec(v_i_1034_);
v_res_1038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_boxed_1036_, v_i_boxed_1037_, v_bs_1035_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_1039_, size_t v_i_1040_, size_t v_stop_1041_, lean_object* v_b_1042_){
_start:
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_usize_dec_eq(v_i_1040_, v_stop_1041_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; 
v___x_1044_ = lean_array_uget_borrowed(v_as_1039_, v_i_1040_);
v___x_1045_ = 2;
v___x_1046_ = lean_box(v___x_1045_);
lean_inc(v___x_1044_);
v___x_1047_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1044_, v___x_1046_, v_b_1042_);
v___x_1048_ = ((size_t)1ULL);
v___x_1049_ = lean_usize_add(v_i_1040_, v___x_1048_);
v_i_1040_ = v___x_1049_;
v_b_1042_ = v___x_1047_;
goto _start;
}
else
{
return v_b_1042_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_1051_, lean_object* v_i_1052_, lean_object* v_stop_1053_, lean_object* v_b_1054_){
_start:
{
size_t v_i_boxed_1055_; size_t v_stop_boxed_1056_; lean_object* v_res_1057_; 
v_i_boxed_1055_ = lean_unbox_usize(v_i_1052_);
lean_dec(v_i_1052_);
v_stop_boxed_1056_ = lean_unbox_usize(v_stop_1053_);
lean_dec(v_stop_1053_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_1051_, v_i_boxed_1055_, v_stop_boxed_1056_, v_b_1054_);
lean_dec_ref(v_as_1051_);
return v_res_1057_;
}
}
static double _init_l_Lean_Elab_runFrontend___closed__2(void){
_start:
{
lean_object* v___x_1060_; double v___x_1061_; 
v___x_1060_ = lean_unsigned_to_nat(1000000000u);
v___x_1061_ = lean_float_of_nat(v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_1065_, lean_object* v_opts_1066_, lean_object* v_fileName_1067_, lean_object* v_mainModuleName_1068_, uint32_t v_trustLevel_1069_, lean_object* v_oleanFileName_x3f_1070_, lean_object* v_ileanFileName_x3f_1071_, uint8_t v_jsonOutput_1072_, lean_object* v_errorOnKinds_1073_, lean_object* v_plugins_1074_, uint8_t v_printStats_1075_, lean_object* v_setup_x3f_1076_){
_start:
{
lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___x_1084_; lean_object* v___f_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_toSnapshot_1098_; lean_object* v_metaSnap_1099_; lean_object* v_stx_1100_; lean_object* v_result_x3f_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; double v___x_1104_; double v___x_1105_; double v___x_1106_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1212_; lean_object* v___y_1213_; uint8_t v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1236_; lean_object* v___y_1237_; uint8_t v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; uint8_t v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1299_; 
v___x_1084_ = lean_io_mono_nanos_now();
v___f_1085_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___x_1086_ = 1;
v___x_1087_ = lean_string_utf8_byte_size(v_input_1065_);
v___x_1088_ = l_Lean_Parser_mkInputContext___redArg(v_input_1065_, v_fileName_1067_, v___x_1086_, v___x_1087_);
v___x_1089_ = l_Lean_internal_cmdlineSnapshots;
v___x_1090_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_1066_, v___x_1089_, v___x_1086_);
v___x_1091_ = l_Lean_Elab_async;
v___x_1092_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_1090_, v___x_1091_, v___x_1086_);
v___x_1093_ = lean_box_uint32(v_trustLevel_1069_);
v___x_1094_ = lean_box(v___x_1086_);
lean_inc(v_mainModuleName_1068_);
lean_inc_ref(v___x_1092_);
v___f_1095_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__1___boxed), 10, 7);
lean_closure_set(v___f_1095_, 0, v_setup_x3f_1076_);
lean_closure_set(v___f_1095_, 1, v___f_1085_);
lean_closure_set(v___f_1095_, 2, v___x_1092_);
lean_closure_set(v___f_1095_, 3, v_plugins_1074_);
lean_closure_set(v___f_1095_, 4, v___x_1093_);
lean_closure_set(v___f_1095_, 5, v___x_1094_);
lean_closure_set(v___f_1095_, 6, v_mainModuleName_1068_);
v___x_1096_ = lean_box(0);
v___x_1097_ = l_Lean_Language_Lean_process(v___f_1095_, v___x_1096_, v___x_1088_);
v_toSnapshot_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_toSnapshot_1098_);
v_metaSnap_1099_ = lean_ctor_get(v___x_1097_, 1);
lean_inc_ref(v_metaSnap_1099_);
v_stx_1100_ = lean_ctor_get(v___x_1097_, 3);
lean_inc(v_stx_1100_);
v_result_x3f_1101_ = lean_ctor_get(v___x_1097_, 4);
lean_inc(v_result_x3f_1101_);
v___f_1102_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__1));
v___x_1103_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1104_ = lean_float_of_nat(v___x_1084_);
v___x_1105_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__2, &l_Lean_Elab_runFrontend___closed__2_once, _init_l_Lean_Elab_runFrontend___closed__2);
v___x_1106_ = lean_float_div(v___x_1104_, v___x_1105_);
if (lean_obj_tag(v_result_x3f_1101_) == 0)
{
v___y_1299_ = v___x_1096_;
goto v___jp_1298_;
}
else
{
lean_object* v_val_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1331_; 
v_val_1319_ = lean_ctor_get(v_result_x3f_1101_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_result_x3f_1101_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1321_ = v_result_x3f_1101_;
v_isShared_1322_ = v_isSharedCheck_1331_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_val_1319_);
lean_dec(v_result_x3f_1101_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1331_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_processedSnap_1323_; lean_object* v_stx_x3f_1324_; lean_object* v_reportingRange_1325_; lean_object* v___f_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v_processedSnap_1323_ = lean_ctor_get(v_val_1319_, 1);
lean_inc_ref(v_processedSnap_1323_);
lean_dec(v_val_1319_);
v_stx_x3f_1324_ = lean_ctor_get(v_processedSnap_1323_, 0);
lean_inc(v_stx_x3f_1324_);
v_reportingRange_1325_ = lean_ctor_get(v_processedSnap_1323_, 1);
lean_inc(v_reportingRange_1325_);
v___f_1326_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__4));
v___x_1327_ = l_Lean_Language_SnapshotTask_map___redArg(v_processedSnap_1323_, v___f_1326_, v_stx_x3f_1324_, v_reportingRange_1325_, v___x_1086_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1327_);
v___x_1329_ = v___x_1321_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
v___y_1299_ = v___x_1329_;
goto v___jp_1298_;
}
}
}
v___jp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = lean_runtime_forget(v___y_1080_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___y_1079_);
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
v___jp_1107_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = l_Lean_trace_profiler_output;
v___x_1112_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(v___x_1092_, v___x_1111_);
if (lean_obj_tag(v___x_1112_) == 1)
{
lean_object* v_val_1113_; lean_object* v___x_1114_; size_t v_sz_1115_; size_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec_ref(v___y_1109_);
v_val_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_val_1113_);
lean_dec_ref_known(v___x_1112_, 1);
lean_inc_ref(v___y_1110_);
v___x_1114_ = l_Lean_Language_SnapshotTree_getAll(v___y_1110_);
v_sz_1115_ = lean_array_size(v___x_1114_);
v___x_1116_ = ((size_t)0ULL);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_1115_, v___x_1116_, v___x_1114_);
v___x_1118_ = l_Lean_Name_toString(v_mainModuleName_1068_, v___x_1086_);
v___x_1119_ = l_Lean_Firefox_Profile_export(v___x_1118_, v___x_1106_, v___x_1117_, v___x_1092_);
lean_dec_ref(v___x_1092_);
lean_dec_ref(v___x_1117_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_1120_);
v___x_1122_ = l_Lean_Json_compress(v___x_1121_);
v___x_1123_ = l_IO_FS_writeFile(v_val_1113_, v___x_1122_);
lean_dec_ref(v___x_1122_);
lean_dec(v_val_1113_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_dec_ref_known(v___x_1123_, 1);
v___y_1079_ = v___y_1108_;
v___y_1080_ = v___y_1110_;
goto v___jp_1078_;
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___y_1108_);
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_val_1113_);
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___y_1108_);
v_a_1132_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1119_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1119_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
lean_dec(v___x_1112_);
v___x_1140_ = l_Lean_trace_profiler_serve;
v___x_1141_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__4(v___y_1109_, v___x_1140_);
lean_dec_ref(v___y_1109_);
if (v___x_1141_ == 0)
{
lean_dec_ref(v___x_1092_);
lean_dec(v_mainModuleName_1068_);
v___y_1079_ = v___y_1108_;
v___y_1080_ = v___y_1110_;
goto v___jp_1078_;
}
else
{
lean_object* v___x_1142_; size_t v_sz_1143_; size_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_inc_ref(v___y_1110_);
v___x_1142_ = l_Lean_Language_SnapshotTree_getAll(v___y_1110_);
v_sz_1143_ = lean_array_size(v___x_1142_);
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_1143_, v___x_1144_, v___x_1142_);
v___x_1146_ = l_Lean_Name_toString(v_mainModuleName_1068_, v___x_1086_);
v___x_1147_ = l_Lean_Firefox_Profile_export(v___x_1146_, v___x_1106_, v___x_1145_, v___x_1092_);
lean_dec_ref(v___x_1092_);
lean_dec_ref(v___x_1145_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v___x_1149_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_1148_);
v___x_1150_ = l_Lean_Json_compress(v___x_1149_);
v___x_1151_ = l_Lean_Firefox_Profile_serve(v___x_1150_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_dec_ref_known(v___x_1151_, 1);
v___y_1079_ = v___y_1108_;
v___y_1080_ = v___y_1110_;
goto v___jp_1078_;
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___y_1108_);
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v___y_1110_);
lean_dec_ref(v___y_1108_);
v_a_1160_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1147_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1147_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
v___jp_1168_:
{
lean_object* v_fileMap_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_fst_1178_; lean_object* v_snd_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_fileMap_1174_ = lean_ctor_get(v___x_1088_, 2);
lean_inc_ref(v_fileMap_1174_);
lean_dec_ref(v___x_1088_);
v___x_1175_ = 0;
v___x_1176_ = l_Lean_Server_findModuleRefs(v_fileMap_1174_, v___y_1173_, v___x_1175_, v___x_1175_);
lean_dec_ref(v___y_1173_);
v___x_1177_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_1176_);
v_fst_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_fst_1178_);
v_snd_1179_ = lean_ctor_get(v___x_1177_, 1);
lean_inc(v_snd_1179_);
lean_dec_ref(v___x_1177_);
v___x_1180_ = lean_unsigned_to_nat(5u);
v___x_1181_ = l_Lean_Server_collectImports(v_stx_1100_);
lean_inc(v_mainModuleName_1068_);
v___x_1182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v_mainModuleName_1068_);
lean_ctor_set(v___x_1182_, 2, v___x_1181_);
lean_ctor_set(v___x_1182_, 3, v_fst_1178_);
lean_ctor_set(v___x_1182_, 4, v_snd_1179_);
v___x_1183_ = l_Lean_Server_instToJsonIlean_toJson(v___x_1182_);
v___x_1184_ = l_Lean_Json_compress(v___x_1183_);
v___x_1185_ = l_IO_FS_writeFile(v___y_1170_, v___x_1184_);
lean_dec_ref(v___x_1184_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_dec_ref_known(v___x_1185_, 1);
v___y_1108_ = v___y_1169_;
v___y_1109_ = v___y_1171_;
v___y_1110_ = v___y_1172_;
goto v___jp_1107_;
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec_ref(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec_ref(v___y_1169_);
lean_dec_ref(v___x_1092_);
lean_dec(v_mainModuleName_1068_);
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
v___jp_1194_:
{
if (lean_obj_tag(v_ileanFileName_x3f_1071_) == 1)
{
lean_object* v_val_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v_val_1199_ = lean_ctor_get(v_ileanFileName_x3f_1071_, 0);
lean_inc_ref(v___y_1198_);
v___x_1200_ = l_Lean_Language_SnapshotTree_getAll(v___y_1198_);
v___x_1201_ = lean_mk_empty_array_with_capacity(v___y_1196_);
v___x_1202_ = lean_array_get_size(v___x_1200_);
v___x_1203_ = lean_nat_dec_lt(v___y_1196_, v___x_1202_);
lean_dec(v___y_1196_);
if (v___x_1203_ == 0)
{
lean_dec_ref(v___x_1200_);
v___y_1169_ = v___y_1195_;
v___y_1170_ = v_val_1199_;
v___y_1171_ = v___y_1197_;
v___y_1172_ = v___y_1198_;
v___y_1173_ = v___x_1201_;
goto v___jp_1168_;
}
else
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_nat_dec_le(v___x_1202_, v___x_1202_);
if (v___x_1204_ == 0)
{
if (v___x_1203_ == 0)
{
lean_dec_ref(v___x_1200_);
v___y_1169_ = v___y_1195_;
v___y_1170_ = v_val_1199_;
v___y_1171_ = v___y_1197_;
v___y_1172_ = v___y_1198_;
v___y_1173_ = v___x_1201_;
goto v___jp_1168_;
}
else
{
size_t v___x_1205_; size_t v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = ((size_t)0ULL);
v___x_1206_ = lean_usize_of_nat(v___x_1202_);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(v___x_1200_, v___x_1205_, v___x_1206_, v___x_1201_);
lean_dec_ref(v___x_1200_);
v___y_1169_ = v___y_1195_;
v___y_1170_ = v_val_1199_;
v___y_1171_ = v___y_1197_;
v___y_1172_ = v___y_1198_;
v___y_1173_ = v___x_1207_;
goto v___jp_1168_;
}
}
else
{
size_t v___x_1208_; size_t v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = ((size_t)0ULL);
v___x_1209_ = lean_usize_of_nat(v___x_1202_);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__5(v___x_1200_, v___x_1208_, v___x_1209_, v___x_1201_);
lean_dec_ref(v___x_1200_);
v___y_1169_ = v___y_1195_;
v___y_1170_ = v_val_1199_;
v___y_1171_ = v___y_1197_;
v___y_1172_ = v___y_1198_;
v___y_1173_ = v___x_1210_;
goto v___jp_1168_;
}
}
}
else
{
lean_dec(v___y_1196_);
lean_dec(v_stx_1100_);
lean_dec_ref(v___x_1088_);
v___y_1108_ = v___y_1195_;
v___y_1109_ = v___y_1197_;
v___y_1110_ = v___y_1198_;
goto v___jp_1107_;
}
}
v___jp_1211_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1222_ = lean_box(v___x_1086_);
v___x_1223_ = lean_box(v___y_1214_);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1224_, 0, v___y_1212_);
lean_closure_set(v___f_1224_, 1, v___y_1221_);
lean_closure_set(v___f_1224_, 2, v___y_1213_);
lean_closure_set(v___f_1224_, 3, v___y_1215_);
lean_closure_set(v___f_1224_, 4, v___x_1222_);
lean_closure_set(v___f_1224_, 5, v___x_1223_);
v___x_1225_ = lean_box(0);
v___x_1226_ = l_Lean_profileitIOUnsafe___redArg(v___y_1218_, v___y_1219_, v___f_1224_, v___x_1225_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_dec_ref_known(v___x_1226_, 1);
v___y_1195_ = v___y_1216_;
v___y_1196_ = v___y_1217_;
v___y_1197_ = v___y_1219_;
v___y_1198_ = v___y_1220_;
goto v___jp_1194_;
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec_ref(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v_stx_1100_);
lean_dec_ref(v___x_1092_);
lean_dec_ref(v___x_1088_);
lean_dec(v_mainModuleName_1068_);
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
v___jp_1235_:
{
if (v___y_1241_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_1070_) == 1)
{
lean_object* v_val_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_val_1243_ = lean_ctor_get(v_oleanFileName_x3f_1070_, 0);
lean_inc(v_val_1243_);
lean_dec_ref_known(v_oleanFileName_x3f_1070_, 1);
v___x_1244_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__3));
v___x_1245_ = l_Lean_MessageLog_empty;
lean_inc_ref(v___y_1242_);
v___x_1246_ = l_Lean_Language_SnapshotTree_getAll(v___y_1242_);
v___x_1247_ = lean_array_get_size(v___x_1246_);
v___x_1248_ = lean_nat_dec_lt(v___y_1240_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_dec_ref(v___x_1246_);
lean_inc_ref(v___y_1237_);
v___y_1212_ = v___y_1236_;
v___y_1213_ = v___y_1237_;
v___y_1214_ = v___y_1238_;
v___y_1215_ = v_val_1243_;
v___y_1216_ = v___y_1239_;
v___y_1217_ = v___y_1240_;
v___y_1218_ = v___x_1244_;
v___y_1219_ = v___y_1237_;
v___y_1220_ = v___y_1242_;
v___y_1221_ = v___x_1245_;
goto v___jp_1211_;
}
else
{
uint8_t v___x_1249_; 
v___x_1249_ = lean_nat_dec_le(v___x_1247_, v___x_1247_);
if (v___x_1249_ == 0)
{
if (v___x_1248_ == 0)
{
lean_dec_ref(v___x_1246_);
lean_inc_ref(v___y_1237_);
v___y_1212_ = v___y_1236_;
v___y_1213_ = v___y_1237_;
v___y_1214_ = v___y_1238_;
v___y_1215_ = v_val_1243_;
v___y_1216_ = v___y_1239_;
v___y_1217_ = v___y_1240_;
v___y_1218_ = v___x_1244_;
v___y_1219_ = v___y_1237_;
v___y_1220_ = v___y_1242_;
v___y_1221_ = v___x_1245_;
goto v___jp_1211_;
}
else
{
size_t v___x_1250_; size_t v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = ((size_t)0ULL);
v___x_1251_ = lean_usize_of_nat(v___x_1247_);
v___x_1252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v___x_1246_, v___x_1250_, v___x_1251_, v___x_1245_);
lean_dec_ref(v___x_1246_);
lean_inc_ref(v___y_1237_);
v___y_1212_ = v___y_1236_;
v___y_1213_ = v___y_1237_;
v___y_1214_ = v___y_1238_;
v___y_1215_ = v_val_1243_;
v___y_1216_ = v___y_1239_;
v___y_1217_ = v___y_1240_;
v___y_1218_ = v___x_1244_;
v___y_1219_ = v___y_1237_;
v___y_1220_ = v___y_1242_;
v___y_1221_ = v___x_1252_;
goto v___jp_1211_;
}
}
else
{
size_t v___x_1253_; size_t v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = ((size_t)0ULL);
v___x_1254_ = lean_usize_of_nat(v___x_1247_);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v___x_1246_, v___x_1253_, v___x_1254_, v___x_1245_);
lean_dec_ref(v___x_1246_);
lean_inc_ref(v___y_1237_);
v___y_1212_ = v___y_1236_;
v___y_1213_ = v___y_1237_;
v___y_1214_ = v___y_1238_;
v___y_1215_ = v_val_1243_;
v___y_1216_ = v___y_1239_;
v___y_1217_ = v___y_1240_;
v___y_1218_ = v___x_1244_;
v___y_1219_ = v___y_1237_;
v___y_1220_ = v___y_1242_;
v___y_1221_ = v___x_1255_;
goto v___jp_1211_;
}
}
}
else
{
lean_dec_ref(v___y_1236_);
lean_dec(v_oleanFileName_x3f_1070_);
v___y_1195_ = v___y_1239_;
v___y_1196_ = v___y_1240_;
v___y_1197_ = v___y_1237_;
v___y_1198_ = v___y_1242_;
goto v___jp_1194_;
}
}
else
{
lean_object* v___x_1256_; 
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v_stx_1100_);
lean_dec_ref(v___x_1092_);
lean_dec_ref(v___x_1088_);
lean_dec(v_oleanFileName_x3f_1070_);
lean_dec(v_mainModuleName_1068_);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1096_);
return v___x_1256_;
}
}
v___jp_1257_:
{
lean_object* v___x_1261_; 
lean_inc_ref(v___y_1259_);
v___x_1261_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_1259_, v___x_1092_, v_jsonOutput_1072_, v___y_1260_);
lean_dec(v___y_1260_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1289_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1289_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1289_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___x_1097_);
if (lean_obj_tag(v___x_1266_) == 1)
{
lean_object* v_val_1267_; lean_object* v_env_1268_; lean_object* v_scopes_1269_; lean_object* v___x_1270_; 
lean_del_object(v___x_1264_);
v_val_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_val_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v_env_1268_ = lean_ctor_get(v_val_1267_, 0);
lean_inc_ref(v_env_1268_);
v_scopes_1269_ = lean_ctor_get(v_val_1267_, 2);
lean_inc(v_scopes_1269_);
lean_dec(v_val_1267_);
lean_inc(v___y_1258_);
v___x_1270_ = l_List_get_x21Internal___redArg(v___x_1103_, v_scopes_1269_, v___y_1258_);
lean_dec(v_scopes_1269_);
if (v_printStats_1075_ == 0)
{
lean_object* v_opts_1271_; uint8_t v___x_1272_; uint8_t v___x_1273_; 
v_opts_1271_ = lean_ctor_get(v___x_1270_, 1);
lean_inc_ref(v_opts_1271_);
lean_dec(v___x_1270_);
v___x_1272_ = lean_unbox(v_a_1262_);
v___x_1273_ = lean_unbox(v_a_1262_);
lean_dec(v_a_1262_);
lean_inc_ref(v_env_1268_);
v___y_1236_ = v_env_1268_;
v___y_1237_ = v_opts_1271_;
v___y_1238_ = v___x_1272_;
v___y_1239_ = v_env_1268_;
v___y_1240_ = v___y_1258_;
v___y_1241_ = v___x_1273_;
v___y_1242_ = v___y_1259_;
goto v___jp_1235_;
}
else
{
lean_object* v_opts_1274_; lean_object* v___x_1275_; 
v_opts_1274_ = lean_ctor_get(v___x_1270_, 1);
lean_inc_ref(v_opts_1274_);
lean_dec(v___x_1270_);
lean_inc_ref(v_env_1268_);
v___x_1275_ = l_Lean_Environment_displayStats(v_env_1268_);
if (lean_obj_tag(v___x_1275_) == 0)
{
uint8_t v___x_1276_; uint8_t v___x_1277_; 
lean_dec_ref_known(v___x_1275_, 1);
v___x_1276_ = lean_unbox(v_a_1262_);
v___x_1277_ = lean_unbox(v_a_1262_);
lean_dec(v_a_1262_);
lean_inc_ref(v_env_1268_);
v___y_1236_ = v_env_1268_;
v___y_1237_ = v_opts_1274_;
v___y_1238_ = v___x_1276_;
v___y_1239_ = v_env_1268_;
v___y_1240_ = v___y_1258_;
v___y_1241_ = v___x_1277_;
v___y_1242_ = v___y_1259_;
goto v___jp_1235_;
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v_opts_1274_);
lean_dec_ref(v_env_1268_);
lean_dec(v_a_1262_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec(v_stx_1100_);
lean_dec_ref(v___x_1092_);
lean_dec_ref(v___x_1088_);
lean_dec(v_oleanFileName_x3f_1070_);
lean_dec(v_mainModuleName_1068_);
v_a_1278_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1275_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1275_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
else
{
lean_object* v___x_1287_; 
lean_dec(v___x_1266_);
lean_dec(v_a_1262_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec(v_stx_1100_);
lean_dec_ref(v___x_1092_);
lean_dec_ref(v___x_1088_);
lean_dec(v_oleanFileName_x3f_1070_);
lean_dec(v_mainModuleName_1068_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1096_);
v___x_1287_ = v___x_1264_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1096_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec(v_stx_1100_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v___x_1092_);
lean_dec_ref(v___x_1088_);
lean_dec(v_oleanFileName_x3f_1070_);
lean_dec(v_mainModuleName_1068_);
v_a_1290_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1261_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1261_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
v___jp_1298_:
{
lean_object* v_stx_x3f_1300_; lean_object* v_reportingRange_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_stx_x3f_1300_ = lean_ctor_get(v_metaSnap_1099_, 0);
lean_inc(v_stx_x3f_1300_);
v_reportingRange_1301_ = lean_ctor_get(v_metaSnap_1099_, 1);
lean_inc(v_reportingRange_1301_);
v___x_1302_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_1099_, v___f_1102_, v_stx_x3f_1300_, v_reportingRange_1301_, v___x_1086_);
v___x_1303_ = lean_unsigned_to_nat(1u);
v___x_1304_ = lean_mk_empty_array_with_capacity(v___x_1303_);
v___x_1305_ = lean_array_push(v___x_1304_, v___x_1302_);
v___x_1306_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_1299_, v___x_1305_);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_toSnapshot_1098_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = lean_box(1);
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = lean_array_get_size(v_errorOnKinds_1073_);
v___x_1311_ = lean_nat_dec_lt(v___x_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
v___y_1258_ = v___x_1309_;
v___y_1259_ = v___x_1307_;
v___y_1260_ = v___x_1308_;
goto v___jp_1257_;
}
else
{
uint8_t v___x_1312_; 
v___x_1312_ = lean_nat_dec_le(v___x_1310_, v___x_1310_);
if (v___x_1312_ == 0)
{
if (v___x_1311_ == 0)
{
v___y_1258_ = v___x_1309_;
v___y_1259_ = v___x_1307_;
v___y_1260_ = v___x_1308_;
goto v___jp_1257_;
}
else
{
size_t v___x_1313_; size_t v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = ((size_t)0ULL);
v___x_1314_ = lean_usize_of_nat(v___x_1310_);
v___x_1315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_errorOnKinds_1073_, v___x_1313_, v___x_1314_, v___x_1308_);
v___y_1258_ = v___x_1309_;
v___y_1259_ = v___x_1307_;
v___y_1260_ = v___x_1315_;
goto v___jp_1257_;
}
}
else
{
size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = ((size_t)0ULL);
v___x_1317_ = lean_usize_of_nat(v___x_1310_);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_errorOnKinds_1073_, v___x_1316_, v___x_1317_, v___x_1308_);
v___y_1258_ = v___x_1309_;
v___y_1259_ = v___x_1307_;
v___y_1260_ = v___x_1318_;
goto v___jp_1257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_1332_, lean_object* v_opts_1333_, lean_object* v_fileName_1334_, lean_object* v_mainModuleName_1335_, lean_object* v_trustLevel_1336_, lean_object* v_oleanFileName_x3f_1337_, lean_object* v_ileanFileName_x3f_1338_, lean_object* v_jsonOutput_1339_, lean_object* v_errorOnKinds_1340_, lean_object* v_plugins_1341_, lean_object* v_printStats_1342_, lean_object* v_setup_x3f_1343_, lean_object* v_a_1344_){
_start:
{
uint32_t v_trustLevel_boxed_1345_; uint8_t v_jsonOutput_boxed_1346_; uint8_t v_printStats_boxed_1347_; lean_object* v_res_1348_; 
v_trustLevel_boxed_1345_ = lean_unbox_uint32(v_trustLevel_1336_);
lean_dec(v_trustLevel_1336_);
v_jsonOutput_boxed_1346_ = lean_unbox(v_jsonOutput_1339_);
v_printStats_boxed_1347_ = lean_unbox(v_printStats_1342_);
v_res_1348_ = l_Lean_Elab_runFrontend(v_input_1332_, v_opts_1333_, v_fileName_1334_, v_mainModuleName_1335_, v_trustLevel_boxed_1345_, v_oleanFileName_x3f_1337_, v_ileanFileName_x3f_1338_, v_jsonOutput_boxed_1346_, v_errorOnKinds_1340_, v_plugins_1341_, v_printStats_boxed_1347_, v_setup_x3f_1343_);
lean_dec_ref(v_errorOnKinds_1340_);
lean_dec(v_ileanFileName_x3f_1338_);
return v_res_1348_;
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
