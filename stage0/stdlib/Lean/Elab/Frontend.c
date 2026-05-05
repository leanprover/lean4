// Lean compiler output
// Module: Lean.Elab.Frontend
// Imports: public import Lean.Language.Lean public import Lean.Server.References public import Lean.Util.Profiler import Lean.Compiler.Options import Lean.Linter.PersistentLintLog
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_273_; lean_object* v_commandState_274_; lean_object* v_parserState_275_; lean_object* v_cmdPos_276_; lean_object* v_commands_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_305_; 
v___x_273_ = lean_st_ref_take(v_a_271_);
v_commandState_274_ = lean_ctor_get(v___x_273_, 0);
v_parserState_275_ = lean_ctor_get(v___x_273_, 1);
v_cmdPos_276_ = lean_ctor_get(v___x_273_, 2);
v_commands_277_ = lean_ctor_get(v___x_273_, 3);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_305_ == 0)
{
v___x_279_ = v___x_273_;
v_isShared_280_ = v_isSharedCheck_305_;
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
v_isShared_280_ = v_isSharedCheck_305_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v_env_281_; lean_object* v_scopes_282_; lean_object* v_usedQuotCtxts_283_; lean_object* v_nextMacroScope_284_; lean_object* v_maxRecDepth_285_; lean_object* v_ngen_286_; lean_object* v_auxDeclNGen_287_; lean_object* v_infoState_288_; lean_object* v_traceState_289_; lean_object* v_snapshotTasks_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_303_; 
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
v_isSharedCheck_303_ = !lean_is_exclusive(v_commandState_274_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; 
v_unused_304_ = lean_ctor_get(v_commandState_274_, 1);
lean_dec(v_unused_304_);
v___x_292_ = v_commandState_274_;
v_isShared_293_ = v_isSharedCheck_303_;
goto v_resetjp_291_;
}
else
{
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
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_303_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v_msgs_270_);
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_env_281_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_msgs_270_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_scopes_282_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v_usedQuotCtxts_283_);
lean_ctor_set(v_reuseFailAlloc_302_, 4, v_nextMacroScope_284_);
lean_ctor_set(v_reuseFailAlloc_302_, 5, v_maxRecDepth_285_);
lean_ctor_set(v_reuseFailAlloc_302_, 6, v_ngen_286_);
lean_ctor_set(v_reuseFailAlloc_302_, 7, v_auxDeclNGen_287_);
lean_ctor_set(v_reuseFailAlloc_302_, 8, v_infoState_288_);
lean_ctor_set(v_reuseFailAlloc_302_, 9, v_traceState_289_);
lean_ctor_set(v_reuseFailAlloc_302_, 10, v_snapshotTasks_290_);
v___x_295_ = v_reuseFailAlloc_302_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_295_);
v___x_297_ = v___x_279_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_parserState_275_);
lean_ctor_set(v_reuseFailAlloc_301_, 2, v_cmdPos_276_);
lean_ctor_set(v_reuseFailAlloc_301_, 3, v_commands_277_);
v___x_297_ = v_reuseFailAlloc_301_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_st_ref_set(v_a_271_, v___x_297_);
v___x_299_ = lean_box(0);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg___boxed(lean_object* v_msgs_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_306_, v_a_307_);
lean_dec(v_a_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object* v_msgs_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_310_, v_a_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___boxed(lean_object* v_msgs_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Elab_Frontend_setMessages(v_msgs_315_, v_a_316_, v_a_317_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg(lean_object* v_a_320_){
_start:
{
lean_object* v___x_322_; 
lean_inc_ref(v_a_320_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v_a_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg___boxed(lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Elab_Frontend_getInputContext___redArg(v_a_323_);
lean_dec_ref(v_a_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_329_; 
lean_inc_ref(v_a_326_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v_a_326_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Elab_Frontend_getInputContext(v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0(lean_object* v_a_334_, lean_object* v___x_335_, lean_object* v_a_336_, lean_object* v_messages_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
lean_inc_ref(v_a_334_);
v___x_339_ = l_Lean_Parser_parseCommand(v_a_334_, v___x_335_, v_a_336_, v_messages_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0___boxed(lean_object* v_a_340_, lean_object* v___x_341_, lean_object* v_a_342_, lean_object* v_messages_343_, lean_object* v_x_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Elab_Frontend_processCommand___lam__0(v_a_340_, v___x_341_, v_a_342_, v_messages_343_, v_x_344_);
lean_dec_ref(v_a_340_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_a_352_; lean_object* v___x_353_; lean_object* v_a_354_; lean_object* v_env_355_; lean_object* v_messages_356_; lean_object* v_scopes_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v_opts_360_; lean_object* v_currNamespace_361_; lean_object* v_openDecls_362_; lean_object* v___x_363_; lean_object* v___f_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_snd_368_; lean_object* v_fst_369_; lean_object* v_fst_370_; lean_object* v_snd_371_; lean_object* v___x_372_; lean_object* v_commandState_373_; lean_object* v_parserState_374_; lean_object* v_cmdPos_375_; lean_object* v_commands_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_406_; 
v___x_350_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_348_);
lean_dec_ref(v___x_350_);
v___x_351_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_348_);
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref(v___x_351_);
v___x_353_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_348_);
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref(v___x_353_);
v_env_355_ = lean_ctor_get(v_a_352_, 0);
lean_inc_ref(v_env_355_);
v_messages_356_ = lean_ctor_get(v_a_352_, 1);
lean_inc_ref(v_messages_356_);
v_scopes_357_ = lean_ctor_get(v_a_352_, 2);
lean_inc(v_scopes_357_);
lean_dec(v_a_352_);
v___x_358_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_359_ = l_List_head_x21___redArg(v___x_358_, v_scopes_357_);
lean_dec(v_scopes_357_);
v_opts_360_ = lean_ctor_get(v___x_359_, 1);
lean_inc_ref_n(v_opts_360_, 2);
v_currNamespace_361_ = lean_ctor_get(v___x_359_, 2);
lean_inc(v_currNamespace_361_);
v_openDecls_362_ = lean_ctor_get(v___x_359_, 3);
lean_inc(v_openDecls_362_);
lean_dec(v___x_359_);
v___x_363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_363_, 0, v_env_355_);
lean_ctor_set(v___x_363_, 1, v_opts_360_);
lean_ctor_set(v___x_363_, 2, v_currNamespace_361_);
lean_ctor_set(v___x_363_, 3, v_openDecls_362_);
lean_inc_ref(v_a_347_);
v___f_364_ = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommand___lam__0___boxed), 5, 4);
lean_closure_set(v___f_364_, 0, v_a_347_);
lean_closure_set(v___f_364_, 1, v___x_363_);
lean_closure_set(v___f_364_, 2, v_a_354_);
lean_closure_set(v___f_364_, 3, v_messages_356_);
v___x_365_ = ((lean_object*)(l_Lean_Elab_Frontend_processCommand___closed__0));
v___x_366_ = lean_box(0);
v___x_367_ = lean_profileit(v___x_365_, v_opts_360_, v___f_364_, v___x_366_);
lean_dec_ref(v_opts_360_);
v_snd_368_ = lean_ctor_get(v___x_367_, 1);
lean_inc(v_snd_368_);
v_fst_369_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_fst_369_);
lean_dec(v___x_367_);
v_fst_370_ = lean_ctor_get(v_snd_368_, 0);
lean_inc(v_fst_370_);
v_snd_371_ = lean_ctor_get(v_snd_368_, 1);
lean_inc(v_snd_371_);
lean_dec(v_snd_368_);
v___x_372_ = lean_st_ref_take(v_a_348_);
v_commandState_373_ = lean_ctor_get(v___x_372_, 0);
v_parserState_374_ = lean_ctor_get(v___x_372_, 1);
v_cmdPos_375_ = lean_ctor_get(v___x_372_, 2);
v_commands_376_ = lean_ctor_get(v___x_372_, 3);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_406_ == 0)
{
v___x_378_ = v___x_372_;
v_isShared_379_ = v_isSharedCheck_406_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_commands_376_);
lean_inc(v_cmdPos_375_);
lean_inc(v_parserState_374_);
lean_inc(v_commandState_373_);
lean_dec(v___x_372_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_406_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_382_; 
lean_inc(v_fst_369_);
v___x_380_ = lean_array_push(v_commands_376_, v_fst_369_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 3, v___x_380_);
v___x_382_ = v___x_378_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_commandState_373_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_parserState_374_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_cmdPos_375_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v___x_380_);
v___x_382_ = v_reuseFailAlloc_405_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_383_ = lean_st_ref_set(v_a_348_, v___x_382_);
v___x_384_ = l_Lean_Elab_Frontend_setParserState___redArg(v_fst_370_, v_a_348_);
lean_dec_ref(v___x_384_);
v___x_385_ = l_Lean_Elab_Frontend_setMessages___redArg(v_snd_371_, v_a_348_);
lean_dec_ref(v___x_385_);
lean_inc(v_fst_369_);
v___x_386_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_fst_369_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_395_; 
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v___x_386_, 0);
lean_dec(v_unused_396_);
v___x_388_ = v___x_386_;
v_isShared_389_ = v_isSharedCheck_395_;
goto v_resetjp_387_;
}
else
{
lean_dec(v___x_386_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_395_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = l_Lean_Parser_isTerminalCommand(v_fst_369_);
v___x_391_ = lean_box(v___x_390_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_391_);
v___x_393_ = v___x_388_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec(v_fst_369_);
v_a_397_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_386_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_386_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Elab_Frontend_processCommand(v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Elab_Frontend_processCommand(v_a_411_, v_a_412_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_425_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_425_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_425_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_425_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
uint8_t v___x_419_; 
v___x_419_ = lean_unbox(v_a_415_);
lean_dec(v_a_415_);
if (v___x_419_ == 0)
{
lean_del_object(v___x_417_);
goto _start;
}
else
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = lean_box(0);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_421_);
v___x_423_ = v___x_417_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v_a_426_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_414_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_414_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands___boxed(lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Elab_Frontend_processCommands(v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object* v_as_438_, size_t v_i_439_, size_t v_stop_440_, lean_object* v_b_441_){
_start:
{
lean_object* v___y_443_; uint8_t v___x_447_; 
v___x_447_ = lean_usize_dec_eq(v_i_439_, v_stop_440_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
v___x_448_ = lean_array_uget_borrowed(v_as_438_, v_i_439_);
if (lean_obj_tag(v___x_448_) == 0)
{
v___y_443_ = v_b_441_;
goto v___jp_442_;
}
else
{
lean_object* v_val_449_; lean_object* v___x_450_; 
v_val_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_val_449_);
v___x_450_ = lean_array_push(v_b_441_, v_val_449_);
v___y_443_ = v___x_450_;
goto v___jp_442_;
}
}
else
{
return v_b_441_;
}
v___jp_442_:
{
size_t v___x_444_; size_t v___x_445_; 
v___x_444_ = ((size_t)1ULL);
v___x_445_ = lean_usize_add(v_i_439_, v___x_444_);
v_i_439_ = v___x_445_;
v_b_441_ = v___y_443_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object* v_as_451_, lean_object* v_i_452_, lean_object* v_stop_453_, lean_object* v_b_454_){
_start:
{
size_t v_i_boxed_455_; size_t v_stop_boxed_456_; lean_object* v_res_457_; 
v_i_boxed_455_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_stop_boxed_456_ = lean_unbox_usize(v_stop_453_);
lean_dec(v_stop_453_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_451_, v_i_boxed_455_, v_stop_boxed_456_, v_b_454_);
lean_dec_ref(v_as_451_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object* v_as_460_, lean_object* v_start_461_, lean_object* v_stop_462_){
_start:
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_464_ = lean_nat_dec_lt(v_start_461_, v_stop_462_);
if (v___x_464_ == 0)
{
return v___x_463_;
}
else
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_array_get_size(v_as_460_);
v___x_466_ = lean_nat_dec_le(v_stop_462_, v___x_465_);
if (v___x_466_ == 0)
{
uint8_t v___x_467_; 
v___x_467_ = lean_nat_dec_lt(v_start_461_, v___x_465_);
if (v___x_467_ == 0)
{
return v___x_463_;
}
else
{
size_t v___x_468_; size_t v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_usize_of_nat(v_start_461_);
v___x_469_ = lean_usize_of_nat(v___x_465_);
v___x_470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_460_, v___x_468_, v___x_469_, v___x_463_);
return v___x_470_;
}
}
else
{
size_t v___x_471_; size_t v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_usize_of_nat(v_start_461_);
v___x_472_ = lean_usize_of_nat(v_stop_462_);
v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_460_, v___x_471_, v___x_472_, v___x_463_);
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object* v_as_474_, lean_object* v_start_475_, lean_object* v_stop_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v_as_474_, v_start_475_, v_stop_476_);
lean_dec(v_stop_476_);
lean_dec(v_start_475_);
lean_dec_ref(v_as_474_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t v_sz_478_, size_t v_i_479_, lean_object* v_bs_480_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = lean_usize_dec_lt(v_i_479_, v_sz_478_);
if (v___x_481_ == 0)
{
return v_bs_480_;
}
else
{
lean_object* v_v_482_; lean_object* v_elabSnap_483_; lean_object* v_infoTreeSnap_484_; lean_object* v___x_485_; lean_object* v_infoTree_x3f_486_; lean_object* v___x_487_; lean_object* v_bs_x27_488_; size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; 
v_v_482_ = lean_array_uget_borrowed(v_bs_480_, v_i_479_);
v_elabSnap_483_ = lean_ctor_get(v_v_482_, 3);
v_infoTreeSnap_484_ = lean_ctor_get(v_elabSnap_483_, 3);
lean_inc_ref(v_infoTreeSnap_484_);
v___x_485_ = l_Lean_Language_SnapshotTask_get___redArg(v_infoTreeSnap_484_);
v_infoTree_x3f_486_ = lean_ctor_get(v___x_485_, 2);
lean_inc(v_infoTree_x3f_486_);
lean_dec(v___x_485_);
v___x_487_ = lean_unsigned_to_nat(0u);
v_bs_x27_488_ = lean_array_uset(v_bs_480_, v_i_479_, v___x_487_);
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_add(v_i_479_, v___x_489_);
v___x_491_ = lean_array_uset(v_bs_x27_488_, v_i_479_, v_infoTree_x3f_486_);
v_i_479_ = v___x_490_;
v_bs_480_ = v___x_491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object* v_sz_493_, lean_object* v_i_494_, lean_object* v_bs_495_){
_start:
{
size_t v_sz_boxed_496_; size_t v_i_boxed_497_; lean_object* v_res_498_; 
v_sz_boxed_496_ = lean_unbox_usize(v_sz_493_);
lean_dec(v_sz_493_);
v_i_boxed_497_ = lean_unbox_usize(v_i_494_);
lean_dec(v_i_494_);
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_boxed_496_, v_i_boxed_497_, v_bs_495_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(lean_object* v_as_499_, size_t v_i_500_, size_t v_stop_501_, lean_object* v_b_502_){
_start:
{
uint8_t v___x_503_; 
v___x_503_ = lean_usize_dec_eq(v_i_500_, v_stop_501_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; size_t v___x_506_; size_t v___x_507_; 
v___x_504_ = lean_array_uget_borrowed(v_as_499_, v_i_500_);
lean_inc(v___x_504_);
v___x_505_ = l_Lean_MessageLog_append(v_b_502_, v___x_504_);
v___x_506_ = ((size_t)1ULL);
v___x_507_ = lean_usize_add(v_i_500_, v___x_506_);
v_i_500_ = v___x_507_;
v_b_502_ = v___x_505_;
goto _start;
}
else
{
return v_b_502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object* v_as_509_, lean_object* v_i_510_, lean_object* v_stop_511_, lean_object* v_b_512_){
_start:
{
size_t v_i_boxed_513_; size_t v_stop_boxed_514_; lean_object* v_res_515_; 
v_i_boxed_513_ = lean_unbox_usize(v_i_510_);
lean_dec(v_i_510_);
v_stop_boxed_514_ = lean_unbox_usize(v_stop_511_);
lean_dec(v_stop_511_);
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_as_509_, v_i_boxed_513_, v_stop_boxed_514_, v_b_512_);
lean_dec_ref(v_as_509_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t v_sz_516_, size_t v_i_517_, lean_object* v_bs_518_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = lean_usize_dec_lt(v_i_517_, v_sz_516_);
if (v___x_519_ == 0)
{
return v_bs_518_;
}
else
{
lean_object* v_v_520_; lean_object* v_stx_521_; lean_object* v___x_522_; lean_object* v_bs_x27_523_; size_t v___x_524_; size_t v___x_525_; lean_object* v___x_526_; 
v_v_520_ = lean_array_uget_borrowed(v_bs_518_, v_i_517_);
v_stx_521_ = lean_ctor_get(v_v_520_, 1);
lean_inc(v_stx_521_);
v___x_522_ = lean_unsigned_to_nat(0u);
v_bs_x27_523_ = lean_array_uset(v_bs_518_, v_i_517_, v___x_522_);
v___x_524_ = ((size_t)1ULL);
v___x_525_ = lean_usize_add(v_i_517_, v___x_524_);
v___x_526_ = lean_array_uset(v_bs_x27_523_, v_i_517_, v_stx_521_);
v_i_517_ = v___x_525_;
v_bs_518_ = v___x_526_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object* v_sz_528_, lean_object* v_i_529_, lean_object* v_bs_530_){
_start:
{
size_t v_sz_boxed_531_; size_t v_i_boxed_532_; lean_object* v_res_533_; 
v_sz_boxed_531_ = lean_unbox_usize(v_sz_528_);
lean_dec(v_sz_528_);
v_i_boxed_532_ = lean_unbox_usize(v_i_529_);
lean_dec(v_i_529_);
v_res_533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_boxed_531_, v_i_boxed_532_, v_bs_530_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(size_t v_sz_534_, size_t v_i_535_, lean_object* v_bs_536_){
_start:
{
uint8_t v___x_537_; 
v___x_537_ = lean_usize_dec_lt(v_i_535_, v_sz_534_);
if (v___x_537_ == 0)
{
return v_bs_536_;
}
else
{
lean_object* v_v_538_; lean_object* v_diagnostics_539_; lean_object* v_msgLog_540_; lean_object* v___x_541_; lean_object* v_bs_x27_542_; size_t v___x_543_; size_t v___x_544_; lean_object* v___x_545_; 
v_v_538_ = lean_array_uget_borrowed(v_bs_536_, v_i_535_);
v_diagnostics_539_ = lean_ctor_get(v_v_538_, 1);
v_msgLog_540_ = lean_ctor_get(v_diagnostics_539_, 0);
lean_inc_ref(v_msgLog_540_);
v___x_541_ = lean_unsigned_to_nat(0u);
v_bs_x27_542_ = lean_array_uset(v_bs_536_, v_i_535_, v___x_541_);
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_add(v_i_535_, v___x_543_);
v___x_545_ = lean_array_uset(v_bs_x27_542_, v_i_535_, v_msgLog_540_);
v_i_535_ = v___x_544_;
v_bs_536_ = v___x_545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3___boxed(lean_object* v_sz_547_, lean_object* v_i_548_, lean_object* v_bs_549_){
_start:
{
size_t v_sz_boxed_550_; size_t v_i_boxed_551_; lean_object* v_res_552_; 
v_sz_boxed_550_ = lean_unbox_usize(v_sz_547_);
lean_dec(v_sz_547_);
v_i_boxed_551_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_sz_boxed_550_, v_i_boxed_551_, v_bs_549_);
return v_res_552_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_unsigned_to_nat(32u);
v___x_554_ = lean_mk_empty_array_with_capacity(v___x_553_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1(void){
_start:
{
size_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_556_ = ((size_t)5ULL);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_unsigned_to_nat(32u);
v___x_559_ = lean_mk_empty_array_with_capacity(v___x_558_);
v___x_560_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0);
v___x_561_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_559_);
lean_ctor_set(v___x_561_, 2, v___x_557_);
lean_ctor_set(v___x_561_, 3, v___x_557_);
lean_ctor_set_usize(v___x_561_, 4, v___x_556_);
return v___x_561_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = l_Lean_NameSet_empty;
v___x_563_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1);
v___x_564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
lean_ctor_set(v___x_564_, 2, v___x_562_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(lean_object* v_inputCtx_565_, lean_object* v_initialSnap_566_, lean_object* v_t_567_, lean_object* v_commands_568_){
_start:
{
lean_object* v_snap_570_; lean_object* v_parserState_571_; lean_object* v_elabSnap_572_; lean_object* v_nextCmdSnap_x3f_573_; lean_object* v_commands_574_; 
v_snap_570_ = lean_task_get_own(v_t_567_);
v_parserState_571_ = lean_ctor_get(v_snap_570_, 2);
lean_inc_ref(v_parserState_571_);
v_elabSnap_572_ = lean_ctor_get(v_snap_570_, 3);
lean_inc_ref(v_elabSnap_572_);
v_nextCmdSnap_x3f_573_ = lean_ctor_get(v_snap_570_, 4);
lean_inc(v_nextCmdSnap_x3f_573_);
v_commands_574_ = lean_array_push(v_commands_568_, v_snap_570_);
if (lean_obj_tag(v_nextCmdSnap_x3f_573_) == 1)
{
lean_object* v_val_575_; lean_object* v_task_576_; 
lean_dec_ref(v_elabSnap_572_);
lean_dec_ref(v_parserState_571_);
v_val_575_ = lean_ctor_get(v_nextCmdSnap_x3f_573_, 0);
lean_inc(v_val_575_);
lean_dec_ref(v_nextCmdSnap_x3f_573_);
v_task_576_ = lean_ctor_get(v_val_575_, 3);
lean_inc_ref(v_task_576_);
lean_dec(v_val_575_);
v_t_567_ = v_task_576_;
v_commands_568_ = v_commands_574_;
goto _start;
}
else
{
lean_object* v___x_578_; lean_object* v___y_580_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; size_t v_sz_626_; size_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
lean_dec(v_nextCmdSnap_x3f_573_);
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
lean_inc_ref(v_initialSnap_566_);
v___x_624_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_initialSnap_566_);
v___x_625_ = l_Lean_Language_SnapshotTree_getAll(v___x_624_);
v_sz_626_ = lean_array_size(v___x_625_);
v___x_627_ = ((size_t)0ULL);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_sz_626_, v___x_627_, v___x_625_);
v___x_629_ = lean_array_get_size(v___x_628_);
v___x_630_ = lean_nat_dec_lt(v___x_578_, v___x_629_);
if (v___x_630_ == 0)
{
lean_dec_ref(v___x_628_);
v___y_580_ = v___x_623_;
goto v___jp_579_;
}
else
{
uint8_t v___x_631_; 
v___x_631_ = lean_nat_dec_le(v___x_629_, v___x_629_);
if (v___x_631_ == 0)
{
if (v___x_630_ == 0)
{
lean_dec_ref(v___x_628_);
v___y_580_ = v___x_623_;
goto v___jp_579_;
}
else
{
size_t v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_usize_of_nat(v___x_629_);
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v___x_628_, v___x_627_, v___x_632_, v___x_623_);
lean_dec_ref(v___x_628_);
v___y_580_ = v___x_633_;
goto v___jp_579_;
}
}
else
{
size_t v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_usize_of_nat(v___x_629_);
v___x_635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v___x_628_, v___x_627_, v___x_634_, v___x_623_);
lean_dec_ref(v___x_628_);
v___y_580_ = v___x_635_;
goto v___jp_579_;
}
}
v___jp_579_:
{
size_t v_sz_581_; lean_object* v_resultSnap_582_; lean_object* v___x_583_; lean_object* v_cmdState_584_; lean_object* v_infoState_585_; lean_object* v_env_586_; lean_object* v_scopes_587_; lean_object* v_usedQuotCtxts_588_; lean_object* v_nextMacroScope_589_; lean_object* v_maxRecDepth_590_; lean_object* v_ngen_591_; lean_object* v_auxDeclNGen_592_; lean_object* v_traceState_593_; lean_object* v_snapshotTasks_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_621_; 
v_sz_581_ = lean_array_size(v_commands_574_);
v_resultSnap_582_ = lean_ctor_get(v_elabSnap_572_, 2);
lean_inc_ref(v_resultSnap_582_);
lean_dec_ref(v_elabSnap_572_);
v___x_583_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_582_);
v_cmdState_584_ = lean_ctor_get(v___x_583_, 1);
lean_inc_ref(v_cmdState_584_);
lean_dec(v___x_583_);
v_infoState_585_ = lean_ctor_get(v_cmdState_584_, 8);
v_env_586_ = lean_ctor_get(v_cmdState_584_, 0);
v_scopes_587_ = lean_ctor_get(v_cmdState_584_, 2);
v_usedQuotCtxts_588_ = lean_ctor_get(v_cmdState_584_, 3);
v_nextMacroScope_589_ = lean_ctor_get(v_cmdState_584_, 4);
v_maxRecDepth_590_ = lean_ctor_get(v_cmdState_584_, 5);
v_ngen_591_ = lean_ctor_get(v_cmdState_584_, 6);
v_auxDeclNGen_592_ = lean_ctor_get(v_cmdState_584_, 7);
v_traceState_593_ = lean_ctor_get(v_cmdState_584_, 9);
v_snapshotTasks_594_ = lean_ctor_get(v_cmdState_584_, 10);
v_isSharedCheck_621_ = !lean_is_exclusive(v_cmdState_584_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v_cmdState_584_, 1);
lean_dec(v_unused_622_);
v___x_596_ = v_cmdState_584_;
v_isShared_597_ = v_isSharedCheck_621_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_snapshotTasks_594_);
lean_inc(v_traceState_593_);
lean_inc(v_infoState_585_);
lean_inc(v_auxDeclNGen_592_);
lean_inc(v_ngen_591_);
lean_inc(v_maxRecDepth_590_);
lean_inc(v_nextMacroScope_589_);
lean_inc(v_usedQuotCtxts_588_);
lean_inc(v_scopes_587_);
lean_inc(v_env_586_);
lean_dec(v_cmdState_584_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_621_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
uint8_t v_enabled_598_; lean_object* v_assignment_599_; lean_object* v_lazyAssignment_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_619_; 
v_enabled_598_ = lean_ctor_get_uint8(v_infoState_585_, sizeof(void*)*3);
v_assignment_599_ = lean_ctor_get(v_infoState_585_, 0);
v_lazyAssignment_600_ = lean_ctor_get(v_infoState_585_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_infoState_585_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v_infoState_585_, 2);
lean_dec(v_unused_620_);
v___x_602_ = v_infoState_585_;
v_isShared_603_ = v_isSharedCheck_619_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_lazyAssignment_600_);
lean_inc(v_assignment_599_);
lean_dec(v_infoState_585_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_619_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v_pos_604_; size_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v_trees_609_; lean_object* v___x_611_; 
v_pos_604_ = lean_ctor_get(v_parserState_571_, 0);
lean_inc(v_pos_604_);
v___x_605_ = ((size_t)0ULL);
lean_inc_ref(v_commands_574_);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_581_, v___x_605_, v_commands_574_);
v___x_607_ = lean_array_get_size(v___x_606_);
v___x_608_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v___x_606_, v___x_578_, v___x_607_);
lean_dec_ref(v___x_606_);
v_trees_609_ = l_Array_toPArray_x27___redArg(v___x_608_);
lean_dec_ref(v___x_608_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 2, v_trees_609_);
v___x_611_ = v___x_602_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_assignment_599_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_lazyAssignment_600_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_trees_609_);
lean_ctor_set_uint8(v_reuseFailAlloc_618_, sizeof(void*)*3, v_enabled_598_);
v___x_611_ = v_reuseFailAlloc_618_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 8, v___x_611_);
lean_ctor_set(v___x_596_, 1, v___y_580_);
v___x_613_ = v___x_596_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_env_586_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___y_580_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_scopes_587_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_usedQuotCtxts_588_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_nextMacroScope_589_);
lean_ctor_set(v_reuseFailAlloc_617_, 5, v_maxRecDepth_590_);
lean_ctor_set(v_reuseFailAlloc_617_, 6, v_ngen_591_);
lean_ctor_set(v_reuseFailAlloc_617_, 7, v_auxDeclNGen_592_);
lean_ctor_set(v_reuseFailAlloc_617_, 8, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_617_, 9, v_traceState_593_);
lean_ctor_set(v_reuseFailAlloc_617_, 10, v_snapshotTasks_594_);
v___x_613_ = v_reuseFailAlloc_617_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_581_, v___x_605_, v_commands_574_);
v___x_615_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v_parserState_571_);
lean_ctor_set(v___x_615_, 2, v_pos_604_);
lean_ctor_set(v___x_615_, 3, v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v_inputCtx_565_);
lean_ctor_set(v___x_616_, 2, v_initialSnap_566_);
return v___x_616_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___boxed(lean_object* v_inputCtx_636_, lean_object* v_initialSnap_637_, lean_object* v_t_638_, lean_object* v_commands_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_636_, v_initialSnap_637_, v_t_638_, v_commands_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object* v_inputCtx_644_, lean_object* v_parserState_645_, lean_object* v_commandState_646_, lean_object* v_old_x3f_647_){
_start:
{
lean_object* v___y_650_; 
if (lean_obj_tag(v_old_x3f_647_) == 0)
{
lean_object* v___x_655_; 
v___x_655_ = lean_box(0);
v___y_650_ = v___x_655_;
goto v___jp_649_;
}
else
{
lean_object* v_val_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_666_; 
v_val_656_ = lean_ctor_get(v_old_x3f_647_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v_old_x3f_647_);
if (v_isSharedCheck_666_ == 0)
{
v___x_658_ = v_old_x3f_647_;
v_isShared_659_ = v_isSharedCheck_666_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_val_656_);
lean_dec(v_old_x3f_647_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_666_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_inputCtx_660_; lean_object* v_initialSnap_661_; lean_object* v___x_662_; lean_object* v___x_664_; 
v_inputCtx_660_ = lean_ctor_get(v_val_656_, 1);
lean_inc_ref(v_inputCtx_660_);
v_initialSnap_661_ = lean_ctor_get(v_val_656_, 2);
lean_inc_ref(v_initialSnap_661_);
lean_dec(v_val_656_);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v_inputCtx_660_);
lean_ctor_set(v___x_662_, 1, v_initialSnap_661_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_662_);
v___x_664_ = v___x_658_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
v___y_650_ = v___x_664_;
goto v___jp_649_;
}
}
}
v___jp_649_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_651_ = l_Lean_Language_Lean_processCommands(v_inputCtx_644_, v_parserState_645_, v_commandState_646_, v___y_650_);
lean_inc_ref(v___x_651_);
v___x_652_ = lean_task_get_own(v___x_651_);
v___x_653_ = ((lean_object*)(l_Lean_Elab_IO_processCommandsIncrementally___closed__0));
v___x_654_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_644_, v___x_652_, v___x_651_, v___x_653_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally___boxed(lean_object* v_inputCtx_667_, lean_object* v_parserState_668_, lean_object* v_commandState_669_, lean_object* v_old_x3f_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_667_, v_parserState_668_, v_commandState_669_, v_old_x3f_670_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object* v_inputCtx_673_, lean_object* v_parserState_674_, lean_object* v_commandState_675_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_toState_679_; lean_object* v___x_680_; 
v___x_677_ = lean_box(0);
v___x_678_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_673_, v_parserState_674_, v_commandState_675_, v___x_677_);
v_toState_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc_ref(v_toState_679_);
lean_dec_ref(v___x_678_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v_toState_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands___boxed(lean_object* v_inputCtx_681_, lean_object* v_parserState_682_, lean_object* v_commandState_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Elab_IO_processCommands(v_inputCtx_681_, v_parserState_682_, v_commandState_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object* v_input_691_, lean_object* v_env_692_, lean_object* v_opts_693_, lean_object* v_fileName_694_){
_start:
{
lean_object* v___y_697_; 
if (lean_obj_tag(v_fileName_694_) == 0)
{
lean_object* v___x_717_; 
v___x_717_ = ((lean_object*)(l_Lean_Elab_process___closed__1));
v___y_697_ = v___x_717_;
goto v___jp_696_;
}
else
{
lean_object* v_val_718_; 
v_val_718_ = lean_ctor_get(v_fileName_694_, 0);
lean_inc(v_val_718_);
lean_dec_ref(v_fileName_694_);
v___y_697_ = v_val_718_;
goto v___jp_696_;
}
v___jp_696_:
{
uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v_inputCtx_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_716_; 
v___x_698_ = 1;
v___x_699_ = lean_string_utf8_byte_size(v_input_691_);
v_inputCtx_700_ = l_Lean_Parser_mkInputContext___redArg(v_input_691_, v___y_697_, v___x_698_, v___x_699_);
v___x_701_ = ((lean_object*)(l_Lean_Elab_process___closed__0));
v___x_702_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
v___x_703_ = l_Lean_Elab_Command_mkState(v_env_692_, v___x_702_, v_opts_693_);
v___x_704_ = l_Lean_Elab_IO_processCommands(v_inputCtx_700_, v___x_701_, v___x_703_);
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_716_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_716_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_716_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_commandState_709_; lean_object* v_env_710_; lean_object* v_messages_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v_commandState_709_ = lean_ctor_get(v_a_705_, 0);
lean_inc_ref(v_commandState_709_);
lean_dec(v_a_705_);
v_env_710_ = lean_ctor_get(v_commandState_709_, 0);
lean_inc_ref(v_env_710_);
v_messages_711_ = lean_ctor_get(v_commandState_709_, 1);
lean_inc_ref(v_messages_711_);
lean_dec_ref(v_commandState_709_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_env_710_);
lean_ctor_set(v___x_712_, 1, v_messages_711_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_712_);
v___x_714_ = v___x_707_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process___boxed(lean_object* v_input_719_, lean_object* v_env_720_, lean_object* v_opts_721_, lean_object* v_fileName_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Elab_process(v_input_719_, v_env_720_, v_opts_721_, v_fileName_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_opts_725_, lean_object* v_opt_726_){
_start:
{
lean_object* v_name_727_; lean_object* v_map_728_; lean_object* v___x_729_; 
v_name_727_ = lean_ctor_get(v_opt_726_, 0);
v_map_728_ = lean_ctor_get(v_opts_725_, 0);
v___x_729_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_728_, v_name_727_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v___x_730_; 
v___x_730_ = lean_box(0);
return v___x_730_;
}
else
{
lean_object* v_val_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_740_; 
v_val_731_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_740_ == 0)
{
v___x_733_ = v___x_729_;
v_isShared_734_ = v_isSharedCheck_740_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_val_731_);
lean_dec(v___x_729_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_740_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
if (lean_obj_tag(v_val_731_) == 0)
{
lean_object* v_v_735_; lean_object* v___x_737_; 
v_v_735_ = lean_ctor_get(v_val_731_, 0);
lean_inc_ref(v_v_735_);
lean_dec_ref(v_val_731_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v_v_735_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_v_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
else
{
lean_object* v___x_739_; 
lean_del_object(v___x_733_);
lean_dec(v_val_731_);
v___x_739_ = lean_box(0);
return v___x_739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2___boxed(lean_object* v_opts_741_, lean_object* v_opt_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(v_opts_741_, v_opt_742_);
lean_dec_ref(v_opt_742_);
lean_dec_ref(v_opts_741_);
return v_res_743_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(lean_object* v_opts_744_, lean_object* v_opt_745_){
_start:
{
lean_object* v_name_746_; lean_object* v_defValue_747_; lean_object* v_map_748_; lean_object* v___x_749_; 
v_name_746_ = lean_ctor_get(v_opt_745_, 0);
v_defValue_747_ = lean_ctor_get(v_opt_745_, 1);
v_map_748_ = lean_ctor_get(v_opts_744_, 0);
v___x_749_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_748_, v_name_746_);
if (lean_obj_tag(v___x_749_) == 0)
{
uint8_t v___x_750_; 
v___x_750_ = lean_unbox(v_defValue_747_);
return v___x_750_;
}
else
{
lean_object* v_val_751_; 
v_val_751_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_val_751_);
lean_dec_ref(v___x_749_);
if (lean_obj_tag(v_val_751_) == 1)
{
uint8_t v_v_752_; 
v_v_752_ = lean_ctor_get_uint8(v_val_751_, 0);
lean_dec_ref(v_val_751_);
return v_v_752_;
}
else
{
uint8_t v___x_753_; 
lean_dec(v_val_751_);
v___x_753_ = lean_unbox(v_defValue_747_);
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_opts_754_, lean_object* v_opt_755_){
_start:
{
uint8_t v_res_756_; lean_object* v_r_757_; 
v_res_756_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(v_opts_754_, v_opt_755_);
lean_dec_ref(v_opt_755_);
lean_dec_ref(v_opts_754_);
v_r_757_ = lean_box(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_hOpt_760_){
_start:
{
lean_inc_ref(v_hOpt_760_);
return v_hOpt_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_hOpt_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Elab_runFrontend___lam__0(v_x_761_, v_x_762_, v_hOpt_763_);
lean_dec_ref(v_hOpt_763_);
lean_dec_ref(v_x_762_);
lean_dec(v_x_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_765_, size_t v_i_766_, size_t v_stop_767_, lean_object* v_b_768_){
_start:
{
uint8_t v___x_770_; 
v___x_770_ = lean_usize_dec_eq(v_i_766_, v_stop_767_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_array_uget_borrowed(v_as_765_, v_i_766_);
lean_inc(v___x_771_);
v___x_772_ = lean_load_dynlib(v___x_771_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; size_t v___x_774_; size_t v___x_775_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref(v___x_772_);
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_766_, v___x_774_);
v_i_766_ = v___x_775_;
v_b_768_ = v_a_773_;
goto _start;
}
else
{
return v___x_772_;
}
}
else
{
lean_object* v___x_777_; 
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v_b_768_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_stop_780_, lean_object* v_b_781_, lean_object* v___y_782_){
_start:
{
size_t v_i_boxed_783_; size_t v_stop_boxed_784_; lean_object* v_res_785_; 
v_i_boxed_783_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_stop_boxed_784_ = lean_unbox_usize(v_stop_780_);
lean_dec(v_stop_780_);
v_res_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_778_, v_i_boxed_783_, v_stop_boxed_784_, v_b_781_);
lean_dec_ref(v_as_778_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_setup_x3f_786_, lean_object* v___f_787_, lean_object* v___x_788_, lean_object* v_plugins_789_, uint32_t v_trustLevel_790_, uint8_t v___x_791_, lean_object* v_mainModuleName_792_, lean_object* v_stx_793_, lean_object* v___y_794_){
_start:
{
uint8_t v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; 
if (lean_obj_tag(v_setup_x3f_786_) == 1)
{
lean_object* v_val_810_; lean_object* v_name_811_; lean_object* v_package_x3f_812_; uint8_t v_isModule_813_; lean_object* v_imports_x3f_814_; lean_object* v_importArts_815_; lean_object* v_dynlibs_816_; lean_object* v_plugins_817_; lean_object* v_options_818_; lean_object* v___y_825_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
lean_dec(v_mainModuleName_792_);
v_val_810_ = lean_ctor_get(v_setup_x3f_786_, 0);
lean_inc(v_val_810_);
lean_dec_ref(v_setup_x3f_786_);
v_name_811_ = lean_ctor_get(v_val_810_, 0);
lean_inc(v_name_811_);
v_package_x3f_812_ = lean_ctor_get(v_val_810_, 1);
lean_inc(v_package_x3f_812_);
v_isModule_813_ = lean_ctor_get_uint8(v_val_810_, sizeof(void*)*7);
v_imports_x3f_814_ = lean_ctor_get(v_val_810_, 2);
lean_inc(v_imports_x3f_814_);
v_importArts_815_ = lean_ctor_get(v_val_810_, 3);
lean_inc(v_importArts_815_);
v_dynlibs_816_ = lean_ctor_get(v_val_810_, 4);
lean_inc_ref(v_dynlibs_816_);
v_plugins_817_ = lean_ctor_get(v_val_810_, 5);
lean_inc_ref(v_plugins_817_);
v_options_818_ = lean_ctor_get(v_val_810_, 6);
lean_inc(v_options_818_);
lean_dec(v_val_810_);
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_array_get_size(v_dynlibs_816_);
v___x_836_ = lean_nat_dec_lt(v___x_834_, v___x_835_);
if (v___x_836_ == 0)
{
lean_dec_ref(v_dynlibs_816_);
goto v___jp_819_;
}
else
{
lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_837_ = lean_box(0);
v___x_838_ = lean_nat_dec_le(v___x_835_, v___x_835_);
if (v___x_838_ == 0)
{
if (v___x_836_ == 0)
{
lean_dec_ref(v_dynlibs_816_);
goto v___jp_819_;
}
else
{
size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; 
v___x_839_ = ((size_t)0ULL);
v___x_840_ = lean_usize_of_nat(v___x_835_);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_816_, v___x_839_, v___x_840_, v___x_837_);
lean_dec_ref(v_dynlibs_816_);
v___y_825_ = v___x_841_;
goto v___jp_824_;
}
}
else
{
size_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((size_t)0ULL);
v___x_843_ = lean_usize_of_nat(v___x_835_);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_816_, v___x_842_, v___x_843_, v___x_837_);
lean_dec_ref(v_dynlibs_816_);
v___y_825_ = v___x_844_;
goto v___jp_824_;
}
}
v___jp_819_:
{
uint8_t v___x_820_; uint8_t v___x_821_; 
v___x_820_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_793_);
v___x_821_ = lean_strict_or(v_isModule_813_, v___x_820_);
if (lean_obj_tag(v_imports_x3f_814_) == 0)
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_793_, v___x_791_);
v___y_797_ = v___x_821_;
v___y_798_ = v_plugins_817_;
v___y_799_ = v_importArts_815_;
v___y_800_ = v_name_811_;
v___y_801_ = v_package_x3f_812_;
v___y_802_ = v_options_818_;
v___y_803_ = v___x_822_;
goto v___jp_796_;
}
else
{
lean_object* v_val_823_; 
lean_dec(v_stx_793_);
v_val_823_ = lean_ctor_get(v_imports_x3f_814_, 0);
lean_inc(v_val_823_);
lean_dec_ref(v_imports_x3f_814_);
v___y_797_ = v___x_821_;
v___y_798_ = v_plugins_817_;
v___y_799_ = v_importArts_815_;
v___y_800_ = v_name_811_;
v___y_801_ = v_package_x3f_812_;
v___y_802_ = v_options_818_;
v___y_803_ = v_val_823_;
goto v___jp_796_;
}
}
v___jp_824_:
{
if (lean_obj_tag(v___y_825_) == 0)
{
lean_dec_ref(v___y_825_);
goto v___jp_819_;
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_options_818_);
lean_dec_ref(v_plugins_817_);
lean_dec(v_importArts_815_);
lean_dec(v_imports_x3f_814_);
lean_dec(v_package_x3f_812_);
lean_dec(v_name_811_);
lean_dec(v_stx_793_);
lean_dec_ref(v_plugins_789_);
lean_dec_ref(v___x_788_);
lean_dec_ref(v___f_787_);
v_a_826_ = lean_ctor_get(v___y_825_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___y_825_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___y_825_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___y_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
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
}
else
{
lean_object* v___x_845_; uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref(v___f_787_);
lean_dec(v_setup_x3f_786_);
v___x_845_ = lean_box(0);
v___x_846_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_793_);
v___x_847_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_793_, v___x_791_);
v___x_848_ = lean_box(1);
v___x_849_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_849_, 0, v_mainModuleName_792_);
lean_ctor_set(v___x_849_, 1, v___x_845_);
lean_ctor_set(v___x_849_, 2, v___x_847_);
lean_ctor_set(v___x_849_, 3, v___x_788_);
lean_ctor_set(v___x_849_, 4, v___x_848_);
lean_ctor_set(v___x_849_, 5, v_plugins_789_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*6 + 4, v___x_846_);
lean_ctor_set_uint32(v___x_849_, sizeof(void*)*6, v_trustLevel_790_);
v___x_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
v___jp_796_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_804_ = l_Lean_LeanOptions_toOptions(v___y_802_);
v___x_805_ = l_Lean_Options_mergeBy(v___f_787_, v___x_788_, v___x_804_);
v___x_806_ = l_Array_append___redArg(v_plugins_789_, v___y_798_);
lean_dec_ref(v___y_798_);
v___x_807_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_807_, 0, v___y_800_);
lean_ctor_set(v___x_807_, 1, v___y_801_);
lean_ctor_set(v___x_807_, 2, v___y_803_);
lean_ctor_set(v___x_807_, 3, v___x_805_);
lean_ctor_set(v___x_807_, 4, v___y_799_);
lean_ctor_set(v___x_807_, 5, v___x_806_);
lean_ctor_set_uint8(v___x_807_, sizeof(void*)*6 + 4, v___y_797_);
lean_ctor_set_uint32(v___x_807_, sizeof(void*)*6, v_trustLevel_790_);
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object* v_setup_x3f_852_, lean_object* v___f_853_, lean_object* v___x_854_, lean_object* v_plugins_855_, lean_object* v_trustLevel_856_, lean_object* v___x_857_, lean_object* v_mainModuleName_858_, lean_object* v_stx_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
uint32_t v_trustLevel_boxed_862_; uint8_t v___x_4473__boxed_863_; lean_object* v_res_864_; 
v_trustLevel_boxed_862_ = lean_unbox_uint32(v_trustLevel_856_);
lean_dec(v_trustLevel_856_);
v___x_4473__boxed_863_ = lean_unbox(v___x_857_);
v_res_864_ = l_Lean_Elab_runFrontend___lam__1(v_setup_x3f_852_, v___f_853_, v___x_854_, v_plugins_855_, v_trustLevel_boxed_862_, v___x_4473__boxed_863_, v_mainModuleName_858_, v_stx_859_, v___y_860_);
lean_dec_ref(v___y_860_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_s_867_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l_Lean_Elab_runFrontend___lam__2___closed__0));
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v_s_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_env_870_, lean_object* v___y_871_, lean_object* v_opts_872_, lean_object* v_val_873_, uint8_t v___x_874_, uint8_t v_a_875_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = l_Lean_Linter_recordLints(v_env_870_, v___y_871_);
v___x_878_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_879_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(v_opts_872_, v___x_878_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_writeModule(v___x_877_, v_val_873_, v___x_874_);
return v___x_880_;
}
else
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_writeModule(v___x_877_, v_val_873_, v_a_875_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_env_882_, lean_object* v___y_883_, lean_object* v_opts_884_, lean_object* v_val_885_, lean_object* v___x_886_, lean_object* v_a_887_, lean_object* v___y_888_){
_start:
{
uint8_t v___x_4595__boxed_889_; uint8_t v_a_4596__boxed_890_; lean_object* v_res_891_; 
v___x_4595__boxed_889_ = lean_unbox(v___x_886_);
v_a_4596__boxed_890_ = lean_unbox(v_a_887_);
v_res_891_ = l_Lean_Elab_runFrontend___lam__3(v_env_882_, v___y_883_, v_opts_884_, v_val_885_, v___x_4595__boxed_889_, v_a_4596__boxed_890_);
lean_dec_ref(v_opts_884_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object* v___f_893_, lean_object* v_s_894_){
_start:
{
lean_object* v_toSnapshot_895_; lean_object* v_metaSnap_896_; lean_object* v_result_x3f_897_; lean_object* v___y_899_; 
v_toSnapshot_895_ = lean_ctor_get(v_s_894_, 0);
lean_inc_ref(v_toSnapshot_895_);
v_metaSnap_896_ = lean_ctor_get(v_s_894_, 1);
lean_inc_ref(v_metaSnap_896_);
v_result_x3f_897_ = lean_ctor_get(v_s_894_, 2);
lean_inc(v_result_x3f_897_);
lean_dec_ref(v_s_894_);
if (lean_obj_tag(v_result_x3f_897_) == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_box(0);
v___y_899_ = v___x_909_;
goto v___jp_898_;
}
else
{
lean_object* v_val_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_923_; 
v_val_910_ = lean_ctor_get(v_result_x3f_897_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v_result_x3f_897_);
if (v_isSharedCheck_923_ == 0)
{
v___x_912_ = v_result_x3f_897_;
v_isShared_913_ = v_isSharedCheck_923_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_val_910_);
lean_dec(v_result_x3f_897_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_923_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_firstCmdSnap_914_; lean_object* v_stx_x3f_915_; lean_object* v_reportingRange_916_; lean_object* v___x_917_; uint8_t v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v_firstCmdSnap_914_ = lean_ctor_get(v_val_910_, 1);
lean_inc_ref(v_firstCmdSnap_914_);
lean_dec(v_val_910_);
v_stx_x3f_915_ = lean_ctor_get(v_firstCmdSnap_914_, 0);
lean_inc(v_stx_x3f_915_);
v_reportingRange_916_ = lean_ctor_get(v_firstCmdSnap_914_, 1);
lean_inc(v_reportingRange_916_);
v___x_917_ = ((lean_object*)(l_Lean_Elab_runFrontend___lam__5___closed__0));
v___x_918_ = 1;
v___x_919_ = l_Lean_Language_SnapshotTask_map___redArg(v_firstCmdSnap_914_, v___x_917_, v_stx_x3f_915_, v_reportingRange_916_, v___x_918_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_919_);
v___x_921_ = v___x_912_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
v___y_899_ = v___x_921_;
goto v___jp_898_;
}
}
}
v___jp_898_:
{
lean_object* v_stx_x3f_900_; lean_object* v_reportingRange_901_; uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_stx_x3f_900_ = lean_ctor_get(v_metaSnap_896_, 0);
lean_inc(v_stx_x3f_900_);
v_reportingRange_901_ = lean_ctor_get(v_metaSnap_896_, 1);
lean_inc(v_reportingRange_901_);
v___x_902_ = 1;
v___x_903_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_896_, v___f_893_, v_stx_x3f_900_, v_reportingRange_901_, v___x_902_);
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_mk_empty_array_with_capacity(v___x_904_);
v___x_906_ = lean_array_push(v___x_905_, v___x_903_);
v___x_907_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_899_, v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v_toSnapshot_895_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_927_, lean_object* v_k_928_, uint8_t v_v_929_){
_start:
{
lean_object* v_map_930_; uint8_t v_hasTrace_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_945_; 
v_map_930_ = lean_ctor_get(v_o_927_, 0);
v_hasTrace_931_ = lean_ctor_get_uint8(v_o_927_, sizeof(void*)*1);
v_isSharedCheck_945_ = !lean_is_exclusive(v_o_927_);
if (v_isSharedCheck_945_ == 0)
{
v___x_933_ = v_o_927_;
v_isShared_934_ = v_isSharedCheck_945_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_map_930_);
lean_dec(v_o_927_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_945_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_935_, 0, v_v_929_);
lean_inc(v_k_928_);
v___x_936_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_928_, v___x_935_, v_map_930_);
if (v_hasTrace_931_ == 0)
{
lean_object* v___x_937_; uint8_t v___x_938_; lean_object* v___x_940_; 
v___x_937_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_938_ = l_Lean_Name_isPrefixOf(v___x_937_, v_k_928_);
lean_dec(v_k_928_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_936_);
v___x_940_ = v___x_933_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_936_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*1, v___x_938_);
return v___x_940_;
}
}
else
{
lean_object* v___x_943_; 
lean_dec(v_k_928_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_936_);
v___x_943_ = v___x_933_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_944_, sizeof(void*)*1, v_hasTrace_931_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_946_, lean_object* v_k_947_, lean_object* v_v_948_){
_start:
{
uint8_t v_v_boxed_949_; lean_object* v_res_950_; 
v_v_boxed_949_ = lean_unbox(v_v_948_);
v_res_950_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_946_, v_k_947_, v_v_boxed_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_951_, lean_object* v_opt_952_, uint8_t v_val_953_){
_start:
{
lean_object* v_name_954_; lean_object* v___x_955_; 
v_name_954_ = lean_ctor_get(v_opt_952_, 0);
lean_inc(v_name_954_);
lean_dec_ref(v_opt_952_);
v___x_955_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_951_, v_name_954_, v_val_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_956_, lean_object* v_opt_957_, lean_object* v_val_958_){
_start:
{
uint8_t v_val_boxed_959_; lean_object* v_res_960_; 
v_val_boxed_959_ = lean_unbox(v_val_958_);
v_res_960_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_956_, v_opt_957_, v_val_boxed_959_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_961_, lean_object* v_opt_962_, uint8_t v_val_963_){
_start:
{
lean_object* v_name_964_; lean_object* v_map_965_; uint8_t v___x_966_; 
v_name_964_ = lean_ctor_get(v_opt_962_, 0);
v_map_965_ = lean_ctor_get(v_opts_961_, 0);
v___x_966_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_964_, v_map_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_961_, v_opt_962_, v_val_963_);
return v___x_967_;
}
else
{
lean_dec_ref(v_opt_962_);
return v_opts_961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_968_, lean_object* v_opt_969_, lean_object* v_val_970_){
_start:
{
uint8_t v_val_boxed_971_; lean_object* v_res_972_; 
v_val_boxed_971_ = lean_unbox(v_val_970_);
v_res_972_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_968_, v_opt_969_, v_val_boxed_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_as_973_, size_t v_i_974_, size_t v_stop_975_, lean_object* v_b_976_){
_start:
{
lean_object* v___y_978_; uint8_t v___x_982_; 
v___x_982_ = lean_usize_dec_eq(v_i_974_, v_stop_975_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v_infoTree_x3f_984_; 
v___x_983_ = lean_array_uget_borrowed(v_as_973_, v_i_974_);
v_infoTree_x3f_984_ = lean_ctor_get(v___x_983_, 2);
if (lean_obj_tag(v_infoTree_x3f_984_) == 1)
{
lean_object* v_val_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_val_985_ = lean_ctor_get(v_infoTree_x3f_984_, 0);
v___x_986_ = lean_unsigned_to_nat(1u);
v___x_987_ = lean_mk_empty_array_with_capacity(v___x_986_);
lean_inc(v_val_985_);
v___x_988_ = lean_array_push(v___x_987_, v_val_985_);
v___x_989_ = l_Array_append___redArg(v_b_976_, v___x_988_);
lean_dec_ref(v___x_988_);
v___y_978_ = v___x_989_;
goto v___jp_977_;
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_991_ = l_Array_append___redArg(v_b_976_, v___x_990_);
v___y_978_ = v___x_991_;
goto v___jp_977_;
}
}
else
{
return v_b_976_;
}
v___jp_977_:
{
size_t v___x_979_; size_t v___x_980_; 
v___x_979_ = ((size_t)1ULL);
v___x_980_ = lean_usize_add(v_i_974_, v___x_979_);
v_i_974_ = v___x_980_;
v_b_976_ = v___y_978_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_as_992_, lean_object* v_i_993_, lean_object* v_stop_994_, lean_object* v_b_995_){
_start:
{
size_t v_i_boxed_996_; size_t v_stop_boxed_997_; lean_object* v_res_998_; 
v_i_boxed_996_ = lean_unbox_usize(v_i_993_);
lean_dec(v_i_993_);
v_stop_boxed_997_ = lean_unbox_usize(v_stop_994_);
lean_dec(v_stop_994_);
v_res_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__4(v_as_992_, v_i_boxed_996_, v_stop_boxed_997_, v_b_995_);
lean_dec_ref(v_as_992_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_as_999_, size_t v_i_1000_, size_t v_stop_1001_, lean_object* v_b_1002_){
_start:
{
uint8_t v___x_1003_; 
v___x_1003_ = lean_usize_dec_eq(v_i_1000_, v_stop_1001_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v_diagnostics_1005_; lean_object* v_msgLog_1006_; lean_object* v___x_1007_; size_t v___x_1008_; size_t v___x_1009_; 
v___x_1004_ = lean_array_uget_borrowed(v_as_999_, v_i_1000_);
v_diagnostics_1005_ = lean_ctor_get(v___x_1004_, 1);
v_msgLog_1006_ = lean_ctor_get(v_diagnostics_1005_, 0);
lean_inc_ref(v_msgLog_1006_);
v___x_1007_ = l_Lean_MessageLog_append(v_b_1002_, v_msgLog_1006_);
v___x_1008_ = ((size_t)1ULL);
v___x_1009_ = lean_usize_add(v_i_1000_, v___x_1008_);
v_i_1000_ = v___x_1009_;
v_b_1002_ = v___x_1007_;
goto _start;
}
else
{
return v_b_1002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_as_1011_, lean_object* v_i_1012_, lean_object* v_stop_1013_, lean_object* v_b_1014_){
_start:
{
size_t v_i_boxed_1015_; size_t v_stop_boxed_1016_; lean_object* v_res_1017_; 
v_i_boxed_1015_ = lean_unbox_usize(v_i_1012_);
lean_dec(v_i_1012_);
v_stop_boxed_1016_ = lean_unbox_usize(v_stop_1013_);
lean_dec(v_stop_1013_);
v_res_1017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v_as_1011_, v_i_boxed_1015_, v_stop_boxed_1016_, v_b_1014_);
lean_dec_ref(v_as_1011_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(size_t v_sz_1018_, size_t v_i_1019_, lean_object* v_bs_1020_){
_start:
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_usize_dec_lt(v_i_1019_, v_sz_1018_);
if (v___x_1021_ == 0)
{
return v_bs_1020_;
}
else
{
lean_object* v_v_1022_; lean_object* v_traces_1023_; lean_object* v___x_1024_; lean_object* v_bs_x27_1025_; size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v_v_1022_ = lean_array_uget_borrowed(v_bs_1020_, v_i_1019_);
v_traces_1023_ = lean_ctor_get(v_v_1022_, 3);
lean_inc_ref(v_traces_1023_);
v___x_1024_ = lean_unsigned_to_nat(0u);
v_bs_x27_1025_ = lean_array_uset(v_bs_1020_, v_i_1019_, v___x_1024_);
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_add(v_i_1019_, v___x_1026_);
v___x_1028_ = lean_array_uset(v_bs_x27_1025_, v_i_1019_, v_traces_1023_);
v_i_1019_ = v___x_1027_;
v_bs_1020_ = v___x_1028_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object* v_sz_1030_, lean_object* v_i_1031_, lean_object* v_bs_1032_){
_start:
{
size_t v_sz_boxed_1033_; size_t v_i_boxed_1034_; lean_object* v_res_1035_; 
v_sz_boxed_1033_ = lean_unbox_usize(v_sz_1030_);
lean_dec(v_sz_1030_);
v_i_boxed_1034_ = lean_unbox_usize(v_i_1031_);
lean_dec(v_i_1031_);
v_res_1035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_boxed_1033_, v_i_boxed_1034_, v_bs_1032_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_1036_, size_t v_i_1037_, size_t v_stop_1038_, lean_object* v_b_1039_){
_start:
{
uint8_t v___x_1040_; 
v___x_1040_ = lean_usize_dec_eq(v_i_1037_, v_stop_1038_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; size_t v___x_1045_; size_t v___x_1046_; 
v___x_1041_ = lean_array_uget_borrowed(v_as_1036_, v_i_1037_);
v___x_1042_ = 2;
v___x_1043_ = lean_box(v___x_1042_);
lean_inc(v___x_1041_);
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1041_, v___x_1043_, v_b_1039_);
v___x_1045_ = ((size_t)1ULL);
v___x_1046_ = lean_usize_add(v_i_1037_, v___x_1045_);
v_i_1037_ = v___x_1046_;
v_b_1039_ = v___x_1044_;
goto _start;
}
else
{
return v_b_1039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_1048_, lean_object* v_i_1049_, lean_object* v_stop_1050_, lean_object* v_b_1051_){
_start:
{
size_t v_i_boxed_1052_; size_t v_stop_boxed_1053_; lean_object* v_res_1054_; 
v_i_boxed_1052_ = lean_unbox_usize(v_i_1049_);
lean_dec(v_i_1049_);
v_stop_boxed_1053_ = lean_unbox_usize(v_stop_1050_);
lean_dec(v_stop_1050_);
v_res_1054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_1048_, v_i_boxed_1052_, v_stop_boxed_1053_, v_b_1051_);
lean_dec_ref(v_as_1048_);
return v_res_1054_;
}
}
static double _init_l_Lean_Elab_runFrontend___closed__2(void){
_start:
{
lean_object* v___x_1057_; double v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(1000000000u);
v___x_1058_ = lean_float_of_nat(v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_1062_, lean_object* v_opts_1063_, lean_object* v_fileName_1064_, lean_object* v_mainModuleName_1065_, uint32_t v_trustLevel_1066_, lean_object* v_oleanFileName_x3f_1067_, lean_object* v_ileanFileName_x3f_1068_, uint8_t v_jsonOutput_1069_, lean_object* v_errorOnKinds_1070_, lean_object* v_plugins_1071_, uint8_t v_printStats_1072_, lean_object* v_setup_x3f_1073_){
_start:
{
lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___x_1081_; lean_object* v___f_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___f_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_toSnapshot_1095_; lean_object* v_metaSnap_1096_; lean_object* v_stx_1097_; lean_object* v_result_x3f_1098_; lean_object* v___f_1099_; lean_object* v___x_1100_; double v___x_1101_; double v___x_1102_; double v___x_1103_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1178_; uint8_t v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; uint8_t v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; uint8_t v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1265_; 
v___x_1081_ = lean_io_mono_nanos_now();
v___f_1082_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___x_1083_ = 1;
v___x_1084_ = lean_string_utf8_byte_size(v_input_1062_);
v___x_1085_ = l_Lean_Parser_mkInputContext___redArg(v_input_1062_, v_fileName_1064_, v___x_1083_, v___x_1084_);
v___x_1086_ = l_Lean_internal_cmdlineSnapshots;
v___x_1087_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_1063_, v___x_1086_, v___x_1083_);
v___x_1088_ = l_Lean_Elab_async;
v___x_1089_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_1087_, v___x_1088_, v___x_1083_);
v___x_1090_ = lean_box_uint32(v_trustLevel_1066_);
v___x_1091_ = lean_box(v___x_1083_);
lean_inc(v_mainModuleName_1065_);
lean_inc_ref(v___x_1089_);
v___f_1092_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__1___boxed), 10, 7);
lean_closure_set(v___f_1092_, 0, v_setup_x3f_1073_);
lean_closure_set(v___f_1092_, 1, v___f_1082_);
lean_closure_set(v___f_1092_, 2, v___x_1089_);
lean_closure_set(v___f_1092_, 3, v_plugins_1071_);
lean_closure_set(v___f_1092_, 4, v___x_1090_);
lean_closure_set(v___f_1092_, 5, v___x_1091_);
lean_closure_set(v___f_1092_, 6, v_mainModuleName_1065_);
v___x_1093_ = lean_box(0);
v___x_1094_ = l_Lean_Language_Lean_process(v___f_1092_, v___x_1093_, v___x_1085_);
v_toSnapshot_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc_ref(v_toSnapshot_1095_);
v_metaSnap_1096_ = lean_ctor_get(v___x_1094_, 1);
lean_inc_ref(v_metaSnap_1096_);
v_stx_1097_ = lean_ctor_get(v___x_1094_, 3);
lean_inc(v_stx_1097_);
v_result_x3f_1098_ = lean_ctor_get(v___x_1094_, 4);
lean_inc(v_result_x3f_1098_);
v___f_1099_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__1));
v___x_1100_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1101_ = lean_float_of_nat(v___x_1081_);
v___x_1102_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__2, &l_Lean_Elab_runFrontend___closed__2_once, _init_l_Lean_Elab_runFrontend___closed__2);
v___x_1103_ = lean_float_div(v___x_1101_, v___x_1102_);
if (lean_obj_tag(v_result_x3f_1098_) == 0)
{
v___y_1265_ = v___x_1093_;
goto v___jp_1264_;
}
else
{
lean_object* v_val_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1297_; 
v_val_1285_ = lean_ctor_get(v_result_x3f_1098_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_result_x3f_1098_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1287_ = v_result_x3f_1098_;
v_isShared_1288_ = v_isSharedCheck_1297_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_val_1285_);
lean_dec(v_result_x3f_1098_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1297_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v_processedSnap_1289_; lean_object* v_stx_x3f_1290_; lean_object* v_reportingRange_1291_; lean_object* v___f_1292_; lean_object* v___x_1293_; lean_object* v___x_1295_; 
v_processedSnap_1289_ = lean_ctor_get(v_val_1285_, 1);
lean_inc_ref(v_processedSnap_1289_);
lean_dec(v_val_1285_);
v_stx_x3f_1290_ = lean_ctor_get(v_processedSnap_1289_, 0);
lean_inc(v_stx_x3f_1290_);
v_reportingRange_1291_ = lean_ctor_get(v_processedSnap_1289_, 1);
lean_inc(v_reportingRange_1291_);
v___f_1292_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__4));
v___x_1293_ = l_Lean_Language_SnapshotTask_map___redArg(v_processedSnap_1289_, v___f_1292_, v_stx_x3f_1290_, v_reportingRange_1291_, v___x_1083_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1293_);
v___x_1295_ = v___x_1287_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
v___y_1265_ = v___x_1295_;
goto v___jp_1264_;
}
}
}
v___jp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_runtime_forget(v___y_1076_);
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___y_1077_);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
v___jp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = l_Lean_trace_profiler_output;
v___x_1108_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(v___x_1089_, v___x_1107_);
if (lean_obj_tag(v___x_1108_) == 1)
{
lean_object* v_val_1109_; lean_object* v___x_1110_; size_t v_sz_1111_; size_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_val_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_val_1109_);
lean_dec_ref(v___x_1108_);
lean_inc_ref(v___y_1105_);
v___x_1110_ = l_Lean_Language_SnapshotTree_getAll(v___y_1105_);
v_sz_1111_ = lean_array_size(v___x_1110_);
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_1111_, v___x_1112_, v___x_1110_);
v___x_1114_ = l_Lean_Name_toString(v_mainModuleName_1065_, v___x_1083_);
v___x_1115_ = l_Lean_Firefox_Profile_export(v___x_1114_, v___x_1103_, v___x_1113_, v___x_1089_);
lean_dec_ref(v___x_1089_);
lean_dec_ref(v___x_1113_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref(v___x_1115_);
v___x_1117_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_1116_);
v___x_1118_ = l_Lean_Json_compress(v___x_1117_);
v___x_1119_ = l_IO_FS_writeFile(v_val_1109_, v___x_1118_);
lean_dec_ref(v___x_1118_);
lean_dec(v_val_1109_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_dec_ref(v___x_1119_);
v___y_1076_ = v___y_1105_;
v___y_1077_ = v___y_1106_;
goto v___jp_1075_;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v___y_1106_);
lean_dec_ref(v___y_1105_);
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_val_1109_);
lean_dec_ref(v___y_1106_);
lean_dec_ref(v___y_1105_);
v_a_1128_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1115_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1115_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_dec(v___x_1108_);
lean_dec_ref(v___x_1089_);
lean_dec(v_mainModuleName_1065_);
v___y_1076_ = v___y_1105_;
v___y_1077_ = v___y_1106_;
goto v___jp_1075_;
}
}
v___jp_1136_:
{
lean_object* v_fileMap_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v_fst_1145_; lean_object* v_snd_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v_fileMap_1141_ = lean_ctor_get(v___x_1085_, 2);
lean_inc_ref(v_fileMap_1141_);
lean_dec_ref(v___x_1085_);
v___x_1142_ = 0;
v___x_1143_ = l_Lean_Server_findModuleRefs(v_fileMap_1141_, v___y_1140_, v___x_1142_, v___x_1142_);
lean_dec_ref(v___y_1140_);
v___x_1144_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_1143_);
v_fst_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_fst_1145_);
v_snd_1146_ = lean_ctor_get(v___x_1144_, 1);
lean_inc(v_snd_1146_);
lean_dec_ref(v___x_1144_);
v___x_1147_ = lean_unsigned_to_nat(5u);
v___x_1148_ = l_Lean_Server_collectImports(v_stx_1097_);
lean_inc(v_mainModuleName_1065_);
v___x_1149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v_mainModuleName_1065_);
lean_ctor_set(v___x_1149_, 2, v___x_1148_);
lean_ctor_set(v___x_1149_, 3, v_fst_1145_);
lean_ctor_set(v___x_1149_, 4, v_snd_1146_);
v___x_1150_ = l_Lean_Server_instToJsonIlean_toJson(v___x_1149_);
v___x_1151_ = l_Lean_Json_compress(v___x_1150_);
v___x_1152_ = l_IO_FS_writeFile(v___y_1138_, v___x_1151_);
lean_dec_ref(v___x_1151_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_dec_ref(v___x_1152_);
v___y_1105_ = v___y_1137_;
v___y_1106_ = v___y_1139_;
goto v___jp_1104_;
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v___y_1139_);
lean_dec_ref(v___y_1137_);
lean_dec_ref(v___x_1089_);
lean_dec(v_mainModuleName_1065_);
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
v___jp_1161_:
{
if (lean_obj_tag(v_ileanFileName_x3f_1068_) == 1)
{
lean_object* v_val_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v_val_1165_ = lean_ctor_get(v_ileanFileName_x3f_1068_, 0);
lean_inc_ref(v___y_1162_);
v___x_1166_ = l_Lean_Language_SnapshotTree_getAll(v___y_1162_);
v___x_1167_ = lean_mk_empty_array_with_capacity(v___y_1163_);
v___x_1168_ = lean_array_get_size(v___x_1166_);
v___x_1169_ = lean_nat_dec_lt(v___y_1163_, v___x_1168_);
lean_dec(v___y_1163_);
if (v___x_1169_ == 0)
{
lean_dec_ref(v___x_1166_);
v___y_1137_ = v___y_1162_;
v___y_1138_ = v_val_1165_;
v___y_1139_ = v___y_1164_;
v___y_1140_ = v___x_1167_;
goto v___jp_1136_;
}
else
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_nat_dec_le(v___x_1168_, v___x_1168_);
if (v___x_1170_ == 0)
{
if (v___x_1169_ == 0)
{
lean_dec_ref(v___x_1166_);
v___y_1137_ = v___y_1162_;
v___y_1138_ = v_val_1165_;
v___y_1139_ = v___y_1164_;
v___y_1140_ = v___x_1167_;
goto v___jp_1136_;
}
else
{
size_t v___x_1171_; size_t v___x_1172_; lean_object* v___x_1173_; 
v___x_1171_ = ((size_t)0ULL);
v___x_1172_ = lean_usize_of_nat(v___x_1168_);
v___x_1173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__4(v___x_1166_, v___x_1171_, v___x_1172_, v___x_1167_);
lean_dec_ref(v___x_1166_);
v___y_1137_ = v___y_1162_;
v___y_1138_ = v_val_1165_;
v___y_1139_ = v___y_1164_;
v___y_1140_ = v___x_1173_;
goto v___jp_1136_;
}
}
else
{
size_t v___x_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = ((size_t)0ULL);
v___x_1175_ = lean_usize_of_nat(v___x_1168_);
v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__4(v___x_1166_, v___x_1174_, v___x_1175_, v___x_1167_);
lean_dec_ref(v___x_1166_);
v___y_1137_ = v___y_1162_;
v___y_1138_ = v_val_1165_;
v___y_1139_ = v___y_1164_;
v___y_1140_ = v___x_1176_;
goto v___jp_1136_;
}
}
}
else
{
lean_dec(v___y_1163_);
lean_dec(v_stx_1097_);
lean_dec_ref(v___x_1085_);
v___y_1105_ = v___y_1162_;
v___y_1106_ = v___y_1164_;
goto v___jp_1104_;
}
}
v___jp_1177_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1188_ = lean_box(v___x_1083_);
v___x_1189_ = lean_box(v___y_1179_);
v___f_1190_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1190_, 0, v___y_1181_);
lean_closure_set(v___f_1190_, 1, v___y_1187_);
lean_closure_set(v___f_1190_, 2, v___y_1180_);
lean_closure_set(v___f_1190_, 3, v___y_1178_);
lean_closure_set(v___f_1190_, 4, v___x_1188_);
lean_closure_set(v___f_1190_, 5, v___x_1189_);
v___x_1191_ = lean_box(0);
v___x_1192_ = l_Lean_profileitIOUnsafe___redArg(v___y_1183_, v___y_1185_, v___f_1190_, v___x_1191_);
lean_dec_ref(v___y_1185_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_dec_ref(v___x_1192_);
v___y_1162_ = v___y_1182_;
v___y_1163_ = v___y_1184_;
v___y_1164_ = v___y_1186_;
goto v___jp_1161_;
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1182_);
lean_dec(v_stx_1097_);
lean_dec_ref(v___x_1089_);
lean_dec_ref(v___x_1085_);
lean_dec(v_mainModuleName_1065_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
v___jp_1201_:
{
if (v___y_1206_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_1067_) == 1)
{
lean_object* v_val_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v_val_1209_ = lean_ctor_get(v_oleanFileName_x3f_1067_, 0);
lean_inc(v_val_1209_);
lean_dec_ref(v_oleanFileName_x3f_1067_);
v___x_1210_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__3));
v___x_1211_ = l_Lean_MessageLog_empty;
lean_inc_ref(v___y_1205_);
v___x_1212_ = l_Lean_Language_SnapshotTree_getAll(v___y_1205_);
v___x_1213_ = lean_array_get_size(v___x_1212_);
v___x_1214_ = lean_nat_dec_lt(v___y_1207_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_dec_ref(v___x_1212_);
lean_inc_ref(v___y_1203_);
v___y_1178_ = v_val_1209_;
v___y_1179_ = v___y_1202_;
v___y_1180_ = v___y_1203_;
v___y_1181_ = v___y_1204_;
v___y_1182_ = v___y_1205_;
v___y_1183_ = v___x_1210_;
v___y_1184_ = v___y_1207_;
v___y_1185_ = v___y_1203_;
v___y_1186_ = v___y_1208_;
v___y_1187_ = v___x_1211_;
goto v___jp_1177_;
}
else
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_nat_dec_le(v___x_1213_, v___x_1213_);
if (v___x_1215_ == 0)
{
if (v___x_1214_ == 0)
{
lean_dec_ref(v___x_1212_);
lean_inc_ref(v___y_1203_);
v___y_1178_ = v_val_1209_;
v___y_1179_ = v___y_1202_;
v___y_1180_ = v___y_1203_;
v___y_1181_ = v___y_1204_;
v___y_1182_ = v___y_1205_;
v___y_1183_ = v___x_1210_;
v___y_1184_ = v___y_1207_;
v___y_1185_ = v___y_1203_;
v___y_1186_ = v___y_1208_;
v___y_1187_ = v___x_1211_;
goto v___jp_1177_;
}
else
{
size_t v___x_1216_; size_t v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = ((size_t)0ULL);
v___x_1217_ = lean_usize_of_nat(v___x_1213_);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v___x_1212_, v___x_1216_, v___x_1217_, v___x_1211_);
lean_dec_ref(v___x_1212_);
lean_inc_ref(v___y_1203_);
v___y_1178_ = v_val_1209_;
v___y_1179_ = v___y_1202_;
v___y_1180_ = v___y_1203_;
v___y_1181_ = v___y_1204_;
v___y_1182_ = v___y_1205_;
v___y_1183_ = v___x_1210_;
v___y_1184_ = v___y_1207_;
v___y_1185_ = v___y_1203_;
v___y_1186_ = v___y_1208_;
v___y_1187_ = v___x_1218_;
goto v___jp_1177_;
}
}
else
{
size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = ((size_t)0ULL);
v___x_1220_ = lean_usize_of_nat(v___x_1213_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v___x_1212_, v___x_1219_, v___x_1220_, v___x_1211_);
lean_dec_ref(v___x_1212_);
lean_inc_ref(v___y_1203_);
v___y_1178_ = v_val_1209_;
v___y_1179_ = v___y_1202_;
v___y_1180_ = v___y_1203_;
v___y_1181_ = v___y_1204_;
v___y_1182_ = v___y_1205_;
v___y_1183_ = v___x_1210_;
v___y_1184_ = v___y_1207_;
v___y_1185_ = v___y_1203_;
v___y_1186_ = v___y_1208_;
v___y_1187_ = v___x_1221_;
goto v___jp_1177_;
}
}
}
else
{
lean_dec_ref(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v_oleanFileName_x3f_1067_);
v___y_1162_ = v___y_1205_;
v___y_1163_ = v___y_1207_;
v___y_1164_ = v___y_1208_;
goto v___jp_1161_;
}
}
else
{
lean_object* v___x_1222_; 
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v_stx_1097_);
lean_dec_ref(v___x_1089_);
lean_dec_ref(v___x_1085_);
lean_dec(v_oleanFileName_x3f_1067_);
lean_dec(v_mainModuleName_1065_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1093_);
return v___x_1222_;
}
}
v___jp_1223_:
{
lean_object* v___x_1227_; 
lean_inc_ref(v___y_1224_);
v___x_1227_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_1224_, v___x_1089_, v_jsonOutput_1069_, v___y_1226_);
lean_dec(v___y_1226_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1255_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1255_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1255_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___x_1094_);
if (lean_obj_tag(v___x_1232_) == 1)
{
lean_object* v_val_1233_; lean_object* v_env_1234_; lean_object* v_scopes_1235_; lean_object* v___x_1236_; 
lean_del_object(v___x_1230_);
v_val_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_val_1233_);
lean_dec_ref(v___x_1232_);
v_env_1234_ = lean_ctor_get(v_val_1233_, 0);
lean_inc_ref(v_env_1234_);
v_scopes_1235_ = lean_ctor_get(v_val_1233_, 2);
lean_inc(v_scopes_1235_);
lean_dec(v_val_1233_);
lean_inc(v___y_1225_);
v___x_1236_ = l_List_get_x21Internal___redArg(v___x_1100_, v_scopes_1235_, v___y_1225_);
lean_dec(v_scopes_1235_);
if (v_printStats_1072_ == 0)
{
lean_object* v_opts_1237_; uint8_t v___x_1238_; uint8_t v___x_1239_; 
v_opts_1237_ = lean_ctor_get(v___x_1236_, 1);
lean_inc_ref(v_opts_1237_);
lean_dec(v___x_1236_);
v___x_1238_ = lean_unbox(v_a_1228_);
v___x_1239_ = lean_unbox(v_a_1228_);
lean_dec(v_a_1228_);
lean_inc_ref(v_env_1234_);
v___y_1202_ = v___x_1238_;
v___y_1203_ = v_opts_1237_;
v___y_1204_ = v_env_1234_;
v___y_1205_ = v___y_1224_;
v___y_1206_ = v___x_1239_;
v___y_1207_ = v___y_1225_;
v___y_1208_ = v_env_1234_;
goto v___jp_1201_;
}
else
{
lean_object* v_opts_1240_; lean_object* v___x_1241_; 
v_opts_1240_ = lean_ctor_get(v___x_1236_, 1);
lean_inc_ref(v_opts_1240_);
lean_dec(v___x_1236_);
lean_inc_ref(v_env_1234_);
v___x_1241_ = l_Lean_Environment_displayStats(v_env_1234_);
if (lean_obj_tag(v___x_1241_) == 0)
{
uint8_t v___x_1242_; uint8_t v___x_1243_; 
lean_dec_ref(v___x_1241_);
v___x_1242_ = lean_unbox(v_a_1228_);
v___x_1243_ = lean_unbox(v_a_1228_);
lean_dec(v_a_1228_);
lean_inc_ref(v_env_1234_);
v___y_1202_ = v___x_1242_;
v___y_1203_ = v_opts_1240_;
v___y_1204_ = v_env_1234_;
v___y_1205_ = v___y_1224_;
v___y_1206_ = v___x_1243_;
v___y_1207_ = v___y_1225_;
v___y_1208_ = v_env_1234_;
goto v___jp_1201_;
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v_opts_1240_);
lean_dec_ref(v_env_1234_);
lean_dec(v_a_1228_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v_stx_1097_);
lean_dec_ref(v___x_1089_);
lean_dec_ref(v___x_1085_);
lean_dec(v_oleanFileName_x3f_1067_);
lean_dec(v_mainModuleName_1065_);
v_a_1244_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1241_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1241_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
else
{
lean_object* v___x_1253_; 
lean_dec(v___x_1232_);
lean_dec(v_a_1228_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v_stx_1097_);
lean_dec_ref(v___x_1089_);
lean_dec_ref(v___x_1085_);
lean_dec(v_oleanFileName_x3f_1067_);
lean_dec(v_mainModuleName_1065_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1093_);
v___x_1253_ = v___x_1230_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1093_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v_stx_1097_);
lean_dec_ref(v___x_1094_);
lean_dec_ref(v___x_1089_);
lean_dec_ref(v___x_1085_);
lean_dec(v_oleanFileName_x3f_1067_);
lean_dec(v_mainModuleName_1065_);
v_a_1256_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1227_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1227_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
v___jp_1264_:
{
lean_object* v_stx_x3f_1266_; lean_object* v_reportingRange_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_stx_x3f_1266_ = lean_ctor_get(v_metaSnap_1096_, 0);
lean_inc(v_stx_x3f_1266_);
v_reportingRange_1267_ = lean_ctor_get(v_metaSnap_1096_, 1);
lean_inc(v_reportingRange_1267_);
v___x_1268_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_1096_, v___f_1099_, v_stx_x3f_1266_, v_reportingRange_1267_, v___x_1083_);
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = lean_mk_empty_array_with_capacity(v___x_1269_);
v___x_1271_ = lean_array_push(v___x_1270_, v___x_1268_);
v___x_1272_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_1265_, v___x_1271_);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_toSnapshot_1095_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_box(1);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = lean_array_get_size(v_errorOnKinds_1070_);
v___x_1277_ = lean_nat_dec_lt(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
v___y_1224_ = v___x_1273_;
v___y_1225_ = v___x_1275_;
v___y_1226_ = v___x_1274_;
goto v___jp_1223_;
}
else
{
uint8_t v___x_1278_; 
v___x_1278_ = lean_nat_dec_le(v___x_1276_, v___x_1276_);
if (v___x_1278_ == 0)
{
if (v___x_1277_ == 0)
{
v___y_1224_ = v___x_1273_;
v___y_1225_ = v___x_1275_;
v___y_1226_ = v___x_1274_;
goto v___jp_1223_;
}
else
{
size_t v___x_1279_; size_t v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = ((size_t)0ULL);
v___x_1280_ = lean_usize_of_nat(v___x_1276_);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_errorOnKinds_1070_, v___x_1279_, v___x_1280_, v___x_1274_);
v___y_1224_ = v___x_1273_;
v___y_1225_ = v___x_1275_;
v___y_1226_ = v___x_1281_;
goto v___jp_1223_;
}
}
else
{
size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = ((size_t)0ULL);
v___x_1283_ = lean_usize_of_nat(v___x_1276_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_errorOnKinds_1070_, v___x_1282_, v___x_1283_, v___x_1274_);
v___y_1224_ = v___x_1273_;
v___y_1225_ = v___x_1275_;
v___y_1226_ = v___x_1284_;
goto v___jp_1223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_1298_, lean_object* v_opts_1299_, lean_object* v_fileName_1300_, lean_object* v_mainModuleName_1301_, lean_object* v_trustLevel_1302_, lean_object* v_oleanFileName_x3f_1303_, lean_object* v_ileanFileName_x3f_1304_, lean_object* v_jsonOutput_1305_, lean_object* v_errorOnKinds_1306_, lean_object* v_plugins_1307_, lean_object* v_printStats_1308_, lean_object* v_setup_x3f_1309_, lean_object* v_a_1310_){
_start:
{
uint32_t v_trustLevel_boxed_1311_; uint8_t v_jsonOutput_boxed_1312_; uint8_t v_printStats_boxed_1313_; lean_object* v_res_1314_; 
v_trustLevel_boxed_1311_ = lean_unbox_uint32(v_trustLevel_1302_);
lean_dec(v_trustLevel_1302_);
v_jsonOutput_boxed_1312_ = lean_unbox(v_jsonOutput_1305_);
v_printStats_boxed_1313_ = lean_unbox(v_printStats_1308_);
v_res_1314_ = l_Lean_Elab_runFrontend(v_input_1298_, v_opts_1299_, v_fileName_1300_, v_mainModuleName_1301_, v_trustLevel_boxed_1311_, v_oleanFileName_x3f_1303_, v_ileanFileName_x3f_1304_, v_jsonOutput_boxed_1312_, v_errorOnKinds_1306_, v_plugins_1307_, v_printStats_boxed_1313_, v_setup_x3f_1309_);
lean_dec_ref(v_errorOnKinds_1306_);
lean_dec(v_ileanFileName_x3f_1304_);
return v_res_1314_;
}
}
lean_object* runtime_initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_References(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Profiler(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_PersistentLintLog(uint8_t builtin);
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
