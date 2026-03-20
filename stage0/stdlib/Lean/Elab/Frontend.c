// Lean compiler output
// Module: Lean.Elab.Frontend
// Imports: public import Lean.Language.Lean public import Lean.Server.References public import Lean.Util.Profiler import Lean.Compiler.Options
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
lean_object* l_Lean_writeModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
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
static const lean_closure_object l_Lean_Elab_runFrontend___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___lam__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_runFrontend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__0_value;
static const lean_closure_object l_Lean_Elab_runFrontend___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__1 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__1_value;
static lean_once_cell_t l_Lean_Elab_runFrontend___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_runFrontend___closed__2;
static const lean_string_object l_Lean_Elab_runFrontend___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ".olean serialization"};
static const lean_object* l_Lean_Elab_runFrontend___closed__3 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__3_value;
static const lean_closure_object l_Lean_Elab_runFrontend___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__4, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_runFrontend___closed__1_value)} };
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
lean_inc(v___x_137_);
v___x_147_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_130_, v___x_146_, v___x_137_);
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
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_329_; 
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
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0(lean_object* v_a_334_, lean_object* v___x_335_, lean_object* v_a_336_, lean_object* v_messages_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Parser_parseCommand(v_a_334_, v___x_335_, v_a_336_, v_messages_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_a_346_; lean_object* v___x_347_; lean_object* v_a_348_; lean_object* v_env_349_; lean_object* v_messages_350_; lean_object* v_scopes_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_opts_354_; lean_object* v_currNamespace_355_; lean_object* v_openDecls_356_; lean_object* v___x_357_; lean_object* v___f_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_snd_362_; lean_object* v_fst_363_; lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___x_366_; lean_object* v_commandState_367_; lean_object* v_parserState_368_; lean_object* v_cmdPos_369_; lean_object* v_commands_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_400_; 
v___x_344_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_342_);
lean_dec_ref(v___x_344_);
v___x_345_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_342_);
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref(v___x_345_);
v___x_347_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_342_);
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref(v___x_347_);
v_env_349_ = lean_ctor_get(v_a_346_, 0);
lean_inc_ref(v_env_349_);
v_messages_350_ = lean_ctor_get(v_a_346_, 1);
lean_inc_ref(v_messages_350_);
v_scopes_351_ = lean_ctor_get(v_a_346_, 2);
lean_inc(v_scopes_351_);
lean_dec(v_a_346_);
v___x_352_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_353_ = l_List_head_x21___redArg(v___x_352_, v_scopes_351_);
lean_dec(v_scopes_351_);
v_opts_354_ = lean_ctor_get(v___x_353_, 1);
lean_inc_ref(v_opts_354_);
v_currNamespace_355_ = lean_ctor_get(v___x_353_, 2);
lean_inc(v_currNamespace_355_);
v_openDecls_356_ = lean_ctor_get(v___x_353_, 3);
lean_inc(v_openDecls_356_);
lean_dec(v___x_353_);
lean_inc_ref(v_opts_354_);
v___x_357_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_357_, 0, v_env_349_);
lean_ctor_set(v___x_357_, 1, v_opts_354_);
lean_ctor_set(v___x_357_, 2, v_currNamespace_355_);
lean_ctor_set(v___x_357_, 3, v_openDecls_356_);
lean_inc_ref(v_a_341_);
v___f_358_ = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommand___lam__0), 5, 4);
lean_closure_set(v___f_358_, 0, v_a_341_);
lean_closure_set(v___f_358_, 1, v___x_357_);
lean_closure_set(v___f_358_, 2, v_a_348_);
lean_closure_set(v___f_358_, 3, v_messages_350_);
v___x_359_ = ((lean_object*)(l_Lean_Elab_Frontend_processCommand___closed__0));
v___x_360_ = lean_box(0);
v___x_361_ = lean_profileit(v___x_359_, v_opts_354_, v___f_358_, v___x_360_);
lean_dec_ref(v_opts_354_);
v_snd_362_ = lean_ctor_get(v___x_361_, 1);
lean_inc(v_snd_362_);
v_fst_363_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_fst_363_);
lean_dec(v___x_361_);
v_fst_364_ = lean_ctor_get(v_snd_362_, 0);
lean_inc(v_fst_364_);
v_snd_365_ = lean_ctor_get(v_snd_362_, 1);
lean_inc(v_snd_365_);
lean_dec(v_snd_362_);
v___x_366_ = lean_st_ref_take(v_a_342_);
v_commandState_367_ = lean_ctor_get(v___x_366_, 0);
v_parserState_368_ = lean_ctor_get(v___x_366_, 1);
v_cmdPos_369_ = lean_ctor_get(v___x_366_, 2);
v_commands_370_ = lean_ctor_get(v___x_366_, 3);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_400_ == 0)
{
v___x_372_ = v___x_366_;
v_isShared_373_ = v_isSharedCheck_400_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_commands_370_);
lean_inc(v_cmdPos_369_);
lean_inc(v_parserState_368_);
lean_inc(v_commandState_367_);
lean_dec(v___x_366_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_400_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
lean_inc(v_fst_363_);
v___x_374_ = lean_array_push(v_commands_370_, v_fst_363_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 3, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_commandState_367_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_parserState_368_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_cmdPos_369_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v___x_374_);
v___x_376_ = v_reuseFailAlloc_399_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = lean_st_ref_set(v_a_342_, v___x_376_);
v___x_378_ = l_Lean_Elab_Frontend_setParserState___redArg(v_fst_364_, v_a_342_);
lean_dec_ref(v___x_378_);
v___x_379_ = l_Lean_Elab_Frontend_setMessages___redArg(v_snd_365_, v_a_342_);
lean_dec_ref(v___x_379_);
lean_inc(v_fst_363_);
v___x_380_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_fst_363_, v_a_341_, v_a_342_);
lean_dec_ref(v_a_341_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_389_; 
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; 
v_unused_390_ = lean_ctor_get(v___x_380_, 0);
lean_dec(v_unused_390_);
v___x_382_ = v___x_380_;
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
else
{
lean_dec(v___x_380_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_389_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_384_ = l_Lean_Parser_isTerminalCommand(v_fst_363_);
v___x_385_ = lean_box(v___x_384_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_385_);
v___x_387_ = v___x_382_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec(v_fst_363_);
v_a_391_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_380_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_380_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Elab_Frontend_processCommand(v_a_401_, v_a_402_);
lean_dec(v_a_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; 
lean_inc_ref(v_a_405_);
v___x_408_ = l_Lean_Elab_Frontend_processCommand(v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_419_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_419_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_419_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_419_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
uint8_t v___x_413_; 
v___x_413_ = lean_unbox(v_a_409_);
lean_dec(v_a_409_);
if (v___x_413_ == 0)
{
lean_del_object(v___x_411_);
goto _start;
}
else
{
lean_object* v___x_415_; lean_object* v___x_417_; 
lean_dec_ref(v_a_405_);
v___x_415_ = lean_box(0);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_415_);
v___x_417_ = v___x_411_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec_ref(v_a_405_);
v_a_420_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_408_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_408_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands___boxed(lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Elab_Frontend_processCommands(v_a_428_, v_a_429_);
lean_dec(v_a_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object* v_as_432_, size_t v_i_433_, size_t v_stop_434_, lean_object* v_b_435_){
_start:
{
lean_object* v___y_437_; uint8_t v___x_441_; 
v___x_441_ = lean_usize_dec_eq(v_i_433_, v_stop_434_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_array_uget_borrowed(v_as_432_, v_i_433_);
if (lean_obj_tag(v___x_442_) == 0)
{
v___y_437_ = v_b_435_;
goto v___jp_436_;
}
else
{
lean_object* v_val_443_; lean_object* v___x_444_; 
v_val_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_val_443_);
v___x_444_ = lean_array_push(v_b_435_, v_val_443_);
v___y_437_ = v___x_444_;
goto v___jp_436_;
}
}
else
{
return v_b_435_;
}
v___jp_436_:
{
size_t v___x_438_; size_t v___x_439_; 
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_add(v_i_433_, v___x_438_);
v_i_433_ = v___x_439_;
v_b_435_ = v___y_437_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object* v_as_445_, lean_object* v_i_446_, lean_object* v_stop_447_, lean_object* v_b_448_){
_start:
{
size_t v_i_boxed_449_; size_t v_stop_boxed_450_; lean_object* v_res_451_; 
v_i_boxed_449_ = lean_unbox_usize(v_i_446_);
lean_dec(v_i_446_);
v_stop_boxed_450_ = lean_unbox_usize(v_stop_447_);
lean_dec(v_stop_447_);
v_res_451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_445_, v_i_boxed_449_, v_stop_boxed_450_, v_b_448_);
lean_dec_ref(v_as_445_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object* v_as_454_, lean_object* v_start_455_, lean_object* v_stop_456_){
_start:
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_458_ = lean_nat_dec_lt(v_start_455_, v_stop_456_);
if (v___x_458_ == 0)
{
return v___x_457_;
}
else
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_array_get_size(v_as_454_);
v___x_460_ = lean_nat_dec_le(v_stop_456_, v___x_459_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; 
v___x_461_ = lean_nat_dec_lt(v_start_455_, v___x_459_);
if (v___x_461_ == 0)
{
return v___x_457_;
}
else
{
size_t v___x_462_; size_t v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_usize_of_nat(v_start_455_);
v___x_463_ = lean_usize_of_nat(v___x_459_);
v___x_464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_454_, v___x_462_, v___x_463_, v___x_457_);
return v___x_464_;
}
}
else
{
size_t v___x_465_; size_t v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_usize_of_nat(v_start_455_);
v___x_466_ = lean_usize_of_nat(v_stop_456_);
v___x_467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_454_, v___x_465_, v___x_466_, v___x_457_);
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object* v_as_468_, lean_object* v_start_469_, lean_object* v_stop_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v_as_468_, v_start_469_, v_stop_470_);
lean_dec(v_stop_470_);
lean_dec(v_start_469_);
lean_dec_ref(v_as_468_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t v_sz_472_, size_t v_i_473_, lean_object* v_bs_474_){
_start:
{
uint8_t v___x_475_; 
v___x_475_ = lean_usize_dec_lt(v_i_473_, v_sz_472_);
if (v___x_475_ == 0)
{
return v_bs_474_;
}
else
{
lean_object* v_v_476_; lean_object* v_elabSnap_477_; lean_object* v_infoTreeSnap_478_; lean_object* v___x_479_; lean_object* v_infoTree_x3f_480_; lean_object* v___x_481_; lean_object* v_bs_x27_482_; size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; 
v_v_476_ = lean_array_uget_borrowed(v_bs_474_, v_i_473_);
v_elabSnap_477_ = lean_ctor_get(v_v_476_, 3);
v_infoTreeSnap_478_ = lean_ctor_get(v_elabSnap_477_, 3);
lean_inc_ref(v_infoTreeSnap_478_);
v___x_479_ = l_Lean_Language_SnapshotTask_get___redArg(v_infoTreeSnap_478_);
v_infoTree_x3f_480_ = lean_ctor_get(v___x_479_, 2);
lean_inc(v_infoTree_x3f_480_);
lean_dec(v___x_479_);
v___x_481_ = lean_unsigned_to_nat(0u);
v_bs_x27_482_ = lean_array_uset(v_bs_474_, v_i_473_, v___x_481_);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_add(v_i_473_, v___x_483_);
v___x_485_ = lean_array_uset(v_bs_x27_482_, v_i_473_, v_infoTree_x3f_480_);
v_i_473_ = v___x_484_;
v_bs_474_ = v___x_485_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object* v_sz_487_, lean_object* v_i_488_, lean_object* v_bs_489_){
_start:
{
size_t v_sz_boxed_490_; size_t v_i_boxed_491_; lean_object* v_res_492_; 
v_sz_boxed_490_ = lean_unbox_usize(v_sz_487_);
lean_dec(v_sz_487_);
v_i_boxed_491_ = lean_unbox_usize(v_i_488_);
lean_dec(v_i_488_);
v_res_492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_boxed_490_, v_i_boxed_491_, v_bs_489_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(lean_object* v_as_493_, size_t v_i_494_, size_t v_stop_495_, lean_object* v_b_496_){
_start:
{
uint8_t v___x_497_; 
v___x_497_ = lean_usize_dec_eq(v_i_494_, v_stop_495_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; size_t v___x_500_; size_t v___x_501_; 
v___x_498_ = lean_array_uget_borrowed(v_as_493_, v_i_494_);
lean_inc(v___x_498_);
v___x_499_ = l_Lean_MessageLog_append(v_b_496_, v___x_498_);
v___x_500_ = ((size_t)1ULL);
v___x_501_ = lean_usize_add(v_i_494_, v___x_500_);
v_i_494_ = v___x_501_;
v_b_496_ = v___x_499_;
goto _start;
}
else
{
return v_b_496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object* v_as_503_, lean_object* v_i_504_, lean_object* v_stop_505_, lean_object* v_b_506_){
_start:
{
size_t v_i_boxed_507_; size_t v_stop_boxed_508_; lean_object* v_res_509_; 
v_i_boxed_507_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_stop_boxed_508_ = lean_unbox_usize(v_stop_505_);
lean_dec(v_stop_505_);
v_res_509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_as_503_, v_i_boxed_507_, v_stop_boxed_508_, v_b_506_);
lean_dec_ref(v_as_503_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t v_sz_510_, size_t v_i_511_, lean_object* v_bs_512_){
_start:
{
uint8_t v___x_513_; 
v___x_513_ = lean_usize_dec_lt(v_i_511_, v_sz_510_);
if (v___x_513_ == 0)
{
return v_bs_512_;
}
else
{
lean_object* v_v_514_; lean_object* v_stx_515_; lean_object* v___x_516_; lean_object* v_bs_x27_517_; size_t v___x_518_; size_t v___x_519_; lean_object* v___x_520_; 
v_v_514_ = lean_array_uget_borrowed(v_bs_512_, v_i_511_);
v_stx_515_ = lean_ctor_get(v_v_514_, 1);
lean_inc(v_stx_515_);
v___x_516_ = lean_unsigned_to_nat(0u);
v_bs_x27_517_ = lean_array_uset(v_bs_512_, v_i_511_, v___x_516_);
v___x_518_ = ((size_t)1ULL);
v___x_519_ = lean_usize_add(v_i_511_, v___x_518_);
v___x_520_ = lean_array_uset(v_bs_x27_517_, v_i_511_, v_stx_515_);
v_i_511_ = v___x_519_;
v_bs_512_ = v___x_520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object* v_sz_522_, lean_object* v_i_523_, lean_object* v_bs_524_){
_start:
{
size_t v_sz_boxed_525_; size_t v_i_boxed_526_; lean_object* v_res_527_; 
v_sz_boxed_525_ = lean_unbox_usize(v_sz_522_);
lean_dec(v_sz_522_);
v_i_boxed_526_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_boxed_525_, v_i_boxed_526_, v_bs_524_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(size_t v_sz_528_, size_t v_i_529_, lean_object* v_bs_530_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = lean_usize_dec_lt(v_i_529_, v_sz_528_);
if (v___x_531_ == 0)
{
return v_bs_530_;
}
else
{
lean_object* v_v_532_; lean_object* v_diagnostics_533_; lean_object* v_msgLog_534_; lean_object* v___x_535_; lean_object* v_bs_x27_536_; size_t v___x_537_; size_t v___x_538_; lean_object* v___x_539_; 
v_v_532_ = lean_array_uget_borrowed(v_bs_530_, v_i_529_);
v_diagnostics_533_ = lean_ctor_get(v_v_532_, 1);
v_msgLog_534_ = lean_ctor_get(v_diagnostics_533_, 0);
lean_inc_ref(v_msgLog_534_);
v___x_535_ = lean_unsigned_to_nat(0u);
v_bs_x27_536_ = lean_array_uset(v_bs_530_, v_i_529_, v___x_535_);
v___x_537_ = ((size_t)1ULL);
v___x_538_ = lean_usize_add(v_i_529_, v___x_537_);
v___x_539_ = lean_array_uset(v_bs_x27_536_, v_i_529_, v_msgLog_534_);
v_i_529_ = v___x_538_;
v_bs_530_ = v___x_539_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3___boxed(lean_object* v_sz_541_, lean_object* v_i_542_, lean_object* v_bs_543_){
_start:
{
size_t v_sz_boxed_544_; size_t v_i_boxed_545_; lean_object* v_res_546_; 
v_sz_boxed_544_ = lean_unbox_usize(v_sz_541_);
lean_dec(v_sz_541_);
v_i_boxed_545_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_sz_boxed_544_, v_i_boxed_545_, v_bs_543_);
return v_res_546_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = lean_unsigned_to_nat(32u);
v___x_548_ = lean_mk_empty_array_with_capacity(v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1(void){
_start:
{
size_t v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_550_ = ((size_t)5ULL);
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = lean_unsigned_to_nat(32u);
v___x_553_ = lean_mk_empty_array_with_capacity(v___x_552_);
v___x_554_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0);
v___x_555_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v___x_553_);
lean_ctor_set(v___x_555_, 2, v___x_551_);
lean_ctor_set(v___x_555_, 3, v___x_551_);
lean_ctor_set_usize(v___x_555_, 4, v___x_550_);
return v___x_555_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = l_Lean_NameSet_empty;
v___x_557_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1);
v___x_558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
lean_ctor_set(v___x_558_, 2, v___x_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(lean_object* v_inputCtx_559_, lean_object* v_initialSnap_560_, lean_object* v_t_561_, lean_object* v_commands_562_){
_start:
{
lean_object* v_snap_564_; lean_object* v_parserState_565_; lean_object* v_elabSnap_566_; lean_object* v_nextCmdSnap_x3f_567_; lean_object* v_commands_568_; 
v_snap_564_ = lean_task_get_own(v_t_561_);
v_parserState_565_ = lean_ctor_get(v_snap_564_, 2);
lean_inc_ref(v_parserState_565_);
v_elabSnap_566_ = lean_ctor_get(v_snap_564_, 3);
lean_inc_ref(v_elabSnap_566_);
v_nextCmdSnap_x3f_567_ = lean_ctor_get(v_snap_564_, 4);
lean_inc(v_nextCmdSnap_x3f_567_);
v_commands_568_ = lean_array_push(v_commands_562_, v_snap_564_);
if (lean_obj_tag(v_nextCmdSnap_x3f_567_) == 1)
{
lean_object* v_val_569_; lean_object* v_task_570_; 
lean_dec_ref(v_elabSnap_566_);
lean_dec_ref(v_parserState_565_);
v_val_569_ = lean_ctor_get(v_nextCmdSnap_x3f_567_, 0);
lean_inc(v_val_569_);
lean_dec_ref(v_nextCmdSnap_x3f_567_);
v_task_570_ = lean_ctor_get(v_val_569_, 3);
lean_inc_ref(v_task_570_);
lean_dec(v_val_569_);
v_t_561_ = v_task_570_;
v_commands_562_ = v_commands_568_;
goto _start;
}
else
{
lean_object* v___x_572_; lean_object* v___y_574_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; size_t v_sz_620_; size_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
lean_dec(v_nextCmdSnap_x3f_567_);
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
lean_inc_ref(v_initialSnap_560_);
v___x_618_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_initialSnap_560_);
v___x_619_ = l_Lean_Language_SnapshotTree_getAll(v___x_618_);
v_sz_620_ = lean_array_size(v___x_619_);
v___x_621_ = ((size_t)0ULL);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_sz_620_, v___x_621_, v___x_619_);
v___x_623_ = lean_array_get_size(v___x_622_);
v___x_624_ = lean_nat_dec_lt(v___x_572_, v___x_623_);
if (v___x_624_ == 0)
{
lean_dec_ref(v___x_622_);
v___y_574_ = v___x_617_;
goto v___jp_573_;
}
else
{
uint8_t v___x_625_; 
v___x_625_ = lean_nat_dec_le(v___x_623_, v___x_623_);
if (v___x_625_ == 0)
{
if (v___x_624_ == 0)
{
lean_dec_ref(v___x_622_);
v___y_574_ = v___x_617_;
goto v___jp_573_;
}
else
{
size_t v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_usize_of_nat(v___x_623_);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v___x_622_, v___x_621_, v___x_626_, v___x_617_);
lean_dec_ref(v___x_622_);
v___y_574_ = v___x_627_;
goto v___jp_573_;
}
}
else
{
size_t v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_usize_of_nat(v___x_623_);
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v___x_622_, v___x_621_, v___x_628_, v___x_617_);
lean_dec_ref(v___x_622_);
v___y_574_ = v___x_629_;
goto v___jp_573_;
}
}
v___jp_573_:
{
size_t v_sz_575_; lean_object* v_resultSnap_576_; lean_object* v___x_577_; lean_object* v_cmdState_578_; lean_object* v_infoState_579_; lean_object* v_env_580_; lean_object* v_scopes_581_; lean_object* v_usedQuotCtxts_582_; lean_object* v_nextMacroScope_583_; lean_object* v_maxRecDepth_584_; lean_object* v_ngen_585_; lean_object* v_auxDeclNGen_586_; lean_object* v_traceState_587_; lean_object* v_snapshotTasks_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_615_; 
v_sz_575_ = lean_array_size(v_commands_568_);
v_resultSnap_576_ = lean_ctor_get(v_elabSnap_566_, 2);
lean_inc_ref(v_resultSnap_576_);
lean_dec_ref(v_elabSnap_566_);
v___x_577_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_576_);
v_cmdState_578_ = lean_ctor_get(v___x_577_, 1);
lean_inc_ref(v_cmdState_578_);
lean_dec(v___x_577_);
v_infoState_579_ = lean_ctor_get(v_cmdState_578_, 8);
v_env_580_ = lean_ctor_get(v_cmdState_578_, 0);
v_scopes_581_ = lean_ctor_get(v_cmdState_578_, 2);
v_usedQuotCtxts_582_ = lean_ctor_get(v_cmdState_578_, 3);
v_nextMacroScope_583_ = lean_ctor_get(v_cmdState_578_, 4);
v_maxRecDepth_584_ = lean_ctor_get(v_cmdState_578_, 5);
v_ngen_585_ = lean_ctor_get(v_cmdState_578_, 6);
v_auxDeclNGen_586_ = lean_ctor_get(v_cmdState_578_, 7);
v_traceState_587_ = lean_ctor_get(v_cmdState_578_, 9);
v_snapshotTasks_588_ = lean_ctor_get(v_cmdState_578_, 10);
v_isSharedCheck_615_ = !lean_is_exclusive(v_cmdState_578_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_cmdState_578_, 1);
lean_dec(v_unused_616_);
v___x_590_ = v_cmdState_578_;
v_isShared_591_ = v_isSharedCheck_615_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_snapshotTasks_588_);
lean_inc(v_traceState_587_);
lean_inc(v_infoState_579_);
lean_inc(v_auxDeclNGen_586_);
lean_inc(v_ngen_585_);
lean_inc(v_maxRecDepth_584_);
lean_inc(v_nextMacroScope_583_);
lean_inc(v_usedQuotCtxts_582_);
lean_inc(v_scopes_581_);
lean_inc(v_env_580_);
lean_dec(v_cmdState_578_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_615_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
uint8_t v_enabled_592_; lean_object* v_assignment_593_; lean_object* v_lazyAssignment_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_613_; 
v_enabled_592_ = lean_ctor_get_uint8(v_infoState_579_, sizeof(void*)*3);
v_assignment_593_ = lean_ctor_get(v_infoState_579_, 0);
v_lazyAssignment_594_ = lean_ctor_get(v_infoState_579_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_infoState_579_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v_infoState_579_, 2);
lean_dec(v_unused_614_);
v___x_596_ = v_infoState_579_;
v_isShared_597_ = v_isSharedCheck_613_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_lazyAssignment_594_);
lean_inc(v_assignment_593_);
lean_dec(v_infoState_579_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_613_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v_pos_598_; size_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v_trees_603_; lean_object* v___x_605_; 
v_pos_598_ = lean_ctor_get(v_parserState_565_, 0);
lean_inc(v_pos_598_);
v___x_599_ = ((size_t)0ULL);
lean_inc_ref(v_commands_568_);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_575_, v___x_599_, v_commands_568_);
v___x_601_ = lean_array_get_size(v___x_600_);
v___x_602_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v___x_600_, v___x_572_, v___x_601_);
lean_dec_ref(v___x_600_);
v_trees_603_ = l_Array_toPArray_x27___redArg(v___x_602_);
lean_dec_ref(v___x_602_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 2, v_trees_603_);
v___x_605_ = v___x_596_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_assignment_593_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_lazyAssignment_594_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_trees_603_);
lean_ctor_set_uint8(v_reuseFailAlloc_612_, sizeof(void*)*3, v_enabled_592_);
v___x_605_ = v_reuseFailAlloc_612_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 8, v___x_605_);
lean_ctor_set(v___x_590_, 1, v___y_574_);
v___x_607_ = v___x_590_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_env_580_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v___y_574_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_scopes_581_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_usedQuotCtxts_582_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_nextMacroScope_583_);
lean_ctor_set(v_reuseFailAlloc_611_, 5, v_maxRecDepth_584_);
lean_ctor_set(v_reuseFailAlloc_611_, 6, v_ngen_585_);
lean_ctor_set(v_reuseFailAlloc_611_, 7, v_auxDeclNGen_586_);
lean_ctor_set(v_reuseFailAlloc_611_, 8, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_611_, 9, v_traceState_587_);
lean_ctor_set(v_reuseFailAlloc_611_, 10, v_snapshotTasks_588_);
v___x_607_ = v_reuseFailAlloc_611_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_575_, v___x_599_, v_commands_568_);
v___x_609_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v_parserState_565_);
lean_ctor_set(v___x_609_, 2, v_pos_598_);
lean_ctor_set(v___x_609_, 3, v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v_inputCtx_559_);
lean_ctor_set(v___x_610_, 2, v_initialSnap_560_);
return v___x_610_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___boxed(lean_object* v_inputCtx_630_, lean_object* v_initialSnap_631_, lean_object* v_t_632_, lean_object* v_commands_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_630_, v_initialSnap_631_, v_t_632_, v_commands_633_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object* v_inputCtx_638_, lean_object* v_parserState_639_, lean_object* v_commandState_640_, lean_object* v_old_x3f_641_){
_start:
{
lean_object* v___y_644_; 
if (lean_obj_tag(v_old_x3f_641_) == 0)
{
lean_object* v___x_649_; 
v___x_649_ = lean_box(0);
v___y_644_ = v___x_649_;
goto v___jp_643_;
}
else
{
lean_object* v_val_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_660_; 
v_val_650_ = lean_ctor_get(v_old_x3f_641_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_old_x3f_641_);
if (v_isSharedCheck_660_ == 0)
{
v___x_652_ = v_old_x3f_641_;
v_isShared_653_ = v_isSharedCheck_660_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_val_650_);
lean_dec(v_old_x3f_641_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_660_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_inputCtx_654_; lean_object* v_initialSnap_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v_inputCtx_654_ = lean_ctor_get(v_val_650_, 1);
lean_inc_ref(v_inputCtx_654_);
v_initialSnap_655_ = lean_ctor_get(v_val_650_, 2);
lean_inc_ref(v_initialSnap_655_);
lean_dec(v_val_650_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_inputCtx_654_);
lean_ctor_set(v___x_656_, 1, v_initialSnap_655_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_656_);
v___x_658_ = v___x_652_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
v___y_644_ = v___x_658_;
goto v___jp_643_;
}
}
}
v___jp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
lean_inc_ref(v_inputCtx_638_);
v___x_645_ = l_Lean_Language_Lean_processCommands(v_inputCtx_638_, v_parserState_639_, v_commandState_640_, v___y_644_);
lean_inc_ref(v___x_645_);
v___x_646_ = lean_task_get_own(v___x_645_);
v___x_647_ = ((lean_object*)(l_Lean_Elab_IO_processCommandsIncrementally___closed__0));
v___x_648_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_638_, v___x_646_, v___x_645_, v___x_647_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally___boxed(lean_object* v_inputCtx_661_, lean_object* v_parserState_662_, lean_object* v_commandState_663_, lean_object* v_old_x3f_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_661_, v_parserState_662_, v_commandState_663_, v_old_x3f_664_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object* v_inputCtx_667_, lean_object* v_parserState_668_, lean_object* v_commandState_669_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v_toState_673_; lean_object* v___x_674_; 
v___x_671_ = lean_box(0);
v___x_672_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_667_, v_parserState_668_, v_commandState_669_, v___x_671_);
v_toState_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc_ref(v_toState_673_);
lean_dec_ref(v___x_672_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v_toState_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands___boxed(lean_object* v_inputCtx_675_, lean_object* v_parserState_676_, lean_object* v_commandState_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Elab_IO_processCommands(v_inputCtx_675_, v_parserState_676_, v_commandState_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object* v_input_685_, lean_object* v_env_686_, lean_object* v_opts_687_, lean_object* v_fileName_688_){
_start:
{
lean_object* v___y_691_; 
if (lean_obj_tag(v_fileName_688_) == 0)
{
lean_object* v___x_711_; 
v___x_711_ = ((lean_object*)(l_Lean_Elab_process___closed__1));
v___y_691_ = v___x_711_;
goto v___jp_690_;
}
else
{
lean_object* v_val_712_; 
v_val_712_ = lean_ctor_get(v_fileName_688_, 0);
lean_inc(v_val_712_);
lean_dec_ref(v_fileName_688_);
v___y_691_ = v_val_712_;
goto v___jp_690_;
}
v___jp_690_:
{
uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v_inputCtx_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_710_; 
v___x_692_ = 1;
v___x_693_ = lean_string_utf8_byte_size(v_input_685_);
v_inputCtx_694_ = l_Lean_Parser_mkInputContext___redArg(v_input_685_, v___y_691_, v___x_692_, v___x_693_);
v___x_695_ = ((lean_object*)(l_Lean_Elab_process___closed__0));
v___x_696_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
v___x_697_ = l_Lean_Elab_Command_mkState(v_env_686_, v___x_696_, v_opts_687_);
v___x_698_ = l_Lean_Elab_IO_processCommands(v_inputCtx_694_, v___x_695_, v___x_697_);
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_710_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_710_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_710_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_commandState_703_; lean_object* v_env_704_; lean_object* v_messages_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v_commandState_703_ = lean_ctor_get(v_a_699_, 0);
lean_inc_ref(v_commandState_703_);
lean_dec(v_a_699_);
v_env_704_ = lean_ctor_get(v_commandState_703_, 0);
lean_inc_ref(v_env_704_);
v_messages_705_ = lean_ctor_get(v_commandState_703_, 1);
lean_inc_ref(v_messages_705_);
lean_dec_ref(v_commandState_703_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v_env_704_);
lean_ctor_set(v___x_706_, 1, v_messages_705_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_706_);
v___x_708_ = v___x_701_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process___boxed(lean_object* v_input_713_, lean_object* v_env_714_, lean_object* v_opts_715_, lean_object* v_fileName_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Elab_process(v_input_713_, v_env_714_, v_opts_715_, v_fileName_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_opts_719_, lean_object* v_opt_720_){
_start:
{
lean_object* v_name_721_; lean_object* v_map_722_; lean_object* v___x_723_; 
v_name_721_ = lean_ctor_get(v_opt_720_, 0);
v_map_722_ = lean_ctor_get(v_opts_719_, 0);
v___x_723_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_722_, v_name_721_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v___x_724_; 
v___x_724_ = lean_box(0);
return v___x_724_;
}
else
{
lean_object* v_val_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_734_; 
v_val_725_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_734_ == 0)
{
v___x_727_ = v___x_723_;
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_val_725_);
lean_dec(v___x_723_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
if (lean_obj_tag(v_val_725_) == 0)
{
lean_object* v_v_729_; lean_object* v___x_731_; 
v_v_729_ = lean_ctor_get(v_val_725_, 0);
lean_inc_ref(v_v_729_);
lean_dec_ref(v_val_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v_v_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_v_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
else
{
lean_object* v___x_733_; 
lean_del_object(v___x_727_);
lean_dec(v_val_725_);
v___x_733_ = lean_box(0);
return v___x_733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2___boxed(lean_object* v_opts_735_, lean_object* v_opt_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(v_opts_735_, v_opt_736_);
lean_dec_ref(v_opt_736_);
lean_dec_ref(v_opts_735_);
return v_res_737_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(lean_object* v_opts_738_, lean_object* v_opt_739_){
_start:
{
lean_object* v_name_740_; lean_object* v_defValue_741_; lean_object* v_map_742_; lean_object* v___x_743_; 
v_name_740_ = lean_ctor_get(v_opt_739_, 0);
v_defValue_741_ = lean_ctor_get(v_opt_739_, 1);
v_map_742_ = lean_ctor_get(v_opts_738_, 0);
v___x_743_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_742_, v_name_740_);
if (lean_obj_tag(v___x_743_) == 0)
{
uint8_t v___x_744_; 
v___x_744_ = lean_unbox(v_defValue_741_);
return v___x_744_;
}
else
{
lean_object* v_val_745_; 
v_val_745_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_val_745_);
lean_dec_ref(v___x_743_);
if (lean_obj_tag(v_val_745_) == 1)
{
uint8_t v_v_746_; 
v_v_746_ = lean_ctor_get_uint8(v_val_745_, 0);
lean_dec_ref(v_val_745_);
return v_v_746_;
}
else
{
uint8_t v___x_747_; 
lean_dec(v_val_745_);
v___x_747_ = lean_unbox(v_defValue_741_);
return v___x_747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_opts_748_, lean_object* v_opt_749_){
_start:
{
uint8_t v_res_750_; lean_object* v_r_751_; 
v_res_750_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(v_opts_748_, v_opt_749_);
lean_dec_ref(v_opt_749_);
lean_dec_ref(v_opts_748_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v_hOpt_754_){
_start:
{
lean_inc_ref(v_hOpt_754_);
return v_hOpt_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_755_, lean_object* v_x_756_, lean_object* v_hOpt_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Elab_runFrontend___lam__0(v_x_755_, v_x_756_, v_hOpt_757_);
lean_dec_ref(v_hOpt_757_);
lean_dec_ref(v_x_756_);
lean_dec(v_x_755_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_759_, size_t v_i_760_, size_t v_stop_761_, lean_object* v_b_762_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = lean_usize_dec_eq(v_i_760_, v_stop_761_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_array_uget_borrowed(v_as_759_, v_i_760_);
lean_inc(v___x_765_);
v___x_766_ = lean_load_dynlib(v___x_765_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; size_t v___x_768_; size_t v___x_769_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_766_);
v___x_768_ = ((size_t)1ULL);
v___x_769_ = lean_usize_add(v_i_760_, v___x_768_);
v_i_760_ = v___x_769_;
v_b_762_ = v_a_767_;
goto _start;
}
else
{
return v___x_766_;
}
}
else
{
lean_object* v___x_771_; 
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v_b_762_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_772_, lean_object* v_i_773_, lean_object* v_stop_774_, lean_object* v_b_775_, lean_object* v___y_776_){
_start:
{
size_t v_i_boxed_777_; size_t v_stop_boxed_778_; lean_object* v_res_779_; 
v_i_boxed_777_ = lean_unbox_usize(v_i_773_);
lean_dec(v_i_773_);
v_stop_boxed_778_ = lean_unbox_usize(v_stop_774_);
lean_dec(v_stop_774_);
v_res_779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_772_, v_i_boxed_777_, v_stop_boxed_778_, v_b_775_);
lean_dec_ref(v_as_772_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_setup_x3f_780_, lean_object* v___f_781_, lean_object* v___x_782_, lean_object* v_plugins_783_, uint32_t v_trustLevel_784_, uint8_t v___x_785_, lean_object* v_mainModuleName_786_, lean_object* v_stx_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___y_791_; lean_object* v___y_792_; uint8_t v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; 
if (lean_obj_tag(v_setup_x3f_780_) == 1)
{
lean_object* v_val_804_; lean_object* v_name_805_; lean_object* v_package_x3f_806_; uint8_t v_isModule_807_; lean_object* v_imports_x3f_808_; lean_object* v_importArts_809_; lean_object* v_dynlibs_810_; lean_object* v_plugins_811_; lean_object* v_options_812_; lean_object* v___y_819_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
lean_dec(v_mainModuleName_786_);
v_val_804_ = lean_ctor_get(v_setup_x3f_780_, 0);
lean_inc(v_val_804_);
lean_dec_ref(v_setup_x3f_780_);
v_name_805_ = lean_ctor_get(v_val_804_, 0);
lean_inc(v_name_805_);
v_package_x3f_806_ = lean_ctor_get(v_val_804_, 1);
lean_inc(v_package_x3f_806_);
v_isModule_807_ = lean_ctor_get_uint8(v_val_804_, sizeof(void*)*7);
v_imports_x3f_808_ = lean_ctor_get(v_val_804_, 2);
lean_inc(v_imports_x3f_808_);
v_importArts_809_ = lean_ctor_get(v_val_804_, 3);
lean_inc(v_importArts_809_);
v_dynlibs_810_ = lean_ctor_get(v_val_804_, 4);
lean_inc_ref(v_dynlibs_810_);
v_plugins_811_ = lean_ctor_get(v_val_804_, 5);
lean_inc_ref(v_plugins_811_);
v_options_812_ = lean_ctor_get(v_val_804_, 6);
lean_inc(v_options_812_);
lean_dec(v_val_804_);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_array_get_size(v_dynlibs_810_);
v___x_830_ = lean_nat_dec_lt(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_dec_ref(v_dynlibs_810_);
goto v___jp_813_;
}
else
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = lean_box(0);
v___x_832_ = lean_nat_dec_le(v___x_829_, v___x_829_);
if (v___x_832_ == 0)
{
if (v___x_830_ == 0)
{
lean_dec_ref(v_dynlibs_810_);
goto v___jp_813_;
}
else
{
size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; 
v___x_833_ = ((size_t)0ULL);
v___x_834_ = lean_usize_of_nat(v___x_829_);
v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_810_, v___x_833_, v___x_834_, v___x_831_);
lean_dec_ref(v_dynlibs_810_);
v___y_819_ = v___x_835_;
goto v___jp_818_;
}
}
else
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v___x_836_ = ((size_t)0ULL);
v___x_837_ = lean_usize_of_nat(v___x_829_);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_810_, v___x_836_, v___x_837_, v___x_831_);
lean_dec_ref(v_dynlibs_810_);
v___y_819_ = v___x_838_;
goto v___jp_818_;
}
}
v___jp_813_:
{
uint8_t v___x_814_; uint8_t v___x_815_; 
v___x_814_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_787_);
v___x_815_ = lean_strict_or(v_isModule_807_, v___x_814_);
if (lean_obj_tag(v_imports_x3f_808_) == 0)
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_787_, v___x_785_);
v___y_791_ = v_package_x3f_806_;
v___y_792_ = v_options_812_;
v___y_793_ = v___x_815_;
v___y_794_ = v_plugins_811_;
v___y_795_ = v_name_805_;
v___y_796_ = v_importArts_809_;
v___y_797_ = v___x_816_;
goto v___jp_790_;
}
else
{
lean_object* v_val_817_; 
lean_dec(v_stx_787_);
v_val_817_ = lean_ctor_get(v_imports_x3f_808_, 0);
lean_inc(v_val_817_);
lean_dec_ref(v_imports_x3f_808_);
v___y_791_ = v_package_x3f_806_;
v___y_792_ = v_options_812_;
v___y_793_ = v___x_815_;
v___y_794_ = v_plugins_811_;
v___y_795_ = v_name_805_;
v___y_796_ = v_importArts_809_;
v___y_797_ = v_val_817_;
goto v___jp_790_;
}
}
v___jp_818_:
{
if (lean_obj_tag(v___y_819_) == 0)
{
lean_dec_ref(v___y_819_);
goto v___jp_813_;
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_options_812_);
lean_dec_ref(v_plugins_811_);
lean_dec(v_importArts_809_);
lean_dec(v_imports_x3f_808_);
lean_dec(v_package_x3f_806_);
lean_dec(v_name_805_);
lean_dec(v_stx_787_);
lean_dec_ref(v_plugins_783_);
lean_dec_ref(v___x_782_);
lean_dec_ref(v___f_781_);
v_a_820_ = lean_ctor_get(v___y_819_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___y_819_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___y_819_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___y_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
else
{
lean_object* v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec_ref(v___f_781_);
lean_dec(v_setup_x3f_780_);
v___x_839_ = lean_box(0);
v___x_840_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_787_);
v___x_841_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_787_, v___x_785_);
v___x_842_ = lean_box(1);
v___x_843_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_843_, 0, v_mainModuleName_786_);
lean_ctor_set(v___x_843_, 1, v___x_839_);
lean_ctor_set(v___x_843_, 2, v___x_841_);
lean_ctor_set(v___x_843_, 3, v___x_782_);
lean_ctor_set(v___x_843_, 4, v___x_842_);
lean_ctor_set(v___x_843_, 5, v_plugins_783_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*6 + 4, v___x_840_);
lean_ctor_set_uint32(v___x_843_, sizeof(void*)*6, v_trustLevel_784_);
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
v___jp_790_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_798_ = l_Lean_LeanOptions_toOptions(v___y_792_);
v___x_799_ = l_Lean_Options_mergeBy(v___f_781_, v___x_782_, v___x_798_);
v___x_800_ = l_Array_append___redArg(v_plugins_783_, v___y_794_);
lean_dec_ref(v___y_794_);
v___x_801_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_801_, 0, v___y_795_);
lean_ctor_set(v___x_801_, 1, v___y_791_);
lean_ctor_set(v___x_801_, 2, v___y_797_);
lean_ctor_set(v___x_801_, 3, v___x_799_);
lean_ctor_set(v___x_801_, 4, v___y_796_);
lean_ctor_set(v___x_801_, 5, v___x_800_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*6 + 4, v___y_793_);
lean_ctor_set_uint32(v___x_801_, sizeof(void*)*6, v_trustLevel_784_);
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object* v_setup_x3f_846_, lean_object* v___f_847_, lean_object* v___x_848_, lean_object* v_plugins_849_, lean_object* v_trustLevel_850_, lean_object* v___x_851_, lean_object* v_mainModuleName_852_, lean_object* v_stx_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
uint32_t v_trustLevel_boxed_856_; uint8_t v___x_4811__boxed_857_; lean_object* v_res_858_; 
v_trustLevel_boxed_856_ = lean_unbox_uint32(v_trustLevel_850_);
lean_dec(v_trustLevel_850_);
v___x_4811__boxed_857_ = lean_unbox(v___x_851_);
v_res_858_ = l_Lean_Elab_runFrontend___lam__1(v_setup_x3f_846_, v___f_847_, v___x_848_, v_plugins_849_, v_trustLevel_boxed_856_, v___x_4811__boxed_857_, v_mainModuleName_852_, v_stx_853_, v___y_854_);
lean_dec_ref(v___y_854_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_s_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_Elab_runFrontend___lam__2___closed__0));
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_s_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* v___f_865_, lean_object* v_s_866_){
_start:
{
lean_object* v_toSnapshot_867_; lean_object* v_metaSnap_868_; lean_object* v_result_x3f_869_; lean_object* v___y_871_; 
v_toSnapshot_867_ = lean_ctor_get(v_s_866_, 0);
lean_inc_ref(v_toSnapshot_867_);
v_metaSnap_868_ = lean_ctor_get(v_s_866_, 1);
lean_inc_ref(v_metaSnap_868_);
v_result_x3f_869_ = lean_ctor_get(v_s_866_, 2);
lean_inc(v_result_x3f_869_);
lean_dec_ref(v_s_866_);
if (lean_obj_tag(v_result_x3f_869_) == 0)
{
lean_object* v___x_881_; 
v___x_881_ = lean_box(0);
v___y_871_ = v___x_881_;
goto v___jp_870_;
}
else
{
lean_object* v_val_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_895_; 
v_val_882_ = lean_ctor_get(v_result_x3f_869_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v_result_x3f_869_);
if (v_isSharedCheck_895_ == 0)
{
v___x_884_ = v_result_x3f_869_;
v_isShared_885_ = v_isSharedCheck_895_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_val_882_);
lean_dec(v_result_x3f_869_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_895_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_firstCmdSnap_886_; lean_object* v_stx_x3f_887_; lean_object* v_reportingRange_888_; lean_object* v___x_889_; uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v_firstCmdSnap_886_ = lean_ctor_get(v_val_882_, 1);
lean_inc_ref(v_firstCmdSnap_886_);
lean_dec(v_val_882_);
v_stx_x3f_887_ = lean_ctor_get(v_firstCmdSnap_886_, 0);
lean_inc(v_stx_x3f_887_);
v_reportingRange_888_ = lean_ctor_get(v_firstCmdSnap_886_, 1);
lean_inc(v_reportingRange_888_);
v___x_889_ = ((lean_object*)(l_Lean_Elab_runFrontend___lam__4___closed__0));
v___x_890_ = 1;
v___x_891_ = l_Lean_Language_SnapshotTask_map___redArg(v_firstCmdSnap_886_, v___x_889_, v_stx_x3f_887_, v_reportingRange_888_, v___x_890_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_891_);
v___x_893_ = v___x_884_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
v___y_871_ = v___x_893_;
goto v___jp_870_;
}
}
}
v___jp_870_:
{
lean_object* v_stx_x3f_872_; lean_object* v_reportingRange_873_; uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_stx_x3f_872_ = lean_ctor_get(v_metaSnap_868_, 0);
lean_inc(v_stx_x3f_872_);
v_reportingRange_873_ = lean_ctor_get(v_metaSnap_868_, 1);
lean_inc(v_reportingRange_873_);
v___x_874_ = 1;
v___x_875_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_868_, v___f_865_, v_stx_x3f_872_, v_reportingRange_873_, v___x_874_);
v___x_876_ = lean_unsigned_to_nat(1u);
v___x_877_ = lean_mk_empty_array_with_capacity(v___x_876_);
v___x_878_ = lean_array_push(v___x_877_, v___x_875_);
v___x_879_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_871_, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_toSnapshot_867_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_899_, lean_object* v_k_900_, uint8_t v_v_901_){
_start:
{
lean_object* v_map_902_; uint8_t v_hasTrace_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_917_; 
v_map_902_ = lean_ctor_get(v_o_899_, 0);
v_hasTrace_903_ = lean_ctor_get_uint8(v_o_899_, sizeof(void*)*1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_o_899_);
if (v_isSharedCheck_917_ == 0)
{
v___x_905_ = v_o_899_;
v_isShared_906_ = v_isSharedCheck_917_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_map_902_);
lean_dec(v_o_899_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_917_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_907_, 0, v_v_901_);
lean_inc(v_k_900_);
v___x_908_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_900_, v___x_907_, v_map_902_);
if (v_hasTrace_903_ == 0)
{
lean_object* v___x_909_; uint8_t v___x_910_; lean_object* v___x_912_; 
v___x_909_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_910_ = l_Lean_Name_isPrefixOf(v___x_909_, v_k_900_);
lean_dec(v_k_900_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_908_);
v___x_912_ = v___x_905_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_908_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*1, v___x_910_);
return v___x_912_;
}
}
else
{
lean_object* v___x_915_; 
lean_dec(v_k_900_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_908_);
v___x_915_ = v___x_905_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_908_);
lean_ctor_set_uint8(v_reuseFailAlloc_916_, sizeof(void*)*1, v_hasTrace_903_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_918_, lean_object* v_k_919_, lean_object* v_v_920_){
_start:
{
uint8_t v_v_boxed_921_; lean_object* v_res_922_; 
v_v_boxed_921_ = lean_unbox(v_v_920_);
v_res_922_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_918_, v_k_919_, v_v_boxed_921_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_923_, lean_object* v_opt_924_, uint8_t v_val_925_){
_start:
{
lean_object* v_name_926_; lean_object* v___x_927_; 
v_name_926_ = lean_ctor_get(v_opt_924_, 0);
lean_inc(v_name_926_);
lean_dec_ref(v_opt_924_);
v___x_927_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_923_, v_name_926_, v_val_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_928_, lean_object* v_opt_929_, lean_object* v_val_930_){
_start:
{
uint8_t v_val_boxed_931_; lean_object* v_res_932_; 
v_val_boxed_931_ = lean_unbox(v_val_930_);
v_res_932_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_928_, v_opt_929_, v_val_boxed_931_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_933_, lean_object* v_opt_934_, uint8_t v_val_935_){
_start:
{
lean_object* v_name_936_; lean_object* v_map_937_; uint8_t v___x_938_; 
v_name_936_ = lean_ctor_get(v_opt_934_, 0);
v_map_937_ = lean_ctor_get(v_opts_933_, 0);
v___x_938_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_936_, v_map_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_933_, v_opt_934_, v_val_935_);
return v___x_939_;
}
else
{
lean_dec_ref(v_opt_934_);
return v_opts_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_940_, lean_object* v_opt_941_, lean_object* v_val_942_){
_start:
{
uint8_t v_val_boxed_943_; lean_object* v_res_944_; 
v_val_boxed_943_ = lean_unbox(v_val_942_);
v_res_944_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_940_, v_opt_941_, v_val_boxed_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_as_945_, size_t v_i_946_, size_t v_stop_947_, lean_object* v_b_948_){
_start:
{
lean_object* v___y_950_; uint8_t v___x_954_; 
v___x_954_ = lean_usize_dec_eq(v_i_946_, v_stop_947_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v_infoTree_x3f_956_; 
v___x_955_ = lean_array_uget_borrowed(v_as_945_, v_i_946_);
v_infoTree_x3f_956_ = lean_ctor_get(v___x_955_, 2);
if (lean_obj_tag(v_infoTree_x3f_956_) == 1)
{
lean_object* v_val_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_val_957_ = lean_ctor_get(v_infoTree_x3f_956_, 0);
v___x_958_ = lean_unsigned_to_nat(1u);
v___x_959_ = lean_mk_empty_array_with_capacity(v___x_958_);
lean_inc(v_val_957_);
v___x_960_ = lean_array_push(v___x_959_, v_val_957_);
v___x_961_ = l_Array_append___redArg(v_b_948_, v___x_960_);
lean_dec_ref(v___x_960_);
v___y_950_ = v___x_961_;
goto v___jp_949_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_963_ = l_Array_append___redArg(v_b_948_, v___x_962_);
v___y_950_ = v___x_963_;
goto v___jp_949_;
}
}
else
{
return v_b_948_;
}
v___jp_949_:
{
size_t v___x_951_; size_t v___x_952_; 
v___x_951_ = ((size_t)1ULL);
v___x_952_ = lean_usize_add(v_i_946_, v___x_951_);
v_i_946_ = v___x_952_;
v_b_948_ = v___y_950_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_as_964_, lean_object* v_i_965_, lean_object* v_stop_966_, lean_object* v_b_967_){
_start:
{
size_t v_i_boxed_968_; size_t v_stop_boxed_969_; lean_object* v_res_970_; 
v_i_boxed_968_ = lean_unbox_usize(v_i_965_);
lean_dec(v_i_965_);
v_stop_boxed_969_ = lean_unbox_usize(v_stop_966_);
lean_dec(v_stop_966_);
v_res_970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__4(v_as_964_, v_i_boxed_968_, v_stop_boxed_969_, v_b_967_);
lean_dec_ref(v_as_964_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_as_971_, size_t v_i_972_, size_t v_stop_973_, lean_object* v_b_974_){
_start:
{
uint8_t v___x_975_; 
v___x_975_ = lean_usize_dec_eq(v_i_972_, v_stop_973_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; size_t v___x_980_; size_t v___x_981_; 
v___x_976_ = lean_array_uget_borrowed(v_as_971_, v_i_972_);
v___x_977_ = 2;
v___x_978_ = lean_box(v___x_977_);
lean_inc(v___x_976_);
v___x_979_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_976_, v___x_978_, v_b_974_);
v___x_980_ = ((size_t)1ULL);
v___x_981_ = lean_usize_add(v_i_972_, v___x_980_);
v_i_972_ = v___x_981_;
v_b_974_ = v___x_979_;
goto _start;
}
else
{
return v_b_974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_as_983_, lean_object* v_i_984_, lean_object* v_stop_985_, lean_object* v_b_986_){
_start:
{
size_t v_i_boxed_987_; size_t v_stop_boxed_988_; lean_object* v_res_989_; 
v_i_boxed_987_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_stop_boxed_988_ = lean_unbox_usize(v_stop_985_);
lean_dec(v_stop_985_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v_as_983_, v_i_boxed_987_, v_stop_boxed_988_, v_b_986_);
lean_dec_ref(v_as_983_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(size_t v_sz_990_, size_t v_i_991_, lean_object* v_bs_992_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = lean_usize_dec_lt(v_i_991_, v_sz_990_);
if (v___x_993_ == 0)
{
return v_bs_992_;
}
else
{
lean_object* v_v_994_; lean_object* v_traces_995_; lean_object* v___x_996_; lean_object* v_bs_x27_997_; size_t v___x_998_; size_t v___x_999_; lean_object* v___x_1000_; 
v_v_994_ = lean_array_uget_borrowed(v_bs_992_, v_i_991_);
v_traces_995_ = lean_ctor_get(v_v_994_, 3);
lean_inc_ref(v_traces_995_);
v___x_996_ = lean_unsigned_to_nat(0u);
v_bs_x27_997_ = lean_array_uset(v_bs_992_, v_i_991_, v___x_996_);
v___x_998_ = ((size_t)1ULL);
v___x_999_ = lean_usize_add(v_i_991_, v___x_998_);
v___x_1000_ = lean_array_uset(v_bs_x27_997_, v_i_991_, v_traces_995_);
v_i_991_ = v___x_999_;
v_bs_992_ = v___x_1000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object* v_sz_1002_, lean_object* v_i_1003_, lean_object* v_bs_1004_){
_start:
{
size_t v_sz_boxed_1005_; size_t v_i_boxed_1006_; lean_object* v_res_1007_; 
v_sz_boxed_1005_ = lean_unbox_usize(v_sz_1002_);
lean_dec(v_sz_1002_);
v_i_boxed_1006_ = lean_unbox_usize(v_i_1003_);
lean_dec(v_i_1003_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_boxed_1005_, v_i_boxed_1006_, v_bs_1004_);
return v_res_1007_;
}
}
static double _init_l_Lean_Elab_runFrontend___closed__2(void){
_start:
{
lean_object* v___x_1010_; double v___x_1011_; 
v___x_1010_ = lean_unsigned_to_nat(1000000000u);
v___x_1011_ = lean_float_of_nat(v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_1015_, lean_object* v_opts_1016_, lean_object* v_fileName_1017_, lean_object* v_mainModuleName_1018_, uint32_t v_trustLevel_1019_, lean_object* v_oleanFileName_x3f_1020_, lean_object* v_ileanFileName_x3f_1021_, uint8_t v_jsonOutput_1022_, lean_object* v_errorOnKinds_1023_, lean_object* v_plugins_1024_, uint8_t v_printStats_1025_, lean_object* v_setup_x3f_1026_){
_start:
{
lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___x_1034_; lean_object* v___f_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___f_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v_toSnapshot_1048_; lean_object* v_metaSnap_1049_; lean_object* v_stx_1050_; lean_object* v_result_x3f_1051_; lean_object* v___f_1052_; lean_object* v___x_1053_; double v___x_1054_; double v___x_1055_; double v___x_1056_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; uint8_t v___y_1137_; lean_object* v___y_1151_; uint8_t v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1201_; 
v___x_1034_ = lean_io_mono_nanos_now();
v___f_1035_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___x_1036_ = 1;
v___x_1037_ = lean_string_utf8_byte_size(v_input_1015_);
v___x_1038_ = l_Lean_Parser_mkInputContext___redArg(v_input_1015_, v_fileName_1017_, v___x_1036_, v___x_1037_);
v___x_1039_ = l_Lean_internal_cmdlineSnapshots;
v___x_1040_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_1016_, v___x_1039_, v___x_1036_);
v___x_1041_ = l_Lean_Elab_async;
v___x_1042_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_1040_, v___x_1041_, v___x_1036_);
v___x_1043_ = lean_box_uint32(v_trustLevel_1019_);
v___x_1044_ = lean_box(v___x_1036_);
lean_inc(v_mainModuleName_1018_);
lean_inc_ref(v___x_1042_);
v___f_1045_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__1___boxed), 10, 7);
lean_closure_set(v___f_1045_, 0, v_setup_x3f_1026_);
lean_closure_set(v___f_1045_, 1, v___f_1035_);
lean_closure_set(v___f_1045_, 2, v___x_1042_);
lean_closure_set(v___f_1045_, 3, v_plugins_1024_);
lean_closure_set(v___f_1045_, 4, v___x_1043_);
lean_closure_set(v___f_1045_, 5, v___x_1044_);
lean_closure_set(v___f_1045_, 6, v_mainModuleName_1018_);
v___x_1046_ = lean_box(0);
lean_inc_ref(v___x_1038_);
v___x_1047_ = l_Lean_Language_Lean_process(v___f_1045_, v___x_1046_, v___x_1038_);
v_toSnapshot_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc_ref(v_toSnapshot_1048_);
v_metaSnap_1049_ = lean_ctor_get(v___x_1047_, 1);
lean_inc_ref(v_metaSnap_1049_);
v_stx_1050_ = lean_ctor_get(v___x_1047_, 3);
lean_inc(v_stx_1050_);
v_result_x3f_1051_ = lean_ctor_get(v___x_1047_, 4);
lean_inc(v_result_x3f_1051_);
v___f_1052_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__1));
v___x_1053_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1054_ = lean_float_of_nat(v___x_1034_);
v___x_1055_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__2, &l_Lean_Elab_runFrontend___closed__2_once, _init_l_Lean_Elab_runFrontend___closed__2);
v___x_1056_ = lean_float_div(v___x_1054_, v___x_1055_);
if (lean_obj_tag(v_result_x3f_1051_) == 0)
{
v___y_1201_ = v___x_1046_;
goto v___jp_1200_;
}
else
{
lean_object* v_val_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1233_; 
v_val_1221_ = lean_ctor_get(v_result_x3f_1051_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_result_x3f_1051_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1223_ = v_result_x3f_1051_;
v_isShared_1224_ = v_isSharedCheck_1233_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_val_1221_);
lean_dec(v_result_x3f_1051_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1233_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_processedSnap_1225_; lean_object* v_stx_x3f_1226_; lean_object* v_reportingRange_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v_processedSnap_1225_ = lean_ctor_get(v_val_1221_, 1);
lean_inc_ref(v_processedSnap_1225_);
lean_dec(v_val_1221_);
v_stx_x3f_1226_ = lean_ctor_get(v_processedSnap_1225_, 0);
lean_inc(v_stx_x3f_1226_);
v_reportingRange_1227_ = lean_ctor_get(v_processedSnap_1225_, 1);
lean_inc(v_reportingRange_1227_);
v___f_1228_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__4));
v___x_1229_ = l_Lean_Language_SnapshotTask_map___redArg(v_processedSnap_1225_, v___f_1228_, v_stx_x3f_1226_, v_reportingRange_1227_, v___x_1036_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1229_);
v___x_1231_ = v___x_1223_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
v___y_1201_ = v___x_1231_;
goto v___jp_1200_;
}
}
}
v___jp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = lean_runtime_forget(v___y_1030_);
v___x_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___y_1029_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
v___jp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = l_Lean_trace_profiler_output;
v___x_1061_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__2(v___x_1042_, v___x_1060_);
if (lean_obj_tag(v___x_1061_) == 1)
{
lean_object* v_val_1062_; lean_object* v___x_1063_; size_t v_sz_1064_; size_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_val_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_val_1062_);
lean_dec_ref(v___x_1061_);
lean_inc_ref(v___y_1059_);
v___x_1063_ = l_Lean_Language_SnapshotTree_getAll(v___y_1059_);
v_sz_1064_ = lean_array_size(v___x_1063_);
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__3(v_sz_1064_, v___x_1065_, v___x_1063_);
v___x_1067_ = l_Lean_Name_toString(v_mainModuleName_1018_, v___x_1036_);
v___x_1068_ = l_Lean_Firefox_Profile_export(v___x_1067_, v___x_1056_, v___x_1066_, v___x_1042_);
lean_dec_ref(v___x_1042_);
lean_dec_ref(v___x_1066_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_1069_);
v___x_1071_ = l_Lean_Json_compress(v___x_1070_);
v___x_1072_ = l_IO_FS_writeFile(v_val_1062_, v___x_1071_);
lean_dec_ref(v___x_1071_);
lean_dec(v_val_1062_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_dec_ref(v___x_1072_);
v___y_1029_ = v___y_1058_;
v___y_1030_ = v___y_1059_;
goto v___jp_1028_;
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v___y_1059_);
lean_dec_ref(v___y_1058_);
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_val_1062_);
lean_dec_ref(v___y_1059_);
lean_dec_ref(v___y_1058_);
v_a_1081_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1068_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1068_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_dec(v___x_1061_);
lean_dec_ref(v___x_1042_);
lean_dec(v_mainModuleName_1018_);
v___y_1029_ = v___y_1058_;
v___y_1030_ = v___y_1059_;
goto v___jp_1028_;
}
}
v___jp_1089_:
{
lean_object* v_fileMap_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v_fst_1098_; lean_object* v_snd_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_fileMap_1094_ = lean_ctor_get(v___x_1038_, 2);
lean_inc_ref(v_fileMap_1094_);
lean_dec_ref(v___x_1038_);
v___x_1095_ = 0;
v___x_1096_ = l_Lean_Server_findModuleRefs(v_fileMap_1094_, v___y_1093_, v___x_1095_, v___x_1095_);
lean_dec_ref(v___y_1093_);
v___x_1097_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_1096_);
v_fst_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_fst_1098_);
v_snd_1099_ = lean_ctor_get(v___x_1097_, 1);
lean_inc(v_snd_1099_);
lean_dec_ref(v___x_1097_);
v___x_1100_ = lean_unsigned_to_nat(5u);
v___x_1101_ = l_Lean_Server_collectImports(v_stx_1050_);
lean_inc(v_mainModuleName_1018_);
v___x_1102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v_mainModuleName_1018_);
lean_ctor_set(v___x_1102_, 2, v___x_1101_);
lean_ctor_set(v___x_1102_, 3, v_fst_1098_);
lean_ctor_set(v___x_1102_, 4, v_snd_1099_);
v___x_1103_ = l_Lean_Server_instToJsonIlean_toJson(v___x_1102_);
v___x_1104_ = l_Lean_Json_compress(v___x_1103_);
v___x_1105_ = l_IO_FS_writeFile(v___y_1090_, v___x_1104_);
lean_dec_ref(v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_dec_ref(v___x_1105_);
v___y_1058_ = v___y_1092_;
v___y_1059_ = v___y_1091_;
goto v___jp_1057_;
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec_ref(v___x_1042_);
lean_dec(v_mainModuleName_1018_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
v___jp_1114_:
{
if (lean_obj_tag(v_ileanFileName_x3f_1021_) == 1)
{
lean_object* v_val_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v_val_1118_ = lean_ctor_get(v_ileanFileName_x3f_1021_, 0);
lean_inc_ref(v___y_1117_);
v___x_1119_ = l_Lean_Language_SnapshotTree_getAll(v___y_1117_);
v___x_1120_ = lean_mk_empty_array_with_capacity(v___y_1115_);
v___x_1121_ = lean_array_get_size(v___x_1119_);
v___x_1122_ = lean_nat_dec_lt(v___y_1115_, v___x_1121_);
lean_dec(v___y_1115_);
if (v___x_1122_ == 0)
{
lean_dec_ref(v___x_1119_);
v___y_1090_ = v_val_1118_;
v___y_1091_ = v___y_1117_;
v___y_1092_ = v___y_1116_;
v___y_1093_ = v___x_1120_;
goto v___jp_1089_;
}
else
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_nat_dec_le(v___x_1121_, v___x_1121_);
if (v___x_1123_ == 0)
{
if (v___x_1122_ == 0)
{
lean_dec_ref(v___x_1119_);
v___y_1090_ = v_val_1118_;
v___y_1091_ = v___y_1117_;
v___y_1092_ = v___y_1116_;
v___y_1093_ = v___x_1120_;
goto v___jp_1089_;
}
else
{
size_t v___x_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = ((size_t)0ULL);
v___x_1125_ = lean_usize_of_nat(v___x_1121_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__4(v___x_1119_, v___x_1124_, v___x_1125_, v___x_1120_);
lean_dec_ref(v___x_1119_);
v___y_1090_ = v_val_1118_;
v___y_1091_ = v___y_1117_;
v___y_1092_ = v___y_1116_;
v___y_1093_ = v___x_1126_;
goto v___jp_1089_;
}
}
else
{
size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = ((size_t)0ULL);
v___x_1128_ = lean_usize_of_nat(v___x_1121_);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__4(v___x_1119_, v___x_1127_, v___x_1128_, v___x_1120_);
lean_dec_ref(v___x_1119_);
v___y_1090_ = v_val_1118_;
v___y_1091_ = v___y_1117_;
v___y_1092_ = v___y_1116_;
v___y_1093_ = v___x_1129_;
goto v___jp_1089_;
}
}
}
else
{
lean_dec(v___y_1115_);
lean_dec(v_stx_1050_);
lean_dec_ref(v___x_1038_);
v___y_1058_ = v___y_1116_;
v___y_1059_ = v___y_1117_;
goto v___jp_1057_;
}
}
v___jp_1130_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1138_ = lean_box(v___y_1137_);
lean_inc_ref(v___y_1134_);
v___x_1139_ = lean_alloc_closure((void*)(l_Lean_writeModule___boxed), 4, 3);
lean_closure_set(v___x_1139_, 0, v___y_1134_);
lean_closure_set(v___x_1139_, 1, v___y_1132_);
lean_closure_set(v___x_1139_, 2, v___x_1138_);
v___x_1140_ = lean_box(0);
v___x_1141_ = l_Lean_profileitIOUnsafe___redArg(v___y_1136_, v___y_1135_, v___x_1139_, v___x_1140_);
lean_dec_ref(v___y_1135_);
lean_dec_ref(v___y_1136_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_dec_ref(v___x_1141_);
v___y_1115_ = v___y_1131_;
v___y_1116_ = v___y_1134_;
v___y_1117_ = v___y_1133_;
goto v___jp_1114_;
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1131_);
lean_dec(v_stx_1050_);
lean_dec_ref(v___x_1042_);
lean_dec_ref(v___x_1038_);
lean_dec(v_mainModuleName_1018_);
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
v___jp_1150_:
{
if (v___y_1152_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_1020_) == 1)
{
lean_object* v_val_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v_val_1156_ = lean_ctor_get(v_oleanFileName_x3f_1020_, 0);
lean_inc(v_val_1156_);
lean_dec_ref(v_oleanFileName_x3f_1020_);
v___x_1157_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__3));
v___x_1158_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1159_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__5(v___y_1155_, v___x_1158_);
if (v___x_1159_ == 0)
{
v___y_1131_ = v___y_1151_;
v___y_1132_ = v_val_1156_;
v___y_1133_ = v___y_1154_;
v___y_1134_ = v___y_1153_;
v___y_1135_ = v___y_1155_;
v___y_1136_ = v___x_1157_;
v___y_1137_ = v___x_1036_;
goto v___jp_1130_;
}
else
{
v___y_1131_ = v___y_1151_;
v___y_1132_ = v_val_1156_;
v___y_1133_ = v___y_1154_;
v___y_1134_ = v___y_1153_;
v___y_1135_ = v___y_1155_;
v___y_1136_ = v___x_1157_;
v___y_1137_ = v___y_1152_;
goto v___jp_1130_;
}
}
else
{
lean_dec_ref(v___y_1155_);
lean_dec(v_oleanFileName_x3f_1020_);
v___y_1115_ = v___y_1151_;
v___y_1116_ = v___y_1153_;
v___y_1117_ = v___y_1154_;
goto v___jp_1114_;
}
}
else
{
lean_object* v___x_1160_; 
lean_dec_ref(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1151_);
lean_dec(v_stx_1050_);
lean_dec_ref(v___x_1042_);
lean_dec_ref(v___x_1038_);
lean_dec(v_oleanFileName_x3f_1020_);
lean_dec(v_mainModuleName_1018_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1046_);
return v___x_1160_;
}
}
v___jp_1161_:
{
lean_object* v___x_1165_; 
lean_inc_ref(v___y_1163_);
v___x_1165_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_1163_, v___x_1042_, v_jsonOutput_1022_, v___y_1164_);
lean_dec(v___y_1164_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1191_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1191_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1191_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___x_1047_);
if (lean_obj_tag(v___x_1170_) == 1)
{
lean_object* v_val_1171_; lean_object* v_env_1172_; lean_object* v_scopes_1173_; lean_object* v___x_1174_; 
lean_del_object(v___x_1168_);
v_val_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_val_1171_);
lean_dec_ref(v___x_1170_);
v_env_1172_ = lean_ctor_get(v_val_1171_, 0);
lean_inc_ref(v_env_1172_);
v_scopes_1173_ = lean_ctor_get(v_val_1171_, 2);
lean_inc(v_scopes_1173_);
lean_dec(v_val_1171_);
lean_inc(v___y_1162_);
v___x_1174_ = l_List_get_x21Internal___redArg(v___x_1053_, v_scopes_1173_, v___y_1162_);
lean_dec(v_scopes_1173_);
if (v_printStats_1025_ == 0)
{
lean_object* v_opts_1175_; uint8_t v___x_1176_; 
v_opts_1175_ = lean_ctor_get(v___x_1174_, 1);
lean_inc_ref(v_opts_1175_);
lean_dec(v___x_1174_);
v___x_1176_ = lean_unbox(v_a_1166_);
lean_dec(v_a_1166_);
v___y_1151_ = v___y_1162_;
v___y_1152_ = v___x_1176_;
v___y_1153_ = v_env_1172_;
v___y_1154_ = v___y_1163_;
v___y_1155_ = v_opts_1175_;
goto v___jp_1150_;
}
else
{
lean_object* v_opts_1177_; lean_object* v___x_1178_; 
v_opts_1177_ = lean_ctor_get(v___x_1174_, 1);
lean_inc_ref(v_opts_1177_);
lean_dec(v___x_1174_);
lean_inc_ref(v_env_1172_);
v___x_1178_ = l_Lean_Environment_displayStats(v_env_1172_);
if (lean_obj_tag(v___x_1178_) == 0)
{
uint8_t v___x_1179_; 
lean_dec_ref(v___x_1178_);
v___x_1179_ = lean_unbox(v_a_1166_);
lean_dec(v_a_1166_);
v___y_1151_ = v___y_1162_;
v___y_1152_ = v___x_1179_;
v___y_1153_ = v_env_1172_;
v___y_1154_ = v___y_1163_;
v___y_1155_ = v_opts_1177_;
goto v___jp_1150_;
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v_opts_1177_);
lean_dec_ref(v_env_1172_);
lean_dec(v_a_1166_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec(v_stx_1050_);
lean_dec_ref(v___x_1042_);
lean_dec_ref(v___x_1038_);
lean_dec(v_oleanFileName_x3f_1020_);
lean_dec(v_mainModuleName_1018_);
v_a_1180_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1178_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1178_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
else
{
lean_object* v___x_1189_; 
lean_dec(v___x_1170_);
lean_dec(v_a_1166_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec(v_stx_1050_);
lean_dec_ref(v___x_1042_);
lean_dec_ref(v___x_1038_);
lean_dec(v_oleanFileName_x3f_1020_);
lean_dec(v_mainModuleName_1018_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1046_);
v___x_1189_ = v___x_1168_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1046_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec(v_stx_1050_);
lean_dec_ref(v___x_1047_);
lean_dec_ref(v___x_1042_);
lean_dec_ref(v___x_1038_);
lean_dec(v_oleanFileName_x3f_1020_);
lean_dec(v_mainModuleName_1018_);
v_a_1192_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1165_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1165_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
v___jp_1200_:
{
lean_object* v_stx_x3f_1202_; lean_object* v_reportingRange_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v_stx_x3f_1202_ = lean_ctor_get(v_metaSnap_1049_, 0);
lean_inc(v_stx_x3f_1202_);
v_reportingRange_1203_ = lean_ctor_get(v_metaSnap_1049_, 1);
lean_inc(v_reportingRange_1203_);
v___x_1204_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_1049_, v___f_1052_, v_stx_x3f_1202_, v_reportingRange_1203_, v___x_1036_);
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = lean_mk_empty_array_with_capacity(v___x_1205_);
v___x_1207_ = lean_array_push(v___x_1206_, v___x_1204_);
v___x_1208_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_1201_, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v_toSnapshot_1048_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_box(1);
v___x_1211_ = lean_unsigned_to_nat(0u);
v___x_1212_ = lean_array_get_size(v_errorOnKinds_1023_);
v___x_1213_ = lean_nat_dec_lt(v___x_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
v___y_1162_ = v___x_1211_;
v___y_1163_ = v___x_1209_;
v___y_1164_ = v___x_1210_;
goto v___jp_1161_;
}
else
{
uint8_t v___x_1214_; 
v___x_1214_ = lean_nat_dec_le(v___x_1212_, v___x_1212_);
if (v___x_1214_ == 0)
{
if (v___x_1213_ == 0)
{
v___y_1162_ = v___x_1211_;
v___y_1163_ = v___x_1209_;
v___y_1164_ = v___x_1210_;
goto v___jp_1161_;
}
else
{
size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = ((size_t)0ULL);
v___x_1216_ = lean_usize_of_nat(v___x_1212_);
v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v_errorOnKinds_1023_, v___x_1215_, v___x_1216_, v___x_1210_);
v___y_1162_ = v___x_1211_;
v___y_1163_ = v___x_1209_;
v___y_1164_ = v___x_1217_;
goto v___jp_1161_;
}
}
else
{
size_t v___x_1218_; size_t v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = ((size_t)0ULL);
v___x_1219_ = lean_usize_of_nat(v___x_1212_);
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__6(v_errorOnKinds_1023_, v___x_1218_, v___x_1219_, v___x_1210_);
v___y_1162_ = v___x_1211_;
v___y_1163_ = v___x_1209_;
v___y_1164_ = v___x_1220_;
goto v___jp_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_1234_, lean_object* v_opts_1235_, lean_object* v_fileName_1236_, lean_object* v_mainModuleName_1237_, lean_object* v_trustLevel_1238_, lean_object* v_oleanFileName_x3f_1239_, lean_object* v_ileanFileName_x3f_1240_, lean_object* v_jsonOutput_1241_, lean_object* v_errorOnKinds_1242_, lean_object* v_plugins_1243_, lean_object* v_printStats_1244_, lean_object* v_setup_x3f_1245_, lean_object* v_a_1246_){
_start:
{
uint32_t v_trustLevel_boxed_1247_; uint8_t v_jsonOutput_boxed_1248_; uint8_t v_printStats_boxed_1249_; lean_object* v_res_1250_; 
v_trustLevel_boxed_1247_ = lean_unbox_uint32(v_trustLevel_1238_);
lean_dec(v_trustLevel_1238_);
v_jsonOutput_boxed_1248_ = lean_unbox(v_jsonOutput_1241_);
v_printStats_boxed_1249_ = lean_unbox(v_printStats_1244_);
v_res_1250_ = l_Lean_Elab_runFrontend(v_input_1234_, v_opts_1235_, v_fileName_1236_, v_mainModuleName_1237_, v_trustLevel_boxed_1247_, v_oleanFileName_x3f_1239_, v_ileanFileName_x3f_1240_, v_jsonOutput_boxed_1248_, v_errorOnKinds_1242_, v_plugins_1243_, v_printStats_boxed_1249_, v_setup_x3f_1245_);
lean_dec_ref(v_errorOnKinds_1242_);
lean_dec(v_ileanFileName_x3f_1240_);
return v_res_1250_;
}
}
lean_object* runtime_initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_References(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Profiler(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
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
