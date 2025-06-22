// Lean compiler output
// Module: Lean.Elab.Frontend
// Imports: Lean.Language.Lean Lean.Util.Profile Lean.Server.References Lean.Util.Profiler
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
lean_object* l_Lean_Language_Lean_process(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Firefox_Profile_export(lean_object*, double, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_toJsonProfile____x40_Lean_Util_Profiler___hyg_4963_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
double lean_float_div(double, double);
static lean_object* l_Lean_Elab_process___closed__1;
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___closed__5;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___redArg(lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___at___Lean_KVMap_mergeBy_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___lam__3___closed__0;
static lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2___closed__0;
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Array_toPArray_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_findModuleRefs(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
static lean_object* l_Lean_Elab_runFrontend___lam__5___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Frontend_processCommand___closed__0;
lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_processCommands(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Server_collectImports(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_runFrontend_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_IO_processCommandsIncrementally___closed__0;
lean_object* l_Lean_Environment_displayStats(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_process___closed__0;
static lean_object* l_Lean_Elab_runFrontend___closed__4;
lean_object* lean_io_mono_nanos_now(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___lam__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object*);
uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Command_runLintersAsync_spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_runtime_forget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_References_0__Lean_Server_toJsonIlean____x40_Lean_Server_References___hyg_1585_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_runLintersAsync_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg___boxed(lean_object*, lean_object*, lean_object*);
static double l_Lean_Elab_runFrontend___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_writeModule(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_load_dynlib(lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_runFrontend___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_runFrontend_spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_setIfNotSet___at___Lean_Language_Lean_process_processHeader_spec__1(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_internal_cmdlineSnapshots;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_1);
x_9 = lean_st_ref_set(x_2, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
x_20 = lean_st_ref_set(x_2, x_19, x_6);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
x_23 = lean_box(0);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Frontend_setCommandState___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_setCommandState___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Frontend_setCommandState(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected internal error: ", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_st_mk_ref(x_8, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
x_22 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_9);
lean_ctor_set(x_22, 4, x_16);
lean_ctor_set(x_22, 5, x_17);
lean_ctor_set(x_22, 6, x_18);
lean_ctor_set(x_22, 7, x_19);
lean_ctor_set(x_22, 8, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*9, x_23);
lean_inc(x_11);
x_24 = lean_apply_3(x_1, x_22, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_11, x_26);
lean_dec(x_11);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Frontend_setCommandState___redArg(x_28, x_3, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_25);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_11);
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_dec(x_24);
x_37 = l_Lean_Exception_toMessageData(x_35);
x_38 = l_Lean_MessageData_toString(x_37, x_36);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
x_47 = lean_string_append(x_46, x_44);
lean_dec(x_44);
x_48 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_st_mk_ref(x_9, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_box(0);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
x_23 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_10);
lean_ctor_set(x_23, 4, x_17);
lean_ctor_set(x_23, 5, x_18);
lean_ctor_set(x_23, 6, x_19);
lean_ctor_set(x_23, 7, x_20);
lean_ctor_set(x_23, 8, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*9, x_24);
lean_inc(x_12);
x_25 = lean_apply_3(x_2, x_23, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_12, x_27);
lean_dec(x_12);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Frontend_setCommandState___redArg(x_29, x_4, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_26);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_12);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = l_Lean_Exception_toMessageData(x_36);
x_39 = l_Lean_MessageData_toString(x_38, x_37);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
x_48 = lean_string_append(x_47, x_45);
lean_dec(x_45);
x_49 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Frontend_runCommandElabM___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Frontend_runCommandElabM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__0;
x_4 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__2;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_st_mk_ref(x_8, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_24 = lean_st_ref_take(x_11, x_12);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3;
lean_ctor_set(x_25, 1, x_30);
x_31 = lean_st_ref_set(x_11, x_25, x_26);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_box(0);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_box(0);
x_40 = lean_box(0);
lean_inc(x_34);
lean_inc(x_33);
x_41 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 2, x_29);
lean_ctor_set(x_41, 3, x_9);
lean_ctor_set(x_41, 4, x_35);
lean_ctor_set(x_41, 5, x_36);
lean_ctor_set(x_41, 6, x_37);
lean_ctor_set(x_41, 7, x_38);
lean_ctor_set(x_41, 8, x_39);
x_42 = lean_unbox(x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*9, x_42);
lean_inc(x_11);
x_43 = l_Lean_Elab_Command_elabCommandTopLevel(x_1, x_41, x_11, x_32);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_get(x_11, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_st_ref_take(x_11, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_49, 1);
lean_dec(x_53);
x_54 = l_Lean_MessageLog_append(x_28, x_51);
lean_ctor_set(x_49, 1, x_54);
x_55 = lean_st_ref_set(x_11, x_49, x_50);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_13 = x_57;
x_14 = x_56;
goto block_23;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_58 = lean_ctor_get(x_49, 0);
x_59 = lean_ctor_get(x_49, 2);
x_60 = lean_ctor_get(x_49, 3);
x_61 = lean_ctor_get(x_49, 4);
x_62 = lean_ctor_get(x_49, 5);
x_63 = lean_ctor_get(x_49, 6);
x_64 = lean_ctor_get(x_49, 7);
x_65 = lean_ctor_get(x_49, 8);
x_66 = lean_ctor_get(x_49, 9);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_67 = l_Lean_MessageLog_append(x_28, x_51);
x_68 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_59);
lean_ctor_set(x_68, 3, x_60);
lean_ctor_set(x_68, 4, x_61);
lean_ctor_set(x_68, 5, x_62);
lean_ctor_set(x_68, 6, x_63);
lean_ctor_set(x_68, 7, x_64);
lean_ctor_set(x_68, 8, x_65);
lean_ctor_set(x_68, 9, x_66);
x_69 = lean_st_ref_set(x_11, x_68, x_50);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_box(0);
x_13 = x_71;
x_14 = x_70;
goto block_23;
}
}
else
{
lean_dec(x_28);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_43, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_43, 1);
lean_inc(x_73);
lean_dec(x_43);
x_13 = x_72;
x_14 = x_73;
goto block_23;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_11);
x_74 = lean_ctor_get(x_43, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_43, 1);
lean_inc(x_75);
lean_dec(x_43);
x_76 = l_Lean_Exception_toMessageData(x_74);
x_77 = l_Lean_MessageData_toString(x_76, x_75);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
x_81 = lean_string_append(x_80, x_79);
lean_dec(x_79);
x_82 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set_tag(x_77, 1);
lean_ctor_set(x_77, 0, x_82);
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_77, 0);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_77);
x_85 = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
x_86 = lean_string_append(x_85, x_83);
lean_dec(x_83);
x_87 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_89 = lean_ctor_get(x_25, 0);
x_90 = lean_ctor_get(x_25, 1);
x_91 = lean_ctor_get(x_25, 2);
x_92 = lean_ctor_get(x_25, 3);
x_93 = lean_ctor_get(x_25, 4);
x_94 = lean_ctor_get(x_25, 5);
x_95 = lean_ctor_get(x_25, 6);
x_96 = lean_ctor_get(x_25, 7);
x_97 = lean_ctor_get(x_25, 8);
x_98 = lean_ctor_get(x_25, 9);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_25);
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3;
x_101 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_101, 0, x_89);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_101, 2, x_91);
lean_ctor_set(x_101, 3, x_92);
lean_ctor_set(x_101, 4, x_93);
lean_ctor_set(x_101, 5, x_94);
lean_ctor_set(x_101, 6, x_95);
lean_ctor_set(x_101, 7, x_96);
lean_ctor_set(x_101, 8, x_97);
lean_ctor_set(x_101, 9, x_98);
x_102 = lean_st_ref_set(x_11, x_101, x_26);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_ctor_get(x_2, 1);
x_105 = lean_ctor_get(x_2, 2);
x_106 = lean_box(0);
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_box(0);
x_109 = lean_box(0);
x_110 = lean_box(0);
x_111 = lean_box(0);
lean_inc(x_105);
lean_inc(x_104);
x_112 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_112, 0, x_104);
lean_ctor_set(x_112, 1, x_105);
lean_ctor_set(x_112, 2, x_99);
lean_ctor_set(x_112, 3, x_9);
lean_ctor_set(x_112, 4, x_106);
lean_ctor_set(x_112, 5, x_107);
lean_ctor_set(x_112, 6, x_108);
lean_ctor_set(x_112, 7, x_109);
lean_ctor_set(x_112, 8, x_110);
x_113 = lean_unbox(x_111);
lean_ctor_set_uint8(x_112, sizeof(void*)*9, x_113);
lean_inc(x_11);
x_114 = l_Lean_Elab_Command_elabCommandTopLevel(x_1, x_112, x_11, x_103);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_st_ref_get(x_11, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_st_ref_take(x_11, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
lean_dec(x_117);
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 3);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 4);
lean_inc(x_126);
x_127 = lean_ctor_get(x_120, 5);
lean_inc(x_127);
x_128 = lean_ctor_get(x_120, 6);
lean_inc(x_128);
x_129 = lean_ctor_get(x_120, 7);
lean_inc(x_129);
x_130 = lean_ctor_get(x_120, 8);
lean_inc(x_130);
x_131 = lean_ctor_get(x_120, 9);
lean_inc(x_131);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 lean_ctor_release(x_120, 5);
 lean_ctor_release(x_120, 6);
 lean_ctor_release(x_120, 7);
 lean_ctor_release(x_120, 8);
 lean_ctor_release(x_120, 9);
 x_132 = x_120;
} else {
 lean_dec_ref(x_120);
 x_132 = lean_box(0);
}
x_133 = l_Lean_MessageLog_append(x_90, x_122);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 10, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_123);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_124);
lean_ctor_set(x_134, 3, x_125);
lean_ctor_set(x_134, 4, x_126);
lean_ctor_set(x_134, 5, x_127);
lean_ctor_set(x_134, 6, x_128);
lean_ctor_set(x_134, 7, x_129);
lean_ctor_set(x_134, 8, x_130);
lean_ctor_set(x_134, 9, x_131);
x_135 = lean_st_ref_set(x_11, x_134, x_121);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_box(0);
x_13 = x_137;
x_14 = x_136;
goto block_23;
}
else
{
lean_dec(x_90);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_114, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_114, 1);
lean_inc(x_139);
lean_dec(x_114);
x_13 = x_138;
x_14 = x_139;
goto block_23;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_11);
x_140 = lean_ctor_get(x_114, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_114, 1);
lean_inc(x_141);
lean_dec(x_114);
x_142 = l_Lean_Exception_toMessageData(x_140);
x_143 = l_Lean_MessageData_toString(x_142, x_141);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
x_147 = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
x_148 = lean_string_append(x_147, x_144);
lean_dec(x_144);
x_149 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_149, 0, x_148);
if (lean_is_scalar(x_146)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_146;
 lean_ctor_set_tag(x_150, 1);
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_145);
return x_150;
}
}
}
block_23:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_st_ref_get(x_11, x_14);
lean_dec(x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Frontend_setCommandState___redArg(x_16, x_3, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Frontend_elabCommandAtFrontend(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_4, 2);
lean_dec(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_ctor_set(x_4, 2, x_10);
x_11 = lean_st_ref_set(x_1, x_4, x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_5);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_st_ref_set(x_1, x_21, x_6);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_updateCmdPos___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Frontend_updateCmdPos___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_updateCmdPos(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_getParserState___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Frontend_getParserState___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_getParserState(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_getCommandState___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Frontend_getCommandState___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_getCommandState(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_dec(x_8);
lean_ctor_set(x_5, 1, x_1);
x_9 = lean_st_ref_set(x_2, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
x_20 = lean_st_ref_set(x_2, x_19, x_6);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
x_23 = lean_box(0);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Frontend_setParserState___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_setParserState___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Frontend_setParserState(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_dec(x_11);
lean_ctor_set(x_6, 1, x_1);
x_12 = lean_st_ref_set(x_2, x_5, x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
x_26 = lean_ctor_get(x_6, 8);
x_27 = lean_ctor_get(x_6, 9);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_28 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_1);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_21);
lean_ctor_set(x_28, 4, x_22);
lean_ctor_set(x_28, 5, x_23);
lean_ctor_set(x_28, 6, x_24);
lean_ctor_set(x_28, 7, x_25);
lean_ctor_set(x_28, 8, x_26);
lean_ctor_set(x_28, 9, x_27);
lean_ctor_set(x_5, 0, x_28);
x_29 = lean_st_ref_set(x_2, x_5, x_7);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_34 = lean_ctor_get(x_5, 1);
x_35 = lean_ctor_get(x_5, 2);
x_36 = lean_ctor_get(x_5, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
x_37 = lean_ctor_get(x_6, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_6, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_6, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_6, 5);
lean_inc(x_41);
x_42 = lean_ctor_get(x_6, 6);
lean_inc(x_42);
x_43 = lean_ctor_get(x_6, 7);
lean_inc(x_43);
x_44 = lean_ctor_get(x_6, 8);
lean_inc(x_44);
x_45 = lean_ctor_get(x_6, 9);
lean_inc(x_45);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 lean_ctor_release(x_6, 8);
 lean_ctor_release(x_6, 9);
 x_46 = x_6;
} else {
 lean_dec_ref(x_6);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 10, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_1);
lean_ctor_set(x_47, 2, x_38);
lean_ctor_set(x_47, 3, x_39);
lean_ctor_set(x_47, 4, x_40);
lean_ctor_set(x_47, 5, x_41);
lean_ctor_set(x_47, 6, x_42);
lean_ctor_set(x_47, 7, x_43);
lean_ctor_set(x_47, 8, x_44);
lean_ctor_set(x_47, 9, x_45);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_34);
lean_ctor_set(x_48, 2, x_35);
lean_ctor_set(x_48, 3, x_36);
x_49 = lean_st_ref_set(x_2, x_48, x_7);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Frontend_setMessages___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_setMessages___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Frontend_setMessages(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_getInputContext(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_parseCommand(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_processCommand___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("parsing", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_4 = l_Lean_Elab_Frontend_updateCmdPos___redArg(x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_Frontend_getCommandState___redArg(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Frontend_getParserState___redArg(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Lean_Elab_Command_instInhabitedScope;
x_16 = l_List_head_x21___redArg(x_15, x_14);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 3);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_17);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommand___lam__0___boxed), 5, 4);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_10);
lean_closure_set(x_21, 3, x_13);
x_22 = l_Lean_Elab_Frontend_processCommand___closed__0;
x_23 = lean_box(0);
x_24 = lean_profileit(x_22, x_17, x_21, x_23);
lean_dec(x_17);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_st_ref_take(x_2, x_11);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_30, 3);
lean_inc(x_26);
x_34 = lean_array_push(x_33, x_26);
lean_ctor_set(x_30, 3, x_34);
x_35 = lean_st_ref_set(x_2, x_30, x_31);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Elab_Frontend_setParserState___redArg(x_27, x_2, x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Elab_Frontend_setMessages___redArg(x_28, x_2, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_26);
x_41 = l_Lean_Elab_Frontend_elabCommandAtFrontend(x_26, x_1, x_2, x_40);
lean_dec(x_1);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = l_Lean_Parser_isTerminalCommand(x_26);
x_45 = lean_box(x_44);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l_Lean_Parser_isTerminalCommand(x_26);
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_26);
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_41, 0);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_41);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_ctor_get(x_30, 0);
x_55 = lean_ctor_get(x_30, 1);
x_56 = lean_ctor_get(x_30, 2);
x_57 = lean_ctor_get(x_30, 3);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_30);
lean_inc(x_26);
x_58 = lean_array_push(x_57, x_26);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_56);
lean_ctor_set(x_59, 3, x_58);
x_60 = lean_st_ref_set(x_2, x_59, x_31);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_Elab_Frontend_setParserState___redArg(x_27, x_2, x_61);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_Elab_Frontend_setMessages___redArg(x_28, x_2, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
lean_inc(x_26);
x_66 = l_Lean_Elab_Frontend_elabCommandAtFrontend(x_26, x_1, x_2, x_65);
lean_dec(x_1);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = l_Lean_Parser_isTerminalCommand(x_26);
x_70 = lean_box(x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_26);
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_74 = x_66;
} else {
 lean_dec_ref(x_66);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Frontend_processCommand___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_processCommand(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_Elab_Frontend_processCommand(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Frontend_processCommands(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Language_SnapshotTask_get___redArg(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_11, x_2, x_9);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_push(x_4, x_12);
x_5 = x_13;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
static lean_object* _init_l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0;
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
return x_4;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_usize_of_nat(x_2);
x_9 = lean_usize_of_nat(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_task_get_own(x_3);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 4);
lean_inc(x_9);
x_10 = lean_array_push(x_4, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_101; lean_object* x_102; lean_object* x_103; size_t x_104; size_t x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_11 = lean_unsigned_to_nat(0u);
x_101 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3;
lean_inc(x_2);
x_102 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(x_2);
x_103 = l_Lean_Language_SnapshotTree_getAll(x_102);
x_104 = lean_array_size(x_103);
x_105 = 0;
x_106 = l_Array_mapMUnsafe_map___at___Lean_Elab_Command_runLintersAsync_spec__2(x_104, x_105, x_103);
x_107 = lean_array_get_size(x_106);
x_108 = lean_nat_dec_lt(x_11, x_107);
if (x_108 == 0)
{
lean_dec(x_107);
lean_dec(x_106);
x_12 = x_101;
goto block_100;
}
else
{
uint8_t x_109; 
x_109 = lean_nat_dec_le(x_107, x_107);
if (x_109 == 0)
{
lean_dec(x_107);
lean_dec(x_106);
x_12 = x_101;
goto block_100;
}
else
{
size_t x_110; lean_object* x_111; 
x_110 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_111 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Command_runLintersAsync_spec__3(x_106, x_105, x_110, x_101);
lean_dec(x_106);
x_12 = x_111;
goto block_100;
}
}
block_100:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_Language_SnapshotTask_get___redArg(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 7);
x_20 = lean_ctor_get(x_16, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_19, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
x_24 = lean_array_size(x_10);
x_25 = 0;
lean_inc(x_10);
x_26 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0(x_24, x_25, x_10);
x_27 = lean_array_get_size(x_26);
x_28 = l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1(x_26, x_11, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_29 = l_Array_toPArray_x27___redArg(x_28);
lean_dec(x_28);
lean_ctor_set(x_19, 2, x_29);
lean_ctor_set(x_16, 1, x_12);
x_30 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__3(x_24, x_25, x_10);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_7);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_1);
lean_ctor_set(x_32, 2, x_2);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_32);
return x_14;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
x_37 = lean_array_size(x_10);
x_38 = 0;
lean_inc(x_10);
x_39 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0(x_37, x_38, x_10);
x_40 = lean_array_get_size(x_39);
x_41 = l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1(x_39, x_11, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_42 = l_Array_toPArray_x27___redArg(x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_33);
lean_ctor_set(x_16, 7, x_43);
lean_ctor_set(x_16, 1, x_12);
x_44 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__3(x_37, x_38, x_10);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_16);
lean_ctor_set(x_45, 1, x_7);
lean_ctor_set(x_45, 2, x_36);
lean_ctor_set(x_45, 3, x_44);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_1);
lean_ctor_set(x_46, 2, x_2);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_46);
return x_14;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_47 = lean_ctor_get(x_16, 7);
x_48 = lean_ctor_get(x_16, 0);
x_49 = lean_ctor_get(x_16, 2);
x_50 = lean_ctor_get(x_16, 3);
x_51 = lean_ctor_get(x_16, 4);
x_52 = lean_ctor_get(x_16, 5);
x_53 = lean_ctor_get(x_16, 6);
x_54 = lean_ctor_get(x_16, 8);
x_55 = lean_ctor_get(x_16, 9);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_47);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_16);
x_56 = lean_ctor_get_uint8(x_47, sizeof(void*)*3);
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_47, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 x_59 = x_47;
} else {
 lean_dec_ref(x_47);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_7, 0);
lean_inc(x_60);
x_61 = lean_array_size(x_10);
x_62 = 0;
lean_inc(x_10);
x_63 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0(x_61, x_62, x_10);
x_64 = lean_array_get_size(x_63);
x_65 = l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1(x_63, x_11, x_64);
lean_dec(x_64);
lean_dec(x_63);
x_66 = l_Array_toPArray_x27___redArg(x_65);
lean_dec(x_65);
if (lean_is_scalar(x_59)) {
 x_67 = lean_alloc_ctor(0, 3, 1);
} else {
 x_67 = x_59;
}
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_58);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*3, x_56);
x_68 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_68, 0, x_48);
lean_ctor_set(x_68, 1, x_12);
lean_ctor_set(x_68, 2, x_49);
lean_ctor_set(x_68, 3, x_50);
lean_ctor_set(x_68, 4, x_51);
lean_ctor_set(x_68, 5, x_52);
lean_ctor_set(x_68, 6, x_53);
lean_ctor_set(x_68, 7, x_67);
lean_ctor_set(x_68, 8, x_54);
lean_ctor_set(x_68, 9, x_55);
x_69 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__3(x_61, x_62, x_10);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_7);
lean_ctor_set(x_70, 2, x_60);
lean_ctor_set(x_70, 3, x_69);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_1);
lean_ctor_set(x_71, 2, x_2);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 0, x_71);
return x_14;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_72 = lean_ctor_get(x_14, 1);
lean_inc(x_72);
lean_dec(x_14);
x_73 = lean_ctor_get(x_72, 7);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 5);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 6);
lean_inc(x_79);
x_80 = lean_ctor_get(x_72, 8);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 9);
lean_inc(x_81);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 lean_ctor_release(x_72, 6);
 lean_ctor_release(x_72, 7);
 lean_ctor_release(x_72, 8);
 lean_ctor_release(x_72, 9);
 x_82 = x_72;
} else {
 lean_dec_ref(x_72);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get_uint8(x_73, sizeof(void*)*3);
x_84 = lean_ctor_get(x_73, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_73, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_86 = x_73;
} else {
 lean_dec_ref(x_73);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_7, 0);
lean_inc(x_87);
x_88 = lean_array_size(x_10);
x_89 = 0;
lean_inc(x_10);
x_90 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0(x_88, x_89, x_10);
x_91 = lean_array_get_size(x_90);
x_92 = l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1(x_90, x_11, x_91);
lean_dec(x_91);
lean_dec(x_90);
x_93 = l_Array_toPArray_x27___redArg(x_92);
lean_dec(x_92);
if (lean_is_scalar(x_86)) {
 x_94 = lean_alloc_ctor(0, 3, 1);
} else {
 x_94 = x_86;
}
lean_ctor_set(x_94, 0, x_84);
lean_ctor_set(x_94, 1, x_85);
lean_ctor_set(x_94, 2, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*3, x_83);
if (lean_is_scalar(x_82)) {
 x_95 = lean_alloc_ctor(0, 10, 0);
} else {
 x_95 = x_82;
}
lean_ctor_set(x_95, 0, x_74);
lean_ctor_set(x_95, 1, x_12);
lean_ctor_set(x_95, 2, x_75);
lean_ctor_set(x_95, 3, x_76);
lean_ctor_set(x_95, 4, x_77);
lean_ctor_set(x_95, 5, x_78);
lean_ctor_set(x_95, 6, x_79);
lean_ctor_set(x_95, 7, x_94);
lean_ctor_set(x_95, 8, x_80);
lean_ctor_set(x_95, 9, x_81);
x_96 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__3(x_88, x_89, x_10);
x_97 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_7);
lean_ctor_set(x_97, 2, x_87);
lean_ctor_set(x_97, 3, x_96);
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_1);
lean_ctor_set(x_98, 2, x_2);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_5);
return x_99;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_8);
lean_dec(x_7);
x_112 = lean_ctor_get(x_9, 0);
lean_inc(x_112);
lean_dec(x_9);
x_113 = lean_ctor_get(x_112, 3);
lean_inc(x_113);
lean_dec(x_112);
x_3 = x_113;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__3(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_IO_processCommandsIncrementally___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_14; 
x_14 = lean_box(0);
x_6 = x_14;
goto block_13;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_4, 0, x_19);
x_6 = x_4;
goto block_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec(x_4);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_6 = x_24;
goto block_13;
}
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_7 = l_Lean_Language_Lean_processCommands(x_1, x_2, x_3, x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = lean_task_get_own(x_8);
x_11 = l_Lean_Elab_IO_processCommandsIncrementally___closed__0;
x_12 = l_Lean_Elab_IO_processCommandsIncrementally_go(x_1, x_10, x_8, x_11, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_box(0);
x_6 = l_Lean_Elab_IO_processCommandsIncrementally(x_1, x_2, x_3, x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Elab_process___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_process___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<input>", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Elab_process___closed__1;
x_6 = x_27;
goto block_26;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
lean_dec(x_4);
x_6 = x_28;
goto block_26;
}
block_26:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Parser_mkInputContext(x_1, x_6, x_8);
x_10 = l_Lean_Elab_process___closed__0;
x_11 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3;
x_12 = l_Lean_Elab_Command_mkState(x_2, x_11, x_3);
x_13 = l_Lean_Elab_IO_processCommands(x_9, x_10, x_12, x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_load_dynlib(x_7, x_5);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_runFrontend_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0;
x_14 = l_Array_append___redArg(x_4, x_13);
x_5 = x_14;
goto block_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2___closed__0;
x_17 = lean_array_push(x_16, x_15);
x_18 = l_Array_append___redArg(x_4, x_17);
lean_dec(x_17);
x_5 = x_18;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_box(2);
x_8 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_4, x_6, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint32_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_11 = l_Lean_Elab_HeaderSyntax_isModule(x_8);
x_12 = l_Lean_Elab_HeaderSyntax_imports(x_8, x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 4, x_11);
lean_ctor_set_uint32(x_14, sizeof(void*)*5, x_5);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_3);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_18 = x_1;
} else {
 lean_dec_ref(x_1);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_17, sizeof(void*)*6);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_17, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 5);
lean_inc(x_25);
lean_dec(x_17);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_array_get_size(x_23);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
lean_dec(x_35);
lean_dec(x_23);
x_26 = x_10;
goto block_33;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_35, x_35);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_23);
x_26 = x_10;
goto block_33;
}
else
{
lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_38 = lean_box(0);
x_39 = 0;
x_40 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_41 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__0(x_23, x_39, x_40, x_38, x_10);
lean_dec(x_23);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_26 = x_42;
goto block_33;
}
else
{
uint8_t x_43; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_41);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
block_33:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_LeanOptions_toOptions(x_25);
x_28 = l_List_forIn_x27_loop___at___Lean_KVMap_mergeBy_spec__0___redArg(x_7, x_27, x_4);
x_29 = l_Array_append___redArg(x_6, x_24);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_22);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*5 + 4, x_20);
lean_ctor_set_uint32(x_30, sizeof(void*)*5, x_5);
if (lean_is_scalar(x_18)) {
 x_31 = lean_alloc_ctor(1, 1, 0);
} else {
 x_31 = x_18;
}
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_runFrontend___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lam__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_runFrontend___lam__3___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lam__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lam__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_17; 
x_17 = lean_box(0);
x_6 = x_17;
goto block_16;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = l_Lean_Elab_runFrontend___lam__5___closed__1;
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Language_SnapshotTask_map___redArg(x_20, x_23, x_21, x_22, x_25);
lean_ctor_set(x_5, 0, x_26);
x_6 = x_5;
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = l_Lean_Elab_runFrontend___lam__5___closed__1;
x_32 = lean_box(1);
x_33 = lean_unbox(x_32);
x_34 = l_Lean_Language_SnapshotTask_map___redArg(x_28, x_31, x_29, x_30, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_6 = x_35;
goto block_16;
}
}
block_16:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Language_SnapshotTask_map___redArg(x_4, x_1, x_7, x_8, x_10);
x_12 = l_Lean_Elab_runFrontend___lam__5___closed__0;
x_13 = lean_array_push(x_12, x_11);
x_14 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(x_6, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_internal_cmdlineSnapshots;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_async;
return x_1;
}
}
static double _init_l_Lean_Elab_runFrontend___closed__2() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_output;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".olean serialization", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint32_t x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; double x_53; double x_54; double x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; 
x_25 = lean_io_mono_nanos_now(x_13);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__0___boxed), 3, 0);
x_30 = lean_box(1);
x_31 = lean_unbox(x_30);
x_32 = l_Lean_Parser_mkInputContext(x_1, x_3, x_31);
x_33 = l_Lean_Elab_runFrontend___closed__0;
x_34 = lean_unbox(x_30);
x_35 = l_Lean_Option_setIfNotSet___at___Lean_Language_Lean_process_processHeader_spec__1(x_2, x_33, x_34);
x_36 = l_Lean_Elab_runFrontend___closed__1;
x_37 = lean_unbox(x_30);
x_38 = l_Lean_Option_setIfNotSet___at___Lean_Language_Lean_process_processHeader_spec__1(x_35, x_36, x_37);
x_39 = lean_box_uint32(x_5);
lean_inc(x_38);
lean_inc(x_4);
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__1___boxed), 10, 7);
lean_closure_set(x_40, 0, x_12);
lean_closure_set(x_40, 1, x_30);
lean_closure_set(x_40, 2, x_4);
lean_closure_set(x_40, 3, x_38);
lean_closure_set(x_40, 4, x_39);
lean_closure_set(x_40, 5, x_10);
lean_closure_set(x_40, 6, x_29);
x_41 = lean_box(0);
lean_inc(x_32);
x_42 = l_Lean_Language_Lean_process(x_40, x_41, x_32, x_27);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 4);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__2___boxed), 1, 0);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3), 1, 0);
x_52 = l_Lean_Elab_Command_instInhabitedScope;
x_53 = lean_float_of_nat(x_26);
x_54 = l_Lean_Elab_runFrontend___closed__2;
x_55 = lean_float_div(x_53, x_54);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_216; 
x_216 = lean_box(0);
x_192 = x_43;
x_193 = x_44;
x_194 = x_46;
x_195 = x_47;
x_196 = x_48;
x_197 = x_11;
x_198 = x_216;
goto block_215;
}
else
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_49);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_218 = lean_ctor_get(x_49, 0);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_inc(x_51);
x_222 = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__5), 2, 1);
lean_closure_set(x_222, 0, x_51);
x_223 = lean_unbox(x_30);
x_224 = l_Lean_Language_SnapshotTask_map___redArg(x_219, x_222, x_220, x_221, x_223);
lean_ctor_set(x_49, 0, x_224);
x_192 = x_43;
x_193 = x_44;
x_194 = x_46;
x_195 = x_47;
x_196 = x_48;
x_197 = x_11;
x_198 = x_49;
goto block_215;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; 
x_225 = lean_ctor_get(x_49, 0);
lean_inc(x_225);
lean_dec(x_49);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_inc(x_51);
x_229 = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__5), 2, 1);
lean_closure_set(x_229, 0, x_51);
x_230 = lean_unbox(x_30);
x_231 = l_Lean_Language_SnapshotTask_map___redArg(x_226, x_229, x_227, x_228, x_230);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_231);
x_192 = x_43;
x_193 = x_44;
x_194 = x_46;
x_195 = x_47;
x_196 = x_48;
x_197 = x_11;
x_198 = x_232;
goto block_215;
}
}
block_24:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_runtime_forget(x_15, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
block_79:
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Lean_Elab_runFrontend___closed__3;
x_60 = l_Lean_Option_get_x3f___at___Lean_addTraceAsMessages___at___Lean_Core_wrapAsyncAsSnapshot_spec__0_spec__0(x_38, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_dec(x_50);
lean_dec(x_38);
lean_dec(x_4);
x_14 = x_57;
x_15 = x_56;
x_16 = x_58;
goto block_24;
}
else
{
lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec(x_60);
lean_inc(x_56);
x_62 = l_Lean_Language_SnapshotTree_getAll(x_56);
x_63 = lean_array_size(x_62);
x_64 = 0;
x_65 = l_Array_mapMUnsafe_map___at___Lean_Elab_runFrontend_spec__1(x_63, x_64, x_62);
x_66 = lean_unbox(x_30);
x_67 = l_Lean_Name_toString(x_4, x_66, x_50);
x_68 = l_Lean_Firefox_Profile_export(x_67, x_55, x_65, x_38, x_58);
lean_dec(x_38);
lean_dec(x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l___private_Lean_Util_Profiler_0__Lean_Firefox_toJsonProfile____x40_Lean_Util_Profiler___hyg_4963_(x_69);
x_72 = l_Lean_Json_compress(x_71);
x_73 = l_IO_FS_writeFile(x_61, x_72, x_70);
lean_dec(x_72);
lean_dec(x_61);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_14 = x_57;
x_15 = x_56;
x_16 = x_74;
goto block_24;
}
else
{
uint8_t x_75; 
lean_dec(x_57);
lean_dec(x_56);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_73, 0);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_73);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
block_105:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_86 = lean_ctor_get(x_32, 2);
lean_inc(x_86);
lean_dec(x_32);
x_87 = lean_box(0);
x_88 = lean_unbox(x_87);
x_89 = lean_unbox(x_87);
x_90 = l_Lean_Server_findModuleRefs(x_86, x_85, x_88, x_89);
lean_dec(x_85);
x_91 = l_Lean_Server_ModuleRefs_toLspModuleRefs(x_90, x_80);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_unsigned_to_nat(4u);
x_95 = l_Lean_Server_collectImports(x_84);
lean_inc(x_4);
x_96 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_4);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_96, 3, x_92);
x_97 = l___private_Lean_Server_References_0__Lean_Server_toJsonIlean____x40_Lean_Server_References___hyg_1585_(x_96);
x_98 = l_Lean_Json_compress(x_97);
x_99 = l_IO_FS_writeFile(x_83, x_98, x_93);
lean_dec(x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_56 = x_82;
x_57 = x_81;
x_58 = x_100;
goto block_79;
}
else
{
uint8_t x_101; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_50);
lean_dec(x_38);
lean_dec(x_4);
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
return x_99;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_99, 0);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_99);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
block_120:
{
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_32);
x_56 = x_107;
x_57 = x_106;
x_58 = x_110;
goto block_79;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_7, 0);
lean_inc(x_107);
x_112 = l_Lean_Language_SnapshotTree_getAll(x_107);
x_113 = l_Lean_Elab_runFrontend___closed__4;
x_114 = lean_array_get_size(x_112);
x_115 = lean_nat_dec_lt(x_109, x_114);
lean_dec(x_109);
if (x_115 == 0)
{
lean_dec(x_114);
lean_dec(x_112);
x_80 = x_110;
x_81 = x_106;
x_82 = x_107;
x_83 = x_111;
x_84 = x_108;
x_85 = x_113;
goto block_105;
}
else
{
uint8_t x_116; 
x_116 = lean_nat_dec_le(x_114, x_114);
if (x_116 == 0)
{
lean_dec(x_114);
lean_dec(x_112);
x_80 = x_110;
x_81 = x_106;
x_82 = x_107;
x_83 = x_111;
x_84 = x_108;
x_85 = x_113;
goto block_105;
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; 
x_117 = 0;
x_118 = lean_usize_of_nat(x_114);
lean_dec(x_114);
x_119 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2(x_112, x_117, x_118, x_113);
lean_dec(x_112);
x_80 = x_110;
x_81 = x_106;
x_82 = x_107;
x_83 = x_111;
x_84 = x_108;
x_85 = x_119;
goto block_105;
}
}
}
}
block_140:
{
if (x_126 == 0)
{
lean_dec(x_45);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_125);
x_106 = x_122;
x_107 = x_121;
x_108 = x_123;
x_109 = x_124;
x_110 = x_127;
goto block_120;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_6, 0);
lean_inc(x_128);
lean_dec(x_6);
x_129 = l_Lean_Elab_runFrontend___closed__5;
lean_inc(x_122);
x_130 = lean_alloc_closure((void*)(l_Lean_writeModule), 3, 2);
lean_closure_set(x_130, 0, x_122);
lean_closure_set(x_130, 1, x_128);
x_131 = lean_box(0);
x_132 = l_Lean_profileitIOUnsafe___redArg(x_129, x_125, x_130, x_131, x_127);
lean_dec(x_125);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_106 = x_122;
x_107 = x_121;
x_108 = x_123;
x_109 = x_124;
x_110 = x_133;
goto block_120;
}
else
{
uint8_t x_134; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_50);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_4);
x_134 = !lean_is_exclusive(x_132);
if (x_134 == 0)
{
return x_132;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_132, 0);
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_132);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_50);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
x_138 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_45;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_127);
return x_139;
}
}
block_191:
{
lean_object* x_148; 
x_148 = l_Lean_Language_SnapshotTree_runAndReport(x_143, x_38, x_8, x_147, x_142);
lean_dec(x_147);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = lean_ctor_get(x_148, 1);
x_152 = l_Lean_Language_Lean_waitForFinalCmdState_x3f(x_141);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
lean_dec(x_150);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
x_153 = lean_box(0);
lean_ctor_set(x_148, 0, x_153);
return x_148;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_free_object(x_148);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 2);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_145);
x_157 = l_List_get_x21Internal___redArg(x_52, x_156, x_145);
lean_dec(x_156);
if (x_146 == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_unbox(x_150);
lean_dec(x_150);
x_121 = x_143;
x_122 = x_155;
x_123 = x_144;
x_124 = x_145;
x_125 = x_158;
x_126 = x_159;
x_127 = x_151;
goto block_140;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
lean_inc(x_155);
x_161 = l_Lean_Environment_displayStats(x_155, x_151);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = lean_unbox(x_150);
lean_dec(x_150);
x_121 = x_143;
x_122 = x_155;
x_123 = x_144;
x_124 = x_145;
x_125 = x_160;
x_126 = x_163;
x_127 = x_162;
goto block_140;
}
else
{
uint8_t x_164; 
lean_dec(x_160);
lean_dec(x_155);
lean_dec(x_150);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
x_164 = !lean_is_exclusive(x_161);
if (x_164 == 0)
{
return x_161;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_161, 0);
x_166 = lean_ctor_get(x_161, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_161);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_148, 0);
x_169 = lean_ctor_get(x_148, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_148);
x_170 = l_Lean_Language_Lean_waitForFinalCmdState_x3f(x_141);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_168);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
x_171 = lean_box(0);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_169);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_170, 0);
lean_inc(x_173);
lean_dec(x_170);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 2);
lean_inc(x_175);
lean_dec(x_173);
lean_inc(x_145);
x_176 = l_List_get_x21Internal___redArg(x_52, x_175, x_145);
lean_dec(x_175);
if (x_146 == 0)
{
lean_object* x_177; uint8_t x_178; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_unbox(x_168);
lean_dec(x_168);
x_121 = x_143;
x_122 = x_174;
x_123 = x_144;
x_124 = x_145;
x_125 = x_177;
x_126 = x_178;
x_127 = x_169;
goto block_140;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
lean_inc(x_174);
x_180 = l_Lean_Environment_displayStats(x_174, x_169);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_unbox(x_168);
lean_dec(x_168);
x_121 = x_143;
x_122 = x_174;
x_123 = x_144;
x_124 = x_145;
x_125 = x_179;
x_126 = x_182;
x_127 = x_181;
goto block_140;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_179);
lean_dec(x_174);
lean_dec(x_168);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
x_183 = lean_ctor_get(x_180, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_185 = x_180;
} else {
 lean_dec_ref(x_180);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
x_187 = !lean_is_exclusive(x_148);
if (x_187 == 0)
{
return x_148;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_148, 0);
x_189 = lean_ctor_get(x_148, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_148);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
block_215:
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_199 = lean_ctor_get(x_195, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_195, 1);
lean_inc(x_200);
x_201 = lean_unbox(x_30);
x_202 = l_Lean_Language_SnapshotTask_map___redArg(x_195, x_51, x_199, x_200, x_201);
x_203 = l_Lean_Elab_runFrontend___lam__5___closed__0;
x_204 = lean_array_push(x_203, x_202);
x_205 = l___private_Lean_Language_Lean_Types_0__Lean_Language_Lean_pushOpt___redArg(x_198, x_204);
if (lean_is_scalar(x_28)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_28;
}
lean_ctor_set(x_206, 0, x_194);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_box(0);
x_208 = lean_unsigned_to_nat(0u);
x_209 = lean_array_get_size(x_9);
x_210 = lean_nat_dec_lt(x_208, x_209);
if (x_210 == 0)
{
lean_dec(x_209);
x_141 = x_192;
x_142 = x_193;
x_143 = x_206;
x_144 = x_196;
x_145 = x_208;
x_146 = x_197;
x_147 = x_207;
goto block_191;
}
else
{
uint8_t x_211; 
x_211 = lean_nat_dec_le(x_209, x_209);
if (x_211 == 0)
{
lean_dec(x_209);
x_141 = x_192;
x_142 = x_193;
x_143 = x_206;
x_144 = x_196;
x_145 = x_208;
x_146 = x_197;
x_147 = x_207;
goto block_191;
}
else
{
size_t x_212; size_t x_213; lean_object* x_214; 
x_212 = 0;
x_213 = lean_usize_of_nat(x_209);
lean_dec(x_209);
x_214 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__3(x_9, x_212, x_213, x_207);
x_141 = x_192;
x_142 = x_193;
x_143 = x_206;
x_144 = x_196;
x_145 = x_208;
x_146 = x_197;
x_147 = x_214;
goto block_191;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_runFrontend_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_runFrontend_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_runFrontend___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint32_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_runFrontend___lam__1(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_runFrontend___lam__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint32_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = lean_unbox(x_11);
lean_dec(x_11);
x_17 = l_Lean_Elab_runFrontend(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_15, x_9, x_10, x_16, x_12, x_13);
lean_dec(x_9);
lean_dec(x_7);
return x_17;
}
}
lean_object* initialize_Lean_Language_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Profile(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_References(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Profiler(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Language_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Profile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_References(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Profiler(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0 = _init_l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0);
l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__0 = _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__0();
lean_mark_persistent(l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__0);
l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1 = _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1();
lean_mark_persistent(l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1);
l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__2 = _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__2();
lean_mark_persistent(l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__2);
l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3 = _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3();
lean_mark_persistent(l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3);
l_Lean_Elab_Frontend_processCommand___closed__0 = _init_l_Lean_Elab_Frontend_processCommand___closed__0();
lean_mark_persistent(l_Lean_Elab_Frontend_processCommand___closed__0);
l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0 = _init_l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0();
lean_mark_persistent(l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0);
l_Lean_Elab_IO_processCommandsIncrementally___closed__0 = _init_l_Lean_Elab_IO_processCommandsIncrementally___closed__0();
lean_mark_persistent(l_Lean_Elab_IO_processCommandsIncrementally___closed__0);
l_Lean_Elab_process___closed__0 = _init_l_Lean_Elab_process___closed__0();
lean_mark_persistent(l_Lean_Elab_process___closed__0);
l_Lean_Elab_process___closed__1 = _init_l_Lean_Elab_process___closed__1();
lean_mark_persistent(l_Lean_Elab_process___closed__1);
l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2___closed__0);
l_Lean_Elab_runFrontend___lam__3___closed__0 = _init_l_Lean_Elab_runFrontend___lam__3___closed__0();
lean_mark_persistent(l_Lean_Elab_runFrontend___lam__3___closed__0);
l_Lean_Elab_runFrontend___lam__5___closed__0 = _init_l_Lean_Elab_runFrontend___lam__5___closed__0();
lean_mark_persistent(l_Lean_Elab_runFrontend___lam__5___closed__0);
l_Lean_Elab_runFrontend___lam__5___closed__1 = _init_l_Lean_Elab_runFrontend___lam__5___closed__1();
lean_mark_persistent(l_Lean_Elab_runFrontend___lam__5___closed__1);
l_Lean_Elab_runFrontend___closed__0 = _init_l_Lean_Elab_runFrontend___closed__0();
lean_mark_persistent(l_Lean_Elab_runFrontend___closed__0);
l_Lean_Elab_runFrontend___closed__1 = _init_l_Lean_Elab_runFrontend___closed__1();
lean_mark_persistent(l_Lean_Elab_runFrontend___closed__1);
l_Lean_Elab_runFrontend___closed__2 = _init_l_Lean_Elab_runFrontend___closed__2();
l_Lean_Elab_runFrontend___closed__3 = _init_l_Lean_Elab_runFrontend___closed__3();
lean_mark_persistent(l_Lean_Elab_runFrontend___closed__3);
l_Lean_Elab_runFrontend___closed__4 = _init_l_Lean_Elab_runFrontend___closed__4();
lean_mark_persistent(l_Lean_Elab_runFrontend___closed__4);
l_Lean_Elab_runFrontend___closed__5 = _init_l_Lean_Elab_runFrontend___closed__5();
lean_mark_persistent(l_Lean_Elab_runFrontend___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
