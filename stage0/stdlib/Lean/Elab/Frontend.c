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
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__5(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
double lean_float_div(double, double);
static lean_object* l_Lean_Elab_process___closed__1;
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_Elab_runFrontend_spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___closed__5;
static lean_object* l_Lean_Elab_runFrontend___lam__2___closed__0;
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
lean_object* l_Lean_Firefox_toJsonProfile____x40_Lean_Util_Profiler___hyg_4936_(lean_object*);
static lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
lean_object* l_Lean_Language_Lean_pushOpt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Array_toPArray_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_findModuleRefs(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Frontend_processCommand___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__4(size_t, size_t, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_processCommands(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Server_collectImports(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_strict_or(uint8_t, uint8_t);
static lean_object* l_Lean_Elab_IO_processCommandsIncrementally___closed__0;
lean_object* l_Lean_Environment_displayStats(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___lam__4___closed__1;
static lean_object* l_Lean_Elab_process___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___closed__4;
lean_object* lean_io_mono_nanos_now(lean_object*);
static lean_object* l_Lean_Elab_runFrontend___lam__4___closed__0;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__5(lean_object*, size_t, size_t, lean_object*);
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
static lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1;
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_runFrontend_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_runtime_forget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg___boxed(lean_object*, lean_object*, lean_object*);
static double l_Lean_Elab_runFrontend___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_runFrontend_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_Elab_runFrontend_spec__3(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_writeModule(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_load_dynlib(lean_object*, lean_object*);
lean_object* l_Lean_Server_toJsonIlean____x40_Lean_Server_References___hyg_1580_(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__5___closed__0;
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_contains(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(x_4);
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
lean_dec_ref(x_2);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_st_mk_ref(x_8, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = 0;
lean_inc_ref(x_14);
lean_inc_ref(x_13);
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
lean_ctor_set_uint8(x_22, sizeof(void*)*9, x_21);
lean_inc(x_11);
x_23 = lean_apply_3(x_1, x_22, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_st_ref_get(x_11, x_25);
lean_dec(x_11);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_Elab_Frontend_setCommandState___redArg(x_27, x_3, x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_24);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_11);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec_ref(x_23);
x_36 = l_Lean_Exception_toMessageData(x_34);
x_37 = l_Lean_MessageData_toString(x_36, x_35);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_42);
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
x_46 = lean_string_append(x_45, x_43);
lean_dec(x_43);
x_47 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_st_mk_ref(x_9, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_box(0);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = 0;
lean_inc_ref(x_15);
lean_inc_ref(x_14);
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
lean_ctor_set_uint8(x_23, sizeof(void*)*9, x_22);
lean_inc(x_12);
x_24 = lean_apply_3(x_2, x_23, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_st_ref_get(x_12, x_26);
lean_dec(x_12);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l_Lean_Elab_Frontend_setCommandState___redArg(x_28, x_4, x_29);
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
lean_dec(x_12);
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_dec_ref(x_24);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Frontend_runCommandElabM___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Frontend_runCommandElabM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
x_1 = lean_box(1);
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
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_st_mk_ref(x_8, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_24 = lean_st_ref_take(x_11, x_12);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3;
lean_ctor_set(x_25, 1, x_30);
x_31 = lean_st_ref_set(x_11, x_25, x_26);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_box(0);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_box(0);
x_40 = 0;
lean_inc_ref(x_34);
lean_inc_ref(x_33);
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
lean_ctor_set_uint8(x_41, sizeof(void*)*9, x_40);
lean_inc(x_11);
x_42 = l_Lean_Elab_Command_elabCommandTopLevel(x_1, x_41, x_11, x_32);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_st_ref_get(x_11, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_st_ref_take(x_11, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_50);
lean_dec(x_45);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_48, 1);
lean_dec(x_52);
x_53 = l_Lean_MessageLog_append(x_28, x_50);
lean_ctor_set(x_48, 1, x_53);
x_54 = lean_st_ref_set(x_11, x_48, x_49);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_box(0);
x_13 = x_56;
x_14 = x_55;
goto block_23;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 2);
x_59 = lean_ctor_get(x_48, 3);
x_60 = lean_ctor_get(x_48, 4);
x_61 = lean_ctor_get(x_48, 5);
x_62 = lean_ctor_get(x_48, 6);
x_63 = lean_ctor_get(x_48, 7);
x_64 = lean_ctor_get(x_48, 8);
x_65 = lean_ctor_get(x_48, 9);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_66 = l_Lean_MessageLog_append(x_28, x_50);
x_67 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_58);
lean_ctor_set(x_67, 3, x_59);
lean_ctor_set(x_67, 4, x_60);
lean_ctor_set(x_67, 5, x_61);
lean_ctor_set(x_67, 6, x_62);
lean_ctor_set(x_67, 7, x_63);
lean_ctor_set(x_67, 8, x_64);
lean_ctor_set(x_67, 9, x_65);
x_68 = lean_st_ref_set(x_11, x_67, x_49);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = lean_box(0);
x_13 = x_70;
x_14 = x_69;
goto block_23;
}
}
else
{
lean_dec_ref(x_28);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_42, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_42, 1);
lean_inc(x_72);
lean_dec_ref(x_42);
x_13 = x_71;
x_14 = x_72;
goto block_23;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_11);
x_73 = lean_ctor_get(x_42, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
lean_dec_ref(x_42);
x_75 = l_Lean_Exception_toMessageData(x_73);
x_76 = l_Lean_MessageData_toString(x_75, x_74);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
x_80 = lean_string_append(x_79, x_78);
lean_dec(x_78);
x_81 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 0, x_81);
return x_76;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_76, 0);
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_76);
x_84 = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
x_85 = lean_string_append(x_84, x_82);
lean_dec(x_82);
x_86 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; 
x_88 = lean_ctor_get(x_25, 0);
x_89 = lean_ctor_get(x_25, 1);
x_90 = lean_ctor_get(x_25, 2);
x_91 = lean_ctor_get(x_25, 3);
x_92 = lean_ctor_get(x_25, 4);
x_93 = lean_ctor_get(x_25, 5);
x_94 = lean_ctor_get(x_25, 6);
x_95 = lean_ctor_get(x_25, 7);
x_96 = lean_ctor_get(x_25, 8);
x_97 = lean_ctor_get(x_25, 9);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_25);
x_98 = lean_unsigned_to_nat(0u);
x_99 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3;
x_100 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_100, 0, x_88);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_100, 2, x_90);
lean_ctor_set(x_100, 3, x_91);
lean_ctor_set(x_100, 4, x_92);
lean_ctor_set(x_100, 5, x_93);
lean_ctor_set(x_100, 6, x_94);
lean_ctor_set(x_100, 7, x_95);
lean_ctor_set(x_100, 8, x_96);
lean_ctor_set(x_100, 9, x_97);
x_101 = lean_st_ref_set(x_11, x_100, x_26);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_ctor_get(x_2, 1);
x_104 = lean_ctor_get(x_2, 2);
x_105 = lean_box(0);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_box(0);
x_108 = lean_box(0);
x_109 = lean_box(0);
x_110 = 0;
lean_inc_ref(x_104);
lean_inc_ref(x_103);
x_111 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_104);
lean_ctor_set(x_111, 2, x_98);
lean_ctor_set(x_111, 3, x_9);
lean_ctor_set(x_111, 4, x_105);
lean_ctor_set(x_111, 5, x_106);
lean_ctor_set(x_111, 6, x_107);
lean_ctor_set(x_111, 7, x_108);
lean_ctor_set(x_111, 8, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*9, x_110);
lean_inc(x_11);
x_112 = l_Lean_Elab_Command_elabCommandTopLevel(x_1, x_111, x_11, x_102);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = lean_st_ref_get(x_11, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec_ref(x_114);
x_117 = lean_st_ref_take(x_11, x_116);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
x_120 = lean_ctor_get(x_115, 1);
lean_inc_ref(x_120);
lean_dec(x_115);
x_121 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_118, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_118, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_118, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_118, 5);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_118, 6);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_118, 7);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_118, 8);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_118, 9);
lean_inc_ref(x_129);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 lean_ctor_release(x_118, 5);
 lean_ctor_release(x_118, 6);
 lean_ctor_release(x_118, 7);
 lean_ctor_release(x_118, 8);
 lean_ctor_release(x_118, 9);
 x_130 = x_118;
} else {
 lean_dec_ref(x_118);
 x_130 = lean_box(0);
}
x_131 = l_Lean_MessageLog_append(x_89, x_120);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 10, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_121);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_122);
lean_ctor_set(x_132, 3, x_123);
lean_ctor_set(x_132, 4, x_124);
lean_ctor_set(x_132, 5, x_125);
lean_ctor_set(x_132, 6, x_126);
lean_ctor_set(x_132, 7, x_127);
lean_ctor_set(x_132, 8, x_128);
lean_ctor_set(x_132, 9, x_129);
x_133 = lean_st_ref_set(x_11, x_132, x_119);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = lean_box(0);
x_13 = x_135;
x_14 = x_134;
goto block_23;
}
else
{
lean_dec_ref(x_89);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_112, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_112, 1);
lean_inc(x_137);
lean_dec_ref(x_112);
x_13 = x_136;
x_14 = x_137;
goto block_23;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_11);
x_138 = lean_ctor_get(x_112, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_112, 1);
lean_inc(x_139);
lean_dec_ref(x_112);
x_140 = l_Lean_Exception_toMessageData(x_138);
x_141 = l_Lean_MessageData_toString(x_140, x_139);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0;
x_146 = lean_string_append(x_145, x_142);
lean_dec(x_142);
x_147 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_147, 0, x_146);
if (lean_is_scalar(x_144)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_144;
 lean_ctor_set_tag(x_148, 1);
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_143);
return x_148;
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
lean_dec_ref(x_15);
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
lean_dec_ref(x_2);
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
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
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
lean_dec_ref(x_1);
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
lean_inc_ref(x_6);
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
lean_inc_ref(x_9);
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
lean_dec_ref(x_1);
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
lean_inc_ref(x_6);
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
lean_inc_ref(x_9);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
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
lean_dec_ref(x_2);
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
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
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
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_6, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_6, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_6, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_6, 5);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_6, 6);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_6, 7);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_6, 8);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_6, 9);
lean_inc_ref(x_45);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_4);
x_6 = l_Lean_Elab_Frontend_getCommandState___redArg(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_Elab_Frontend_getParserState___redArg(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_13);
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
lean_inc_ref(x_1);
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
lean_dec_ref(x_24);
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
lean_dec_ref(x_29);
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
lean_dec_ref(x_35);
x_37 = l_Lean_Elab_Frontend_setParserState___redArg(x_27, x_2, x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_Elab_Frontend_setMessages___redArg(x_28, x_2, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
lean_inc(x_26);
x_41 = l_Lean_Elab_Frontend_elabCommandAtFrontend(x_26, x_1, x_2, x_40);
lean_dec_ref(x_1);
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
lean_dec_ref(x_60);
x_62 = l_Lean_Elab_Frontend_setParserState___redArg(x_27, x_2, x_61);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_Lean_Elab_Frontend_setMessages___redArg(x_28, x_2, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
lean_inc(x_26);
x_66 = l_Lean_Elab_Frontend_elabCommandAtFrontend(x_26, x_1, x_2, x_65);
lean_dec_ref(x_1);
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
lean_inc_ref(x_1);
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
lean_dec_ref(x_4);
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_Language_SnapshotTask_get___redArg(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(0u);
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
lean_dec_ref(x_11);
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
x_7 = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_9, x_2, x_7);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_MessageLog_append(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_task_get_own(x_3);
x_7 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_6, 4);
lean_inc(x_9);
x_10 = lean_array_push(x_4, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_101; lean_object* x_102; lean_object* x_103; size_t x_104; size_t x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_11 = lean_unsigned_to_nat(0u);
x_101 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3;
lean_inc_ref(x_2);
x_102 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(x_2);
x_103 = l_Lean_Language_SnapshotTree_getAll(x_102);
x_104 = lean_array_size(x_103);
x_105 = 0;
x_106 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__4(x_104, x_105, x_103);
x_107 = lean_array_get_size(x_106);
x_108 = lean_nat_dec_lt(x_11, x_107);
if (x_108 == 0)
{
lean_dec(x_107);
lean_dec_ref(x_106);
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
lean_dec_ref(x_106);
x_12 = x_101;
goto block_100;
}
else
{
size_t x_110; lean_object* x_111; 
x_110 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_111 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__5(x_106, x_105, x_110, x_101);
lean_dec_ref(x_106);
x_12 = x_111;
goto block_100;
}
}
block_100:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_8);
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
lean_inc_ref(x_10);
x_26 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0(x_24, x_25, x_10);
x_27 = lean_array_get_size(x_26);
x_28 = l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1(x_26, x_11, x_27);
lean_dec(x_27);
lean_dec_ref(x_26);
x_29 = l_Array_toPArray_x27___redArg(x_28);
lean_dec_ref(x_28);
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
lean_inc_ref(x_10);
x_39 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0(x_37, x_38, x_10);
x_40 = lean_array_get_size(x_39);
x_41 = l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1(x_39, x_11, x_40);
lean_dec(x_40);
lean_dec_ref(x_39);
x_42 = l_Array_toPArray_x27___redArg(x_41);
lean_dec_ref(x_41);
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
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_58);
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
lean_inc_ref(x_10);
x_63 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0(x_61, x_62, x_10);
x_64 = lean_array_get_size(x_63);
x_65 = l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1(x_63, x_11, x_64);
lean_dec(x_64);
lean_dec_ref(x_63);
x_66 = l_Array_toPArray_x27___redArg(x_65);
lean_dec_ref(x_65);
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
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_72, 0);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_72, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 5);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_72, 6);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_72, 8);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_72, 9);
lean_inc_ref(x_81);
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
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_73, 1);
lean_inc_ref(x_85);
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
lean_inc_ref(x_10);
x_90 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__0(x_88, x_89, x_10);
x_91 = lean_array_get_size(x_90);
x_92 = l_Array_filterMapM___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__1(x_90, x_11, x_91);
lean_dec(x_91);
lean_dec_ref(x_90);
x_93 = l_Array_toPArray_x27___redArg(x_92);
lean_dec_ref(x_92);
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
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_112 = lean_ctor_get(x_9, 0);
lean_inc(x_112);
lean_dec_ref(x_9);
x_113 = lean_ctor_get(x_112, 3);
lean_inc_ref(x_113);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_IO_processCommandsIncrementally_go_spec__5(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
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
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_18);
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
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_22);
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
lean_inc_ref(x_1);
x_7 = l_Lean_Language_Lean_processCommands(x_1, x_2, x_3, x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
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
lean_inc_ref(x_9);
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
lean_inc_ref(x_12);
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
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
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
lean_object* x_26; 
x_26 = l_Lean_Elab_process___closed__1;
x_6 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
lean_dec_ref(x_4);
x_6 = x_27;
goto block_25;
}
block_25:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = 1;
x_8 = l_Lean_Parser_mkInputContext(x_1, x_6, x_7);
x_9 = l_Lean_Elab_process___closed__0;
x_10 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3;
x_11 = l_Lean_Elab_Command_mkState(x_2, x_10, x_3);
x_12 = l_Lean_Elab_IO_processCommands(x_8, x_9, x_11, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_5, 0, x_3);
x_6 = l_Lean_KVMap_insertCore(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_KVMap_contains(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Option_set___at___Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0_spec__0(x_1, x_2, x_3);
return x_6;
}
else
{
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_load_dynlib(x_7, x_5);
lean_dec_ref(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
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
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_Elab_runFrontend_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; 
lean_free_object(x_4);
lean_dec(x_7);
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_box(0);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_runFrontend_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
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
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_dec_ref(x_11);
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
lean_dec_ref(x_12);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__5___closed__0;
x_17 = lean_array_push(x_16, x_15);
x_18 = l_Array_append___redArg(x_4, x_17);
lean_dec_ref(x_17);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 2;
x_8 = lean_box(x_7);
x_9 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_NameMap_insert_spec__0___redArg(x_6, x_8, x_4);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
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
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint32_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_7);
x_25 = l_Lean_Elab_HeaderSyntax_isModule(x_8);
x_26 = l_Lean_Elab_HeaderSyntax_imports(x_8, x_2);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_4);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_6);
lean_ctor_set_uint8(x_28, sizeof(void*)*5 + 4, x_25);
lean_ctor_set_uint32(x_28, sizeof(void*)*5, x_5);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_10);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_3);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_31, sizeof(void*)*6);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 3);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_31, 4);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_31, 5);
lean_inc(x_38);
lean_dec(x_31);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get_size(x_36);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec_ref(x_36);
x_39 = x_10;
goto block_44;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_46, x_46);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec_ref(x_36);
x_39 = x_10;
goto block_44;
}
else
{
lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
x_49 = lean_box(0);
x_50 = 0;
x_51 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_52 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2(x_36, x_50, x_51, x_49, x_10);
lean_dec_ref(x_36);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec_ref(x_52);
x_39 = x_53;
goto block_44;
}
else
{
uint8_t x_54; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_52);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
block_44:
{
uint8_t x_40; uint8_t x_41; 
x_40 = l_Lean_Elab_HeaderSyntax_isModule(x_8);
x_41 = lean_strict_or(x_33, x_40);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_42; 
x_42 = l_Lean_Elab_HeaderSyntax_imports(x_8, x_2);
x_11 = x_38;
x_12 = x_39;
x_13 = x_41;
x_14 = x_32;
x_15 = x_37;
x_16 = x_35;
x_17 = x_42;
goto block_24;
}
else
{
lean_object* x_43; 
lean_dec(x_8);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec_ref(x_34);
x_11 = x_38;
x_12 = x_39;
x_13 = x_41;
x_14 = x_32;
x_15 = x_37;
x_16 = x_35;
x_17 = x_43;
goto block_24;
}
}
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = l_Lean_LeanOptions_toOptions(x_11);
x_19 = l_List_forIn_x27_loop___at___Lean_KVMap_mergeBy_spec__0___redArg(x_7, x_18, x_4);
x_20 = l_Array_append___redArg(x_6, x_15);
lean_dec_ref(x_15);
x_21 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*5 + 4, x_13);
lean_ctor_set_uint32(x_21, sizeof(void*)*5, x_5);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_runFrontend___lam__2___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lam__4___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lam__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec_ref(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
x_6 = x_16;
goto block_15;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = l_Lean_Elab_runFrontend___lam__4___closed__1;
x_23 = 1;
x_24 = l_Lean_Language_SnapshotTask_map___redArg(x_19, x_22, x_20, x_21, x_23);
lean_ctor_set(x_5, 0, x_24);
x_6 = x_5;
goto block_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = l_Lean_Elab_runFrontend___lam__4___closed__1;
x_30 = 1;
x_31 = l_Lean_Language_SnapshotTask_map___redArg(x_26, x_29, x_27, x_28, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_6 = x_32;
goto block_15;
}
}
block_15:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = 1;
x_10 = l_Lean_Language_SnapshotTask_map___redArg(x_4, x_1, x_7, x_8, x_9);
x_11 = l_Lean_Elab_runFrontend___lam__4___closed__0;
x_12 = lean_array_push(x_11, x_10);
x_13 = l_Lean_Language_Lean_pushOpt___redArg(x_6, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
return x_14;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; double x_50; double x_51; double x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_179; 
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
x_30 = 1;
x_31 = l_Lean_Parser_mkInputContext(x_1, x_3, x_30);
x_32 = l_Lean_Elab_runFrontend___closed__0;
x_33 = l_Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0(x_2, x_32, x_30);
x_34 = l_Lean_Elab_runFrontend___closed__1;
x_35 = l_Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0(x_33, x_34, x_30);
x_36 = lean_box(x_30);
x_37 = lean_box_uint32(x_5);
lean_inc(x_35);
lean_inc(x_4);
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__1___boxed), 10, 7);
lean_closure_set(x_38, 0, x_12);
lean_closure_set(x_38, 1, x_36);
lean_closure_set(x_38, 2, x_4);
lean_closure_set(x_38, 3, x_35);
lean_closure_set(x_38, 4, x_37);
lean_closure_set(x_38, 5, x_10);
lean_closure_set(x_38, 6, x_29);
x_39 = lean_box(0);
lean_inc_ref(x_31);
x_40 = l_Lean_Language_Lean_process(x_38, x_39, x_31, x_27);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_41, 1);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_41, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 4);
lean_inc(x_47);
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__2), 1, 0);
x_49 = l_Lean_Elab_Command_instInhabitedScope;
x_50 = lean_float_of_nat(x_26);
x_51 = l_Lean_Elab_runFrontend___closed__2;
x_52 = lean_float_div(x_50, x_51);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_196; 
x_196 = lean_box(0);
x_179 = x_196;
goto block_195;
}
else
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_47);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_ctor_get(x_47, 0);
x_199 = lean_ctor_get(x_198, 1);
lean_inc_ref(x_199);
lean_dec(x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_inc_ref(x_48);
x_202 = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4), 2, 1);
lean_closure_set(x_202, 0, x_48);
x_203 = l_Lean_Language_SnapshotTask_map___redArg(x_199, x_202, x_200, x_201, x_30);
lean_ctor_set(x_47, 0, x_203);
x_179 = x_47;
goto block_195;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_204 = lean_ctor_get(x_47, 0);
lean_inc(x_204);
lean_dec(x_47);
x_205 = lean_ctor_get(x_204, 1);
lean_inc_ref(x_205);
lean_dec(x_204);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_inc_ref(x_48);
x_208 = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4), 2, 1);
lean_closure_set(x_208, 0, x_48);
x_209 = l_Lean_Language_SnapshotTask_map___redArg(x_205, x_208, x_206, x_207, x_30);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_179 = x_210;
goto block_195;
}
}
block_24:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_runtime_forget(x_14, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
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
lean_ctor_set(x_22, 0, x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
block_75:
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_Elab_runFrontend___closed__3;
x_57 = l_Lean_Option_get_x3f___at___Lean_Elab_runFrontend_spec__3(x_35, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_dec(x_35);
lean_dec(x_4);
x_14 = x_53;
x_15 = x_54;
x_16 = x_55;
goto block_24;
}
else
{
lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc_ref(x_53);
x_59 = l_Lean_Language_SnapshotTree_getAll(x_53);
x_60 = lean_array_size(x_59);
x_61 = 0;
x_62 = l_Array_mapMUnsafe_map___at___Lean_Elab_runFrontend_spec__4(x_60, x_61, x_59);
x_63 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_4, x_30);
x_64 = l_Lean_Firefox_Profile_export(x_63, x_52, x_62, x_35, x_55);
lean_dec(x_35);
lean_dec_ref(x_62);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = l_Lean_Firefox_toJsonProfile____x40_Lean_Util_Profiler___hyg_4936_(x_65);
x_68 = l_Lean_Json_compress(x_67);
x_69 = l_IO_FS_writeFile(x_58, x_68, x_66);
lean_dec_ref(x_68);
lean_dec(x_58);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
x_14 = x_53;
x_15 = x_54;
x_16 = x_70;
goto block_24;
}
else
{
uint8_t x_71; 
lean_dec_ref(x_54);
lean_dec_ref(x_53);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
return x_69;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_69);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
block_98:
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_81 = lean_ctor_get(x_31, 2);
lean_inc_ref(x_81);
lean_dec_ref(x_31);
x_82 = 0;
x_83 = l_Lean_Server_findModuleRefs(x_81, x_80, x_82, x_82);
lean_dec_ref(x_80);
x_84 = l_Lean_Server_ModuleRefs_toLspModuleRefs(x_83, x_77);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = lean_unsigned_to_nat(4u);
x_88 = l_Lean_Server_collectImports(x_46);
lean_inc(x_4);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_4);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_85);
x_90 = l_Lean_Server_toJsonIlean____x40_Lean_Server_References___hyg_1580_(x_89);
x_91 = l_Lean_Json_compress(x_90);
x_92 = l_IO_FS_writeFile(x_76, x_91, x_86);
lean_dec_ref(x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec_ref(x_92);
x_53 = x_78;
x_54 = x_79;
x_55 = x_93;
goto block_75;
}
else
{
uint8_t x_94; 
lean_dec_ref(x_79);
lean_dec_ref(x_78);
lean_dec(x_35);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_92, 0);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_92);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
block_112:
{
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_101);
lean_dec(x_46);
lean_dec_ref(x_31);
x_53 = x_99;
x_54 = x_100;
x_55 = x_102;
goto block_75;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_103 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_99);
x_104 = l_Lean_Language_SnapshotTree_getAll(x_99);
x_105 = l_Lean_Elab_runFrontend___closed__4;
x_106 = lean_array_get_size(x_104);
x_107 = lean_nat_dec_lt(x_101, x_106);
lean_dec(x_101);
if (x_107 == 0)
{
lean_dec(x_106);
lean_dec_ref(x_104);
x_76 = x_103;
x_77 = x_102;
x_78 = x_99;
x_79 = x_100;
x_80 = x_105;
goto block_98;
}
else
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_106, x_106);
if (x_108 == 0)
{
lean_dec(x_106);
lean_dec_ref(x_104);
x_76 = x_103;
x_77 = x_102;
x_78 = x_99;
x_79 = x_100;
x_80 = x_105;
goto block_98;
}
else
{
size_t x_109; size_t x_110; lean_object* x_111; 
x_109 = 0;
x_110 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_111 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__5(x_104, x_109, x_110, x_105);
lean_dec_ref(x_104);
x_76 = x_103;
x_77 = x_102;
x_78 = x_99;
x_79 = x_100;
x_80 = x_111;
goto block_98;
}
}
}
}
block_131:
{
if (x_116 == 0)
{
lean_dec(x_43);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_113);
x_99 = x_114;
x_100 = x_115;
x_101 = x_117;
x_102 = x_118;
goto block_112;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_6, 0);
lean_inc(x_119);
lean_dec_ref(x_6);
x_120 = l_Lean_Elab_runFrontend___closed__5;
lean_inc_ref(x_115);
x_121 = lean_alloc_closure((void*)(l_Lean_writeModule), 3, 2);
lean_closure_set(x_121, 0, x_115);
lean_closure_set(x_121, 1, x_119);
x_122 = lean_box(0);
x_123 = l_Lean_profileitIOUnsafe___redArg(x_120, x_113, x_121, x_122, x_118);
lean_dec(x_113);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec_ref(x_123);
x_99 = x_114;
x_100 = x_115;
x_101 = x_117;
x_102 = x_124;
goto block_112;
}
else
{
uint8_t x_125; 
lean_dec(x_117);
lean_dec_ref(x_115);
lean_dec_ref(x_114);
lean_dec(x_46);
lean_dec(x_35);
lean_dec_ref(x_31);
lean_dec(x_4);
x_125 = !lean_is_exclusive(x_123);
if (x_125 == 0)
{
return x_123;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_123, 0);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_123);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_117);
lean_dec_ref(x_115);
lean_dec_ref(x_114);
lean_dec(x_113);
lean_dec(x_46);
lean_dec(x_35);
lean_dec_ref(x_31);
lean_dec(x_6);
lean_dec(x_4);
x_129 = lean_box(0);
if (lean_is_scalar(x_43)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_43;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_118);
return x_130;
}
}
block_178:
{
lean_object* x_135; 
x_135 = l_Lean_Language_SnapshotTree_runAndReport(x_132, x_35, x_8, x_134, x_42);
lean_dec(x_134);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ctor_get(x_135, 1);
x_139 = l_Lean_Language_Lean_waitForFinalCmdState_x3f(x_41);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; 
lean_dec(x_137);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_35);
lean_dec_ref(x_31);
lean_dec(x_6);
lean_dec(x_4);
x_140 = lean_box(0);
lean_ctor_set(x_135, 0, x_140);
return x_135;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_free_object(x_135);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
lean_dec_ref(x_139);
x_142 = lean_ctor_get(x_141, 0);
lean_inc_ref(x_142);
x_143 = lean_ctor_get(x_141, 2);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_133);
x_144 = l_List_get_x21Internal___redArg(x_49, x_143, x_133);
lean_dec(x_143);
if (x_11 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_unbox(x_137);
lean_dec(x_137);
x_113 = x_145;
x_114 = x_132;
x_115 = x_142;
x_116 = x_146;
x_117 = x_133;
x_118 = x_138;
goto block_131;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
lean_inc_ref(x_142);
x_148 = l_Lean_Environment_displayStats(x_142, x_138);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = lean_unbox(x_137);
lean_dec(x_137);
x_113 = x_147;
x_114 = x_132;
x_115 = x_142;
x_116 = x_150;
x_117 = x_133;
x_118 = x_149;
goto block_131;
}
else
{
uint8_t x_151; 
lean_dec(x_147);
lean_dec_ref(x_142);
lean_dec(x_137);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_35);
lean_dec_ref(x_31);
lean_dec(x_6);
lean_dec(x_4);
x_151 = !lean_is_exclusive(x_148);
if (x_151 == 0)
{
return x_148;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_148, 0);
x_153 = lean_ctor_get(x_148, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_148);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_135, 0);
x_156 = lean_ctor_get(x_135, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_135);
x_157 = l_Lean_Language_Lean_waitForFinalCmdState_x3f(x_41);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_155);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_35);
lean_dec_ref(x_31);
lean_dec(x_6);
lean_dec(x_4);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
lean_dec_ref(x_157);
x_161 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_160, 2);
lean_inc(x_162);
lean_dec(x_160);
lean_inc(x_133);
x_163 = l_List_get_x21Internal___redArg(x_49, x_162, x_133);
lean_dec(x_162);
if (x_11 == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_unbox(x_155);
lean_dec(x_155);
x_113 = x_164;
x_114 = x_132;
x_115 = x_161;
x_116 = x_165;
x_117 = x_133;
x_118 = x_156;
goto block_131;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
lean_inc_ref(x_161);
x_167 = l_Lean_Environment_displayStats(x_161, x_156);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = lean_unbox(x_155);
lean_dec(x_155);
x_113 = x_166;
x_114 = x_132;
x_115 = x_161;
x_116 = x_169;
x_117 = x_133;
x_118 = x_168;
goto block_131;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_166);
lean_dec_ref(x_161);
lean_dec(x_155);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_35);
lean_dec_ref(x_31);
lean_dec(x_6);
lean_dec(x_4);
x_170 = lean_ctor_get(x_167, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_167, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_172 = x_167;
} else {
 lean_dec_ref(x_167);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_35);
lean_dec_ref(x_31);
lean_dec(x_6);
lean_dec(x_4);
x_174 = !lean_is_exclusive(x_135);
if (x_174 == 0)
{
return x_135;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_135, 0);
x_176 = lean_ctor_get(x_135, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_135);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
block_195:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_180 = lean_ctor_get(x_45, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_45, 1);
lean_inc(x_181);
x_182 = l_Lean_Language_SnapshotTask_map___redArg(x_45, x_48, x_180, x_181, x_30);
x_183 = l_Lean_Elab_runFrontend___lam__4___closed__0;
x_184 = lean_array_push(x_183, x_182);
x_185 = l_Lean_Language_Lean_pushOpt___redArg(x_179, x_184);
if (lean_is_scalar(x_28)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_28;
}
lean_ctor_set(x_186, 0, x_44);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_box(1);
x_188 = lean_unsigned_to_nat(0u);
x_189 = lean_array_get_size(x_9);
x_190 = lean_nat_dec_lt(x_188, x_189);
if (x_190 == 0)
{
lean_dec(x_189);
x_132 = x_186;
x_133 = x_188;
x_134 = x_187;
goto block_178;
}
else
{
uint8_t x_191; 
x_191 = lean_nat_dec_le(x_189, x_189);
if (x_191 == 0)
{
lean_dec(x_189);
x_132 = x_186;
x_133 = x_188;
x_134 = x_187;
goto block_178;
}
else
{
size_t x_192; size_t x_193; lean_object* x_194; 
x_192 = 0;
x_193 = lean_usize_of_nat(x_189);
lean_dec(x_189);
x_194 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__6(x_9, x_192, x_193, x_187);
x_132 = x_186;
x_133 = x_188;
x_134 = x_194;
goto block_178;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Option_set___at___Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0_spec__0(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Option_setIfNotSet___at___Lean_Elab_runFrontend_spec__0(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__2(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___Lean_Elab_runFrontend_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get_x3f___at___Lean_Elab_runFrontend_spec__3(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_runFrontend_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_runFrontend_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__5(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__6(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_runFrontend___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint32_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_runFrontend___lam__1(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint32_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_15 = lean_unbox(x_8);
x_16 = lean_unbox(x_11);
x_17 = l_Lean_Elab_runFrontend(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_15, x_9, x_10, x_16, x_12, x_13);
lean_dec_ref(x_9);
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
l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__5___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__5___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lean_Elab_runFrontend_spec__5___closed__0);
l_Lean_Elab_runFrontend___lam__2___closed__0 = _init_l_Lean_Elab_runFrontend___lam__2___closed__0();
lean_mark_persistent(l_Lean_Elab_runFrontend___lam__2___closed__0);
l_Lean_Elab_runFrontend___lam__4___closed__0 = _init_l_Lean_Elab_runFrontend___lam__4___closed__0();
lean_mark_persistent(l_Lean_Elab_runFrontend___lam__4___closed__0);
l_Lean_Elab_runFrontend___lam__4___closed__1 = _init_l_Lean_Elab_runFrontend___lam__4___closed__1();
lean_mark_persistent(l_Lean_Elab_runFrontend___lam__4___closed__1);
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
