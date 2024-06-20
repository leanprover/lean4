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
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Firefox_Profile_export(lean_object*, double, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__2(lean_object*, lean_object*, lean_object*, double, double, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___rarg(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
double lean_float_div(double, double);
static lean_object* l_Lean_Elab_process___closed__1;
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_runFrontend___lambda__2___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___lambda__2___closed__2;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1;
lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___boxed(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object*);
static double l_Lean_Elab_runFrontend___closed__1;
static lean_object* l_Lean_Elab_runFrontend___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_findModuleRefs(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_processCommands(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___closed__3;
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__2(size_t, size_t, lean_object*);
lean_object* l_Lean_Language_reportMessages(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_process___closed__2;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__5(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Frontend_State_commands___default___closed__1;
lean_object* l_Array_toPArray_x27___rarg(lean_object*);
lean_object* lean_io_mono_nanos_now(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_set_main_module(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___lambda__2___closed__3;
lean_object* l___private_Lean_Util_Profiler_0__Lean_Firefox_toJsonProfile____x40_Lean_Util_Profiler___hyg_3604_(lean_object*);
lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
LEAN_EXPORT lean_object* lean_run_frontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Server_References_0__Lean_Server_toJsonIlean____x40_Lean_Server_References___hyg_1472_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState(lean_object*);
static lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get_x3f___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_State_commands___default;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__4(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___rarg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Language_SnapshotTask_get___rarg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___rarg___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___lambda__2___closed__5;
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_output;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Elab_Frontend_processCommand___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___boxed(lean_object*);
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos(lean_object*);
static lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
static lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__2;
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
static lean_object* _init_l_Lean_Elab_Frontend_State_commands___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_State_commands___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Frontend_State_commands___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_1);
x_10 = lean_st_ref_set(x_3, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_st_ref_set(x_3, x_20, x_7);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
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
static lean_object* _init_l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected internal error: ", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_53 = lean_st_ref_get(x_3, x_4);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_2, 1);
x_57 = lean_ctor_get(x_2, 2);
x_58 = lean_ctor_get(x_54, 2);
lean_inc(x_58);
x_59 = lean_box(0);
x_60 = lean_box(0);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_firstFrontendMacroScope;
x_63 = lean_box(0);
x_64 = 0;
lean_inc(x_57);
lean_inc(x_56);
x_65 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_57);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_58);
lean_ctor_set(x_65, 4, x_59);
lean_ctor_set(x_65, 5, x_62);
lean_ctor_set(x_65, 6, x_63);
lean_ctor_set(x_65, 7, x_60);
lean_ctor_set(x_65, 8, x_60);
lean_ctor_set(x_65, 9, x_60);
lean_ctor_set_uint8(x_65, sizeof(void*)*10, x_64);
x_66 = lean_ctor_get(x_54, 0);
lean_inc(x_66);
lean_dec(x_54);
x_67 = lean_st_mk_ref(x_66, x_55);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_inc(x_68);
x_70 = lean_apply_3(x_1, x_65, x_68, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_st_ref_get(x_68, x_72);
lean_dec(x_68);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
lean_ctor_set(x_73, 1, x_75);
lean_ctor_set(x_73, 0, x_71);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_73);
x_5 = x_77;
x_6 = x_76;
goto block_52;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 0);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_73);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_5 = x_81;
x_6 = x_79;
goto block_52;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_68);
x_82 = lean_ctor_get(x_70, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_70, 1);
lean_inc(x_83);
lean_dec(x_70);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_82);
x_5 = x_84;
x_6 = x_83;
goto block_52;
}
block_52:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lean_Exception_toMessageData(x_8);
x_10 = l_Lean_MessageData_toString(x_9, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
x_16 = lean_string_append(x_14, x_15);
lean_ctor_set_tag(x_5, 18);
lean_ctor_set(x_5, 0, x_16);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1;
x_20 = lean_string_append(x_19, x_17);
lean_dec(x_17);
x_21 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
x_22 = lean_string_append(x_20, x_21);
lean_ctor_set_tag(x_5, 18);
lean_ctor_set(x_5, 0, x_22);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_5);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
x_29 = l_Lean_Exception_toMessageData(x_28);
x_30 = l_Lean_MessageData_toString(x_29, x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1;
x_35 = lean_string_append(x_34, x_31);
lean_dec(x_31);
x_36 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_38, 0, x_37);
if (lean_is_scalar(x_33)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_33;
 lean_ctor_set_tag(x_39, 1);
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_42 = x_30;
} else {
 lean_dec_ref(x_30);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Elab_Frontend_setCommandState(x_46, x_2, x_3, x_6);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_runCommandElabM___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Frontend_runCommandElabM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__2;
x_3 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_53 = lean_st_ref_get(x_3, x_4);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_2, 1);
x_57 = lean_ctor_get(x_2, 2);
x_58 = lean_ctor_get(x_54, 2);
lean_inc(x_58);
x_59 = lean_box(0);
x_60 = lean_box(0);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_firstFrontendMacroScope;
x_63 = lean_box(0);
x_64 = 0;
lean_inc(x_57);
lean_inc(x_56);
x_65 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_57);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_58);
lean_ctor_set(x_65, 4, x_59);
lean_ctor_set(x_65, 5, x_62);
lean_ctor_set(x_65, 6, x_63);
lean_ctor_set(x_65, 7, x_60);
lean_ctor_set(x_65, 8, x_60);
lean_ctor_set(x_65, 9, x_60);
lean_ctor_set_uint8(x_65, sizeof(void*)*10, x_64);
x_66 = lean_ctor_get(x_54, 0);
lean_inc(x_66);
lean_dec(x_54);
x_67 = lean_st_mk_ref(x_66, x_55);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_st_ref_take(x_68, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_71, 1);
x_75 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
lean_ctor_set(x_71, 1, x_75);
x_76 = lean_st_ref_set(x_68, x_71, x_72);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_68);
x_78 = l_Lean_Elab_Command_elabCommandTopLevel(x_1, x_65, x_68, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_st_ref_get(x_68, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_st_ref_take(x_68, x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_85, 1);
lean_dec(x_88);
x_89 = l_Lean_MessageLog_append(x_74, x_83);
lean_ctor_set(x_85, 1, x_89);
x_90 = lean_st_ref_set(x_68, x_85, x_86);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_st_ref_get(x_68, x_91);
lean_dec(x_68);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ctor_get(x_92, 1);
x_96 = lean_box(0);
lean_ctor_set(x_92, 1, x_94);
lean_ctor_set(x_92, 0, x_96);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_5 = x_97;
x_6 = x_95;
goto block_52;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_92, 0);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_92);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_5 = x_102;
x_6 = x_99;
goto block_52;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_103 = lean_ctor_get(x_85, 0);
x_104 = lean_ctor_get(x_85, 2);
x_105 = lean_ctor_get(x_85, 3);
x_106 = lean_ctor_get(x_85, 4);
x_107 = lean_ctor_get(x_85, 5);
x_108 = lean_ctor_get(x_85, 6);
x_109 = lean_ctor_get(x_85, 7);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_85);
x_110 = l_Lean_MessageLog_append(x_74, x_83);
x_111 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_104);
lean_ctor_set(x_111, 3, x_105);
lean_ctor_set(x_111, 4, x_106);
lean_ctor_set(x_111, 5, x_107);
lean_ctor_set(x_111, 6, x_108);
lean_ctor_set(x_111, 7, x_109);
x_112 = lean_st_ref_set(x_68, x_111, x_86);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_st_ref_get(x_68, x_113);
lean_dec(x_68);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
x_118 = lean_box(0);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_115);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_5 = x_120;
x_6 = x_116;
goto block_52;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_74);
lean_dec(x_68);
x_121 = lean_ctor_get(x_78, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_78, 1);
lean_inc(x_122);
lean_dec(x_78);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_121);
x_5 = x_123;
x_6 = x_122;
goto block_52;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_124 = lean_ctor_get(x_71, 0);
x_125 = lean_ctor_get(x_71, 1);
x_126 = lean_ctor_get(x_71, 2);
x_127 = lean_ctor_get(x_71, 3);
x_128 = lean_ctor_get(x_71, 4);
x_129 = lean_ctor_get(x_71, 5);
x_130 = lean_ctor_get(x_71, 6);
x_131 = lean_ctor_get(x_71, 7);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_71);
x_132 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
x_133 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_127);
lean_ctor_set(x_133, 4, x_128);
lean_ctor_set(x_133, 5, x_129);
lean_ctor_set(x_133, 6, x_130);
lean_ctor_set(x_133, 7, x_131);
x_134 = lean_st_ref_set(x_68, x_133, x_72);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
lean_inc(x_68);
x_136 = l_Lean_Elab_Command_elabCommandTopLevel(x_1, x_65, x_68, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_st_ref_get(x_68, x_137);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_st_ref_take(x_68, x_140);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 4);
lean_inc(x_148);
x_149 = lean_ctor_get(x_143, 5);
lean_inc(x_149);
x_150 = lean_ctor_get(x_143, 6);
lean_inc(x_150);
x_151 = lean_ctor_get(x_143, 7);
lean_inc(x_151);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 lean_ctor_release(x_143, 5);
 lean_ctor_release(x_143, 6);
 lean_ctor_release(x_143, 7);
 x_152 = x_143;
} else {
 lean_dec_ref(x_143);
 x_152 = lean_box(0);
}
x_153 = l_Lean_MessageLog_append(x_125, x_141);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 8, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_154, 2, x_146);
lean_ctor_set(x_154, 3, x_147);
lean_ctor_set(x_154, 4, x_148);
lean_ctor_set(x_154, 5, x_149);
lean_ctor_set(x_154, 6, x_150);
lean_ctor_set(x_154, 7, x_151);
x_155 = lean_st_ref_set(x_68, x_154, x_144);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_st_ref_get(x_68, x_156);
lean_dec(x_68);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = lean_box(0);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_158);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_5 = x_163;
x_6 = x_159;
goto block_52;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_125);
lean_dec(x_68);
x_164 = lean_ctor_get(x_136, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_136, 1);
lean_inc(x_165);
lean_dec(x_136);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_164);
x_5 = x_166;
x_6 = x_165;
goto block_52;
}
}
block_52:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lean_Exception_toMessageData(x_8);
x_10 = l_Lean_MessageData_toString(x_9, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
x_16 = lean_string_append(x_14, x_15);
lean_ctor_set_tag(x_5, 18);
lean_ctor_set(x_5, 0, x_16);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_5);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1;
x_20 = lean_string_append(x_19, x_17);
lean_dec(x_17);
x_21 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
x_22 = lean_string_append(x_20, x_21);
lean_ctor_set_tag(x_5, 18);
lean_ctor_set(x_5, 0, x_22);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_5);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
x_29 = l_Lean_Exception_toMessageData(x_28);
x_30 = l_Lean_MessageData_toString(x_29, x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1;
x_35 = lean_string_append(x_34, x_31);
lean_dec(x_31);
x_36 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_38, 0, x_37);
if (lean_is_scalar(x_33)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_33;
 lean_ctor_set_tag(x_39, 1);
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_42 = x_30;
} else {
 lean_dec_ref(x_30);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
lean_dec(x_5);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Elab_Frontend_setCommandState(x_46, x_2, x_3, x_6);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
lean_dec(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_ctor_set(x_4, 2, x_9);
x_10 = lean_st_ref_set(x_1, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_st_ref_set(x_1, x_21, x_5);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_updateCmdPos___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Frontend_updateCmdPos___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Frontend_updateCmdPos(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_getParserState___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Frontend_getParserState___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Frontend_getParserState(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_getCommandState___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Frontend_getCommandState___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Frontend_getCommandState(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
lean_dec(x_9);
lean_ctor_set(x_6, 1, x_1);
x_10 = lean_st_ref_set(x_3, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_1);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_st_ref_set(x_3, x_20, x_7);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
lean_ctor_set(x_7, 1, x_1);
x_13 = lean_st_ref_set(x_3, x_6, x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 2);
x_22 = lean_ctor_get(x_7, 3);
x_23 = lean_ctor_get(x_7, 4);
x_24 = lean_ctor_get(x_7, 5);
x_25 = lean_ctor_get(x_7, 6);
x_26 = lean_ctor_get(x_7, 7);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_22);
lean_ctor_set(x_27, 4, x_23);
lean_ctor_set(x_27, 5, x_24);
lean_ctor_set(x_27, 6, x_25);
lean_ctor_set(x_27, 7, x_26);
lean_ctor_set(x_6, 0, x_27);
x_28 = lean_st_ref_set(x_3, x_6, x_8);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_33 = lean_ctor_get(x_6, 1);
x_34 = lean_ctor_get(x_6, 2);
x_35 = lean_ctor_get(x_6, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_6);
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_7, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_7, 4);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 5);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 6);
lean_inc(x_41);
x_42 = lean_ctor_get(x_7, 7);
lean_inc(x_42);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 x_43 = x_7;
} else {
 lean_dec_ref(x_7);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 8, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_1);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 3, x_38);
lean_ctor_set(x_44, 4, x_39);
lean_ctor_set(x_44, 5, x_40);
lean_ctor_set(x_44, 6, x_41);
lean_ctor_set(x_44, 7, x_42);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
x_46 = lean_st_ref_set(x_3, x_45, x_8);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Parser_parseCommand(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_processCommand___closed__1() {
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
x_4 = l_Lean_Elab_Frontend_updateCmdPos___rarg(x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_Frontend_getCommandState___rarg(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Frontend_getParserState___rarg(x_2, x_8);
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
x_16 = l_List_head_x21___rarg(x_15, x_14);
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
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommand___lambda__1___boxed), 5, 4);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_10);
lean_closure_set(x_21, 3, x_13);
x_22 = l_Lean_Elab_Frontend_processCommand___closed__1;
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
x_37 = l_Lean_Elab_Frontend_setParserState(x_27, x_1, x_2, x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Elab_Frontend_setMessages(x_28, x_1, x_2, x_38);
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
x_62 = l_Lean_Elab_Frontend_setParserState(x_27, x_1, x_2, x_61);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_Elab_Frontend_setMessages(x_28, x_1, x_2, x_63);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Frontend_processCommand___lambda__1(x_1, x_2, x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_Lean_Elab_Frontend_State_commands___default___closed__1;
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
x_8 = lean_st_mk_ref(x_7, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Frontend_processCommands(x_1, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_9, x_12);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_array_push(x_4, x_10);
x_2 = x_8;
x_4 = x_11;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Frontend_State_commands___default___closed__1;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Frontend_State_commands___default___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l_Lean_Elab_Frontend_State_commands___default___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__4(x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Language_SnapshotTask_get___rarg(x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_array_push(x_4, x_10);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_2);
x_12 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(x_2);
x_13 = l_Lean_Language_SnapshotTree_getAll(x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_13);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__1(x_15, x_16, x_13);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
x_21 = l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__2(x_15, x_16, x_13);
x_22 = lean_array_get_size(x_21);
x_23 = l_Array_filterMapM___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__3(x_21, x_19, x_22);
lean_dec(x_22);
lean_dec(x_21);
x_24 = l_Array_toPArray_x27___rarg(x_23);
lean_dec(x_23);
x_25 = lean_ctor_get(x_8, 4);
lean_inc(x_25);
x_26 = l_Lean_Language_SnapshotTask_get___rarg(x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 6);
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_29, 1);
lean_dec(x_32);
lean_ctor_set(x_29, 1, x_24);
if (x_20 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_18);
lean_dec(x_17);
x_33 = lean_ctor_get(x_8, 2);
lean_inc(x_33);
lean_dec(x_8);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
lean_ctor_set(x_27, 1, x_35);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_11);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
lean_ctor_set(x_37, 2, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_37);
return x_6;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_8, 2);
lean_inc(x_38);
lean_dec(x_8);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_nat_dec_le(x_18, x_18);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_18);
lean_dec(x_17);
x_41 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
lean_ctor_set(x_27, 1, x_41);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_38);
lean_ctor_set(x_42, 2, x_39);
lean_ctor_set(x_42, 3, x_11);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_1);
lean_ctor_set(x_43, 2, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_43);
return x_6;
}
else
{
size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_45 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
x_46 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__5(x_17, x_16, x_44, x_45);
lean_dec(x_17);
lean_ctor_set(x_27, 1, x_46);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_27);
lean_ctor_set(x_47, 1, x_38);
lean_ctor_set(x_47, 2, x_39);
lean_ctor_set(x_47, 3, x_11);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_1);
lean_ctor_set(x_48, 2, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_48);
return x_6;
}
}
}
else
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get_uint8(x_29, sizeof(void*)*2);
x_50 = lean_ctor_get(x_29, 0);
lean_inc(x_50);
lean_dec(x_29);
x_51 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_24);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_49);
if (x_20 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_18);
lean_dec(x_17);
x_52 = lean_ctor_get(x_8, 2);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
lean_ctor_set(x_27, 6, x_51);
lean_ctor_set(x_27, 1, x_54);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_27);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_11);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_1);
lean_ctor_set(x_56, 2, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_56);
return x_6;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_8, 2);
lean_inc(x_57);
lean_dec(x_8);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_nat_dec_le(x_18, x_18);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_18);
lean_dec(x_17);
x_60 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
lean_ctor_set(x_27, 6, x_51);
lean_ctor_set(x_27, 1, x_60);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_27);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_11);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_1);
lean_ctor_set(x_62, 2, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_62);
return x_6;
}
else
{
size_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_64 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
x_65 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__5(x_17, x_16, x_63, x_64);
lean_dec(x_17);
lean_ctor_set(x_27, 6, x_51);
lean_ctor_set(x_27, 1, x_65);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_27);
lean_ctor_set(x_66, 1, x_57);
lean_ctor_set(x_66, 2, x_58);
lean_ctor_set(x_66, 3, x_11);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_1);
lean_ctor_set(x_67, 2, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_67);
return x_6;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_27, 6);
x_69 = lean_ctor_get(x_27, 0);
x_70 = lean_ctor_get(x_27, 2);
x_71 = lean_ctor_get(x_27, 3);
x_72 = lean_ctor_get(x_27, 4);
x_73 = lean_ctor_get(x_27, 5);
x_74 = lean_ctor_get(x_27, 7);
lean_inc(x_74);
lean_inc(x_68);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_27);
x_75 = lean_ctor_get_uint8(x_68, sizeof(void*)*2);
x_76 = lean_ctor_get(x_68, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_77 = x_68;
} else {
 lean_dec_ref(x_68);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 1);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_24);
lean_ctor_set_uint8(x_78, sizeof(void*)*2, x_75);
if (x_20 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_18);
lean_dec(x_17);
x_79 = lean_ctor_get(x_8, 2);
lean_inc(x_79);
lean_dec(x_8);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
x_82 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_82, 0, x_69);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_70);
lean_ctor_set(x_82, 3, x_71);
lean_ctor_set(x_82, 4, x_72);
lean_ctor_set(x_82, 5, x_73);
lean_ctor_set(x_82, 6, x_78);
lean_ctor_set(x_82, 7, x_74);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_11);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_1);
lean_ctor_set(x_84, 2, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_84);
return x_6;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_8, 2);
lean_inc(x_85);
lean_dec(x_8);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_nat_dec_le(x_18, x_18);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_18);
lean_dec(x_17);
x_88 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
x_89 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_89, 0, x_69);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_70);
lean_ctor_set(x_89, 3, x_71);
lean_ctor_set(x_89, 4, x_72);
lean_ctor_set(x_89, 5, x_73);
lean_ctor_set(x_89, 6, x_78);
lean_ctor_set(x_89, 7, x_74);
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set(x_90, 2, x_86);
lean_ctor_set(x_90, 3, x_11);
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_1);
lean_ctor_set(x_91, 2, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_91);
return x_6;
}
else
{
size_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_93 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
x_94 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__5(x_17, x_16, x_92, x_93);
lean_dec(x_17);
x_95 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_95, 0, x_69);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_70);
lean_ctor_set(x_95, 3, x_71);
lean_ctor_set(x_95, 4, x_72);
lean_ctor_set(x_95, 5, x_73);
lean_ctor_set(x_95, 6, x_78);
lean_ctor_set(x_95, 7, x_74);
x_96 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_85);
lean_ctor_set(x_96, 2, x_86);
lean_ctor_set(x_96, 3, x_11);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_1);
lean_ctor_set(x_97, 2, x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_97);
return x_6;
}
}
}
}
else
{
lean_object* x_98; 
lean_free_object(x_6);
lean_dec(x_8);
x_98 = lean_ctor_get(x_9, 0);
lean_inc(x_98);
lean_dec(x_9);
x_3 = x_98;
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_6, 0);
x_101 = lean_ctor_get(x_6, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_6);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
x_103 = lean_array_push(x_4, x_102);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; size_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_inc(x_2);
x_104 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(x_2);
x_105 = l_Lean_Language_SnapshotTree_getAll(x_104);
x_106 = lean_array_get_size(x_105);
x_107 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_108 = 0;
lean_inc(x_105);
x_109 = l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__1(x_107, x_108, x_105);
x_110 = lean_array_get_size(x_109);
x_111 = lean_unsigned_to_nat(0u);
x_112 = lean_nat_dec_lt(x_111, x_110);
x_113 = l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__2(x_107, x_108, x_105);
x_114 = lean_array_get_size(x_113);
x_115 = l_Array_filterMapM___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__3(x_113, x_111, x_114);
lean_dec(x_114);
lean_dec(x_113);
x_116 = l_Array_toPArray_x27___rarg(x_115);
lean_dec(x_115);
x_117 = lean_ctor_get(x_100, 4);
lean_inc(x_117);
x_118 = l_Lean_Language_SnapshotTask_get___rarg(x_117);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_ctor_get(x_119, 6);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 5);
lean_inc(x_125);
x_126 = lean_ctor_get(x_119, 7);
lean_inc(x_126);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 lean_ctor_release(x_119, 5);
 lean_ctor_release(x_119, 6);
 lean_ctor_release(x_119, 7);
 x_127 = x_119;
} else {
 lean_dec_ref(x_119);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get_uint8(x_120, sizeof(void*)*2);
x_129 = lean_ctor_get(x_120, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_130 = x_120;
} else {
 lean_dec_ref(x_120);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 2, 1);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_116);
lean_ctor_set_uint8(x_131, sizeof(void*)*2, x_128);
if (x_112 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_110);
lean_dec(x_109);
x_132 = lean_ctor_get(x_100, 2);
lean_inc(x_132);
lean_dec(x_100);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
if (lean_is_scalar(x_127)) {
 x_135 = lean_alloc_ctor(0, 8, 0);
} else {
 x_135 = x_127;
}
lean_ctor_set(x_135, 0, x_121);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_122);
lean_ctor_set(x_135, 3, x_123);
lean_ctor_set(x_135, 4, x_124);
lean_ctor_set(x_135, 5, x_125);
lean_ctor_set(x_135, 6, x_131);
lean_ctor_set(x_135, 7, x_126);
x_136 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_132);
lean_ctor_set(x_136, 2, x_133);
lean_ctor_set(x_136, 3, x_103);
x_137 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_1);
lean_ctor_set(x_137, 2, x_2);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_5);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_ctor_get(x_100, 2);
lean_inc(x_139);
lean_dec(x_100);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_nat_dec_le(x_110, x_110);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_110);
lean_dec(x_109);
x_142 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
if (lean_is_scalar(x_127)) {
 x_143 = lean_alloc_ctor(0, 8, 0);
} else {
 x_143 = x_127;
}
lean_ctor_set(x_143, 0, x_121);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_122);
lean_ctor_set(x_143, 3, x_123);
lean_ctor_set(x_143, 4, x_124);
lean_ctor_set(x_143, 5, x_125);
lean_ctor_set(x_143, 6, x_131);
lean_ctor_set(x_143, 7, x_126);
x_144 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_139);
lean_ctor_set(x_144, 2, x_140);
lean_ctor_set(x_144, 3, x_103);
x_145 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_1);
lean_ctor_set(x_145, 2, x_2);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_5);
return x_146;
}
else
{
size_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_147 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_148 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
x_149 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__5(x_109, x_108, x_147, x_148);
lean_dec(x_109);
if (lean_is_scalar(x_127)) {
 x_150 = lean_alloc_ctor(0, 8, 0);
} else {
 x_150 = x_127;
}
lean_ctor_set(x_150, 0, x_121);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_150, 2, x_122);
lean_ctor_set(x_150, 3, x_123);
lean_ctor_set(x_150, 4, x_124);
lean_ctor_set(x_150, 5, x_125);
lean_ctor_set(x_150, 6, x_131);
lean_ctor_set(x_150, 7, x_126);
x_151 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_139);
lean_ctor_set(x_151, 2, x_140);
lean_ctor_set(x_151, 3, x_103);
x_152 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_1);
lean_ctor_set(x_152, 2, x_2);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_5);
return x_153;
}
}
}
else
{
lean_object* x_154; 
lean_dec(x_100);
x_154 = lean_ctor_get(x_101, 0);
lean_inc(x_154);
lean_dec(x_101);
x_3 = x_154;
x_4 = x_103;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_IO_processCommandsIncrementally_go___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
lean_inc(x_1);
x_7 = l_Lean_Language_Lean_processCommands(x_1, x_2, x_3, x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l_Lean_Language_SnapshotTask_get___rarg(x_8);
x_11 = l_Lean_Elab_Frontend_State_commands___default___closed__1;
x_12 = l_Lean_Elab_IO_processCommandsIncrementally_go(x_1, x_10, x_8, x_11, x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_4, 0, x_21);
lean_inc(x_1);
x_22 = l_Lean_Language_Lean_processCommands(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_23);
x_25 = l_Lean_Language_SnapshotTask_get___rarg(x_23);
x_26 = l_Lean_Elab_Frontend_State_commands___default___closed__1;
x_27 = l_Lean_Elab_IO_processCommandsIncrementally_go(x_1, x_25, x_23, x_26, x_24);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
lean_dec(x_4);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_inc(x_1);
x_37 = l_Lean_Language_Lean_processCommands(x_1, x_2, x_3, x_36, x_5);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_38);
x_40 = l_Lean_Language_SnapshotTask_get___rarg(x_38);
x_41 = l_Lean_Elab_Frontend_State_commands___default___closed__1;
x_42 = l_Lean_Elab_IO_processCommandsIncrementally_go(x_1, x_40, x_38, x_41, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_process___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_process___closed__2() {
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
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4;
x_7 = l_Lean_Elab_Command_mkState(x_2, x_6, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Elab_process___closed__2;
x_9 = 1;
x_10 = l_Lean_Parser_mkInputContext(x_1, x_8, x_9);
x_11 = l_Lean_Elab_process___closed__1;
x_12 = l_Lean_Elab_IO_processCommands(x_10, x_11, x_7, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
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
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = 1;
x_31 = l_Lean_Parser_mkInputContext(x_1, x_29, x_30);
x_32 = l_Lean_Elab_process___closed__1;
x_33 = l_Lean_Elab_IO_processCommands(x_31, x_32, x_7, x_5);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_33, 0, x_40);
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_33);
if (x_46 == 0)
{
return x_33;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_33);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_MessageLog_hasErrors(x_1);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_output;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Import", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_runFrontend___lambda__2___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("importing", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_runFrontend___lambda__2___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_runFrontend___lambda__2___closed__5;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, double x_4, double x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_runFrontend___lambda__2___closed__1;
x_11 = l_Lean_Option_get_x3f___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1(x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = l_Lean_Elab_runFrontend___lambda__1(x_1, x_2, x_12, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Elab_runFrontend___lambda__2___closed__3;
x_16 = 1;
x_17 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
x_18 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_float(x_18, sizeof(void*)*2, x_4);
lean_ctor_set_float(x_18, sizeof(void*)*2 + 8, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 16, x_16);
x_19 = l_Lean_Elab_runFrontend___lambda__2___closed__6;
x_20 = l_Lean_Elab_Frontend_State_commands___default___closed__1;
x_21 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_runFrontend___lambda__2___closed__7;
x_25 = lean_array_push(x_24, x_23);
x_26 = l_Array_toPArray_x27___rarg(x_25);
lean_dec(x_25);
x_27 = l_Lean_PersistentArray_append___rarg(x_26, x_6);
x_28 = l_Lean_Name_toString(x_7, x_16);
x_29 = l_Lean_Firefox_Profile_export(x_28, x_4, x_27, x_3, x_9);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Util_Profiler_0__Lean_Firefox_toJsonProfile____x40_Lean_Util_Profiler___hyg_3604_(x_30);
x_33 = l_Lean_Json_compress(x_32);
x_34 = l_IO_FS_writeFile(x_14, x_33, x_31);
lean_dec(x_33);
lean_dec(x_14);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_runFrontend___lambda__1(x_1, x_2, x_35, x_36);
lean_dec(x_35);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_14);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, double x_5, double x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l_Lean_Elab_IO_processCommands(x_1, x_2, x_9, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 7);
lean_inc(x_19);
lean_dec(x_14);
lean_inc(x_3);
x_20 = l_Lean_Language_reportMessages(x_17, x_3, x_4, x_15);
if (lean_obj_tag(x_20) == 0)
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_runFrontend___lambda__2(x_17, x_16, x_3, x_5, x_6, x_19, x_7, x_22, x_21);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_17);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l_Lean_PersistentArray_toArray___rarg(x_26);
lean_dec(x_26);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
lean_dec(x_1);
x_29 = 0;
x_30 = l_Lean_Server_findModuleRefs(x_28, x_27, x_29, x_29);
lean_dec(x_27);
x_31 = l_Lean_Server_ModuleRefs_toLspModuleRefs(x_30, x_24);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(3u);
lean_inc(x_7);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
lean_ctor_set(x_35, 2, x_32);
x_36 = l___private_Lean_Server_References_0__Lean_Server_toJsonIlean____x40_Lean_Server_References___hyg_1472_(x_35);
x_37 = l_Lean_Json_compress(x_36);
x_38 = l_IO_FS_writeFile(x_25, x_37, x_33);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_runFrontend___lambda__2(x_17, x_16, x_3, x_5, x_6, x_19, x_7, x_39, x_40);
lean_dec(x_39);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_17);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_12);
if (x_50 == 0)
{
return x_12;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_12, 0);
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_12);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
static double _init_l_Lean_Elab_runFrontend___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_run_frontend(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint32_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; double x_14; double x_15; double x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_io_mono_nanos_now(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Float_ofScientific(x_10, x_12, x_13);
lean_dec(x_10);
x_15 = l_Lean_Elab_runFrontend___closed__1;
x_16 = lean_float_div(x_14, x_15);
x_17 = 1;
x_18 = l_Lean_Parser_mkInputContext(x_1, x_3, x_17);
lean_inc(x_18);
x_19 = l_Lean_Parser_parseHeader(x_18, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
lean_inc(x_18);
lean_inc(x_2);
x_26 = l_Lean_Elab_processHeader(x_23, x_2, x_25, x_18, x_5, x_17, x_22);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; double x_36; double x_37; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_4);
x_31 = lean_environment_set_main_module(x_29, x_4);
lean_inc(x_2);
lean_inc(x_30);
lean_inc(x_31);
x_32 = l_Lean_Elab_Command_mkState(x_31, x_30, x_2);
x_33 = lean_io_mono_nanos_now(x_28);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Float_ofScientific(x_34, x_12, x_13);
lean_dec(x_34);
x_37 = lean_float_div(x_36, x_15);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_31);
lean_dec(x_30);
x_38 = lean_box(0);
x_39 = l_Lean_Elab_runFrontend___lambda__3(x_18, x_24, x_2, x_7, x_16, x_37, x_4, x_6, x_32, x_38, x_35);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_32, 6);
x_42 = lean_ctor_get(x_32, 4);
lean_dec(x_42);
x_43 = lean_ctor_get(x_32, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_32, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_32, 0);
lean_dec(x_45);
x_46 = l_Lean_Elab_runFrontend___closed__3;
x_47 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_2, x_46);
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_17);
x_49 = l_Lean_Elab_runFrontend___closed__2;
lean_ctor_set(x_32, 4, x_47);
lean_ctor_set(x_32, 3, x_49);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 0, x_31);
x_50 = lean_box(0);
x_51 = l_Lean_Elab_runFrontend___lambda__3(x_18, x_24, x_2, x_7, x_16, x_37, x_4, x_6, x_32, x_50, x_35);
lean_dec(x_6);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_41, 0);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_41);
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_17);
x_55 = l_Lean_Elab_runFrontend___closed__2;
lean_ctor_set(x_32, 6, x_54);
lean_ctor_set(x_32, 4, x_47);
lean_ctor_set(x_32, 3, x_55);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 0, x_31);
x_56 = lean_box(0);
x_57 = l_Lean_Elab_runFrontend___lambda__3(x_18, x_24, x_2, x_7, x_16, x_37, x_4, x_6, x_32, x_56, x_35);
lean_dec(x_6);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_58 = lean_ctor_get(x_32, 2);
x_59 = lean_ctor_get(x_32, 5);
x_60 = lean_ctor_get(x_32, 6);
x_61 = lean_ctor_get(x_32, 7);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_32);
x_62 = l_Lean_Elab_runFrontend___closed__3;
x_63 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_2, x_62);
x_64 = lean_ctor_get(x_60, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_66 = x_60;
} else {
 lean_dec_ref(x_60);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 1);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_17);
x_68 = l_Lean_Elab_runFrontend___closed__2;
x_69 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_69, 0, x_31);
lean_ctor_set(x_69, 1, x_30);
lean_ctor_set(x_69, 2, x_58);
lean_ctor_set(x_69, 3, x_68);
lean_ctor_set(x_69, 4, x_63);
lean_ctor_set(x_69, 5, x_59);
lean_ctor_set(x_69, 6, x_67);
lean_ctor_set(x_69, 7, x_61);
x_70 = lean_box(0);
x_71 = l_Lean_Elab_runFrontend___lambda__3(x_18, x_24, x_2, x_7, x_16, x_37, x_4, x_6, x_69, x_70, x_35);
lean_dec(x_6);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_26);
if (x_72 == 0)
{
return x_26;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_26, 0);
x_74 = lean_ctor_get(x_26, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_26);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_19);
if (x_76 == 0)
{
return x_19;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_19, 0);
x_78 = lean_ctor_get(x_19, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_19);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_runFrontend___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
double x_10; double x_11; lean_object* x_12; 
x_10 = lean_unbox_float(x_4);
lean_dec(x_4);
x_11 = lean_unbox_float(x_5);
lean_dec(x_5);
x_12 = l_Lean_Elab_runFrontend___lambda__2(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; double x_13; double x_14; lean_object* x_15; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox_float(x_5);
lean_dec(x_5);
x_14 = lean_unbox_float(x_6);
lean_dec(x_6);
x_15 = l_Lean_Elab_runFrontend___lambda__3(x_1, x_2, x_3, x_12, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint32_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = lean_run_frontend(x_1, x_2, x_3, x_4, x_9, x_6, x_10, x_8);
return x_11;
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
l_Lean_Elab_Frontend_State_commands___default___closed__1 = _init_l_Lean_Elab_Frontend_State_commands___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Frontend_State_commands___default___closed__1);
l_Lean_Elab_Frontend_State_commands___default = _init_l_Lean_Elab_Frontend_State_commands___default();
lean_mark_persistent(l_Lean_Elab_Frontend_State_commands___default);
l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1 = _init_l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1);
l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2 = _init_l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2);
l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1 = _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1();
lean_mark_persistent(l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__1);
l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__2 = _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__2();
lean_mark_persistent(l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__2);
l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3 = _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3();
lean_mark_persistent(l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__3);
l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4 = _init_l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4();
lean_mark_persistent(l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__4);
l_Lean_Elab_Frontend_processCommand___closed__1 = _init_l_Lean_Elab_Frontend_processCommand___closed__1();
lean_mark_persistent(l_Lean_Elab_Frontend_processCommand___closed__1);
l_Lean_Elab_process___closed__1 = _init_l_Lean_Elab_process___closed__1();
lean_mark_persistent(l_Lean_Elab_process___closed__1);
l_Lean_Elab_process___closed__2 = _init_l_Lean_Elab_process___closed__2();
lean_mark_persistent(l_Lean_Elab_process___closed__2);
l_Lean_Elab_runFrontend___lambda__2___closed__1 = _init_l_Lean_Elab_runFrontend___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_runFrontend___lambda__2___closed__1);
l_Lean_Elab_runFrontend___lambda__2___closed__2 = _init_l_Lean_Elab_runFrontend___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_runFrontend___lambda__2___closed__2);
l_Lean_Elab_runFrontend___lambda__2___closed__3 = _init_l_Lean_Elab_runFrontend___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_runFrontend___lambda__2___closed__3);
l_Lean_Elab_runFrontend___lambda__2___closed__4 = _init_l_Lean_Elab_runFrontend___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_runFrontend___lambda__2___closed__4);
l_Lean_Elab_runFrontend___lambda__2___closed__5 = _init_l_Lean_Elab_runFrontend___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_runFrontend___lambda__2___closed__5);
l_Lean_Elab_runFrontend___lambda__2___closed__6 = _init_l_Lean_Elab_runFrontend___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_runFrontend___lambda__2___closed__6);
l_Lean_Elab_runFrontend___lambda__2___closed__7 = _init_l_Lean_Elab_runFrontend___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_runFrontend___lambda__2___closed__7);
l_Lean_Elab_runFrontend___closed__1 = _init_l_Lean_Elab_runFrontend___closed__1();
l_Lean_Elab_runFrontend___closed__2 = _init_l_Lean_Elab_runFrontend___closed__2();
lean_mark_persistent(l_Lean_Elab_runFrontend___closed__2);
l_Lean_Elab_runFrontend___closed__3 = _init_l_Lean_Elab_runFrontend___closed__3();
lean_mark_persistent(l_Lean_Elab_runFrontend___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
