// Lean compiler output
// Module: Lean.Elab.Frontend
// Imports: Init Lean.Elab.Import Lean.Elab.Command Lean.Util.Profile Lean.Server.References
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
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__2;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_Server_ModuleRefs_instCoeModuleRefsModuleRefs___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_process___closed__2;
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_State_commands___default;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__21;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_run_frontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_process___closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__6;
lean_object* lean_environment_set_main_module(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMap_ofList___at_Lean_Server_ModuleRefs_instCoeModuleRefsModuleRefs___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__17;
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__8;
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__4;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__22;
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_runFrontend___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__3;
static lean_object* l_Lean_Elab_process___closed__4;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__18;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__15;
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMap_toList___at_Lean_Server_ModuleRefs_instCoeModuleRefsModuleRefs___spec__1(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_IO_print___at_IO_println___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_runFrontend___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_getPrintMessageEndPos___boxed(lean_object*);
static lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__20;
static lean_object* l_Lean_Elab_Frontend_processCommand___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_FileMap_ofString(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Frontend_processCommand___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___rarg(lean_object*);
static lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
lean_object* l___private_Lean_Server_References_0__Lean_Server_toJsonIlean____x40_Lean_Server_References___hyg_1289_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Elab_Frontend_processCommand___spec__1(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__12;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__7;
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Elab_Frontend_processCommand___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_findModuleRefs(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Frontend_State_commands___default___closed__1;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__11;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___boxed(lean_object*);
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__19;
uint8_t l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
static lean_object* l_Lean_Elab_process___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Parser_isEOI(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___closed__1;
static lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_getPrintMessageEndPos(lean_object*);
static lean_object* l_Lean_Elab_process___closed__5;
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Elab_Frontend_processCommand___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_runFrontend___closed__2;
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___boxed(lean_object*);
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
x_1 = lean_mk_string_from_bytes("unexpected internal error: ", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_38 = lean_st_ref_get(x_3, x_4);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
x_44 = lean_box(0);
x_45 = lean_box(0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_firstFrontendMacroScope;
x_48 = lean_box(0);
lean_inc(x_42);
lean_inc(x_41);
x_49 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_43);
lean_ctor_set(x_49, 4, x_44);
lean_ctor_set(x_49, 5, x_47);
lean_ctor_set(x_49, 6, x_48);
lean_ctor_set(x_49, 7, x_45);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
lean_dec(x_39);
x_51 = lean_st_mk_ref(x_50, x_40);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_52);
x_54 = lean_apply_3(x_1, x_49, x_52, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_get(x_52, x_56);
lean_dec(x_52);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_5 = x_61;
x_6 = x_59;
goto block_37;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_52);
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_dec(x_54);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_62);
x_5 = x_64;
x_6 = x_63;
goto block_37;
}
block_37:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Exception_toMessageData(x_7);
x_9 = l_Lean_MessageData_toString(x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1;
x_20 = lean_string_append(x_19, x_17);
lean_dec(x_17);
x_21 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Frontend_setCommandState(x_31, x_2, x_3, x_6);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_38 = lean_st_ref_get(x_3, x_4);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
x_44 = lean_box(0);
x_45 = lean_box(0);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_firstFrontendMacroScope;
x_48 = lean_box(0);
lean_inc(x_42);
lean_inc(x_41);
x_49 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_43);
lean_ctor_set(x_49, 4, x_44);
lean_ctor_set(x_49, 5, x_47);
lean_ctor_set(x_49, 6, x_48);
lean_ctor_set(x_49, 7, x_45);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
lean_dec(x_39);
x_51 = lean_st_mk_ref(x_50, x_40);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_52);
x_54 = l_Lean_Elab_Command_elabCommandTopLevel(x_1, x_49, x_52, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_get(x_52, x_56);
lean_dec(x_52);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_5 = x_61;
x_6 = x_59;
goto block_37;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_52);
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_dec(x_54);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_62);
x_5 = x_64;
x_6 = x_63;
goto block_37;
}
block_37:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Exception_toMessageData(x_7);
x_9 = l_Lean_MessageData_toString(x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__1;
x_20 = lean_string_append(x_19, x_17);
lean_dec(x_17);
x_21 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Frontend_setCommandState(x_31, x_2, x_3, x_6);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 2);
x_22 = lean_ctor_get(x_7, 3);
x_23 = lean_ctor_get(x_7, 4);
x_24 = lean_ctor_get(x_7, 5);
x_25 = lean_ctor_get(x_7, 6);
x_26 = lean_ctor_get(x_7, 7);
x_27 = lean_ctor_get(x_7, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_1);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set(x_28, 4, x_23);
lean_ctor_set(x_28, 5, x_24);
lean_ctor_set(x_28, 6, x_25);
lean_ctor_set(x_28, 7, x_26);
lean_ctor_set(x_28, 8, x_27);
lean_ctor_set(x_6, 0, x_28);
x_29 = lean_st_ref_set(x_3, x_6, x_8);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_34 = lean_ctor_get(x_6, 1);
x_35 = lean_ctor_get(x_6, 2);
x_36 = lean_ctor_get(x_6, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_6);
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_7, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 5);
lean_inc(x_41);
x_42 = lean_ctor_get(x_7, 6);
lean_inc(x_42);
x_43 = lean_ctor_get(x_7, 7);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 8);
lean_inc(x_44);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 x_45 = x_7;
} else {
 lean_dec_ref(x_7);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 9, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_1);
lean_ctor_set(x_46, 2, x_38);
lean_ctor_set(x_46, 3, x_39);
lean_ctor_set(x_46, 4, x_40);
lean_ctor_set(x_46, 5, x_41);
lean_ctor_set(x_46, 6, x_42);
lean_ctor_set(x_46, 7, x_43);
lean_ctor_set(x_46, 8, x_44);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_34);
lean_ctor_set(x_47, 2, x_35);
lean_ctor_set(x_47, 3, x_36);
x_48 = lean_st_ref_set(x_3, x_47, x_8);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_box(0);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
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
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Elab_Frontend_processCommand___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_3, x_4, x_5);
x_8 = l_Lean_profileitIOUnsafe___rarg(x_1, x_2, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Elab_Frontend_processCommand___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_profileitM___at_Lean_Elab_Frontend_processCommand___spec__1___rarg___boxed), 6, 0);
return x_2;
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
x_1 = lean_mk_string_from_bytes("parsing", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Frontend_processCommand___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elaboration", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
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
x_23 = lean_profileit(x_22, x_17, x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_st_ref_take(x_2, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_32 = lean_ctor_get(x_29, 3);
lean_inc(x_25);
x_33 = lean_array_push(x_32, x_25);
lean_ctor_set(x_29, 3, x_33);
x_34 = lean_st_ref_set(x_2, x_29, x_30);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Elab_Frontend_setParserState(x_26, x_1, x_2, x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Elab_Frontend_setMessages(x_27, x_1, x_2, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_38, 1);
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
lean_inc(x_25);
x_42 = l_Lean_Parser_isEOI(x_25);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_38);
lean_inc(x_25);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed), 4, 1);
lean_closure_set(x_43, 0, x_25);
x_44 = l_Lean_Elab_Frontend_processCommand___closed__2;
x_45 = l_Lean_profileitM___at_Lean_Elab_Frontend_processCommand___spec__1___rarg(x_44, x_17, x_43, x_1, x_2, x_40);
lean_dec(x_17);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = l_Lean_Parser_isTerminalCommand(x_25);
x_49 = lean_box(x_48);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = l_Lean_Parser_isTerminalCommand(x_25);
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_25);
x_54 = !lean_is_exclusive(x_45);
if (x_54 == 0)
{
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_45, 0);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_45);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; lean_object* x_59; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_58 = 1;
x_59 = lean_box(x_58);
lean_ctor_set(x_38, 0, x_59);
return x_38;
}
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_dec(x_38);
lean_inc(x_25);
x_61 = l_Lean_Parser_isEOI(x_25);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_inc(x_25);
x_62 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed), 4, 1);
lean_closure_set(x_62, 0, x_25);
x_63 = l_Lean_Elab_Frontend_processCommand___closed__2;
x_64 = l_Lean_profileitM___at_Lean_Elab_Frontend_processCommand___spec__1___rarg(x_63, x_17, x_62, x_1, x_2, x_60);
lean_dec(x_17);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = l_Lean_Parser_isTerminalCommand(x_25);
x_68 = lean_box(x_67);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_25);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_74 = 1;
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_60);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_77 = lean_ctor_get(x_29, 0);
x_78 = lean_ctor_get(x_29, 1);
x_79 = lean_ctor_get(x_29, 2);
x_80 = lean_ctor_get(x_29, 3);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_29);
lean_inc(x_25);
x_81 = lean_array_push(x_80, x_25);
x_82 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_81);
x_83 = lean_st_ref_set(x_2, x_82, x_30);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_Lean_Elab_Frontend_setParserState(x_26, x_1, x_2, x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_Elab_Frontend_setMessages(x_27, x_1, x_2, x_86);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
lean_inc(x_25);
x_90 = l_Lean_Parser_isEOI(x_25);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_89);
lean_inc(x_25);
x_91 = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed), 4, 1);
lean_closure_set(x_91, 0, x_25);
x_92 = l_Lean_Elab_Frontend_processCommand___closed__2;
x_93 = l_Lean_profileitM___at_Lean_Elab_Frontend_processCommand___spec__1___rarg(x_92, x_17, x_91, x_1, x_2, x_88);
lean_dec(x_17);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
x_96 = l_Lean_Parser_isTerminalCommand(x_25);
x_97 = lean_box(x_96);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_95;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_25);
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_101 = x_93;
} else {
 lean_dec_ref(x_93);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
uint8_t x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_103 = 1;
x_104 = lean_box(x_103);
if (lean_is_scalar(x_89)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_89;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_88);
return x_105;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Elab_Frontend_processCommand___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_profileitM___at_Lean_Elab_Frontend_processCommand___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
lean_inc(x_9);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_process___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_process___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_process___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_process___closed__3;
x_3 = l_Lean_Elab_process___closed__2;
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
static lean_object* _init_l_Lean_Elab_process___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<input>", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Elab_process___closed__4;
x_7 = l_Lean_Elab_Command_mkState(x_2, x_6, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Elab_process___closed__5;
x_9 = l_Lean_Parser_mkInputContext(x_1, x_8);
x_10 = l_Lean_Elab_process___closed__1;
x_11 = l_Lean_Elab_IO_processCommands(x_9, x_10, x_7, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
lean_dec(x_4);
x_29 = l_Lean_Parser_mkInputContext(x_1, x_28);
x_30 = l_Lean_Elab_process___closed__1;
x_31 = l_Lean_Elab_IO_processCommands(x_29, x_30, x_7, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_31, 0, x_38);
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("printMessageEndPos", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__4;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__6;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__8;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__10;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__11;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Frontend", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__12;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__14;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__16;
x_2 = lean_unsigned_to_nat(1031u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__18() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("print end position of each message in addition to start position", 64);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__17;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__18;
x_3 = l_Lean_Elab_Frontend_runCommandElabM___rarg___closed__2;
x_4 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__19;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("info", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__5;
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__21;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__2;
x_3 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__20;
x_4 = lean_register_option(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__22;
x_7 = 0;
x_8 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__17;
x_9 = l_Lean_registerTraceClass(x_6, x_7, x_8, x_5);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_getPrintMessageEndPos(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__2;
x_3 = 0;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getPrintMessageEndPos___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_getPrintMessageEndPos(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_runFrontend___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_Elab_getPrintMessageEndPos(x_1);
x_9 = l_Lean_Message_toString(x_6, x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_IO_print___at_IO_println___spec__1(x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_2 = x_7;
x_3 = x_14;
x_4 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_IO_processCommands(x_1, x_2, x_7, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 7);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_15);
x_17 = l_Lean_MessageLog_toList(x_15);
x_18 = lean_box(0);
x_19 = l_List_forIn_loop___at_Lean_Elab_runFrontend___spec__1(x_3, x_17, x_18, x_13);
lean_dec(x_3);
if (lean_obj_tag(x_19) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_runFrontend___lambda__1(x_15, x_14, x_18, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
lean_dec(x_4);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = l_Lean_PersistentArray_toArray___rarg(x_24);
x_26 = l_Lean_FileMap_ofString(x_5);
x_27 = 0;
x_28 = l_Lean_Server_findModuleRefs(x_26, x_25, x_27, x_27);
x_29 = l_Lean_HashMap_toList___at_Lean_Server_ModuleRefs_instCoeModuleRefsModuleRefs___spec__1(x_28);
x_30 = lean_box(0);
x_31 = l_List_mapTR_loop___at_Lean_Server_ModuleRefs_instCoeModuleRefsModuleRefs___spec__4(x_29, x_30);
x_32 = l_Lean_HashMap_ofList___at_Lean_Server_ModuleRefs_instCoeModuleRefsModuleRefs___spec__5(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
lean_ctor_set(x_34, 2, x_32);
x_35 = l___private_Lean_Server_References_0__Lean_Server_toJsonIlean____x40_Lean_Server_References___hyg_1289_(x_34);
x_36 = l_Lean_Json_compress(x_35);
x_37 = l_IO_FS_writeFile(x_23, x_36, x_22);
lean_dec(x_36);
lean_dec(x_23);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Elab_runFrontend___lambda__1(x_15, x_14, x_38, x_39);
lean_dec(x_38);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_15);
lean_dec(x_14);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_19);
if (x_45 == 0)
{
return x_19;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_19, 0);
x_47 = lean_ctor_get(x_19, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_19);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_10);
if (x_49 == 0)
{
return x_10;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_10, 0);
x_51 = lean_ctor_get(x_10, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_10);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_runFrontend___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_run_frontend(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint32_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = l_Lean_Parser_mkInputContext(x_1, x_3);
lean_inc(x_8);
x_9 = l_Lean_Parser_parseHeader(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_2);
x_16 = l_Lean_Elab_processHeader(x_13, x_2, x_15, x_8, x_5, x_12);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_4);
x_21 = lean_environment_set_main_module(x_19, x_4);
lean_inc(x_2);
lean_inc(x_20);
lean_inc(x_21);
x_22 = l_Lean_Elab_Command_mkState(x_21, x_20, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_runFrontend___lambda__2(x_8, x_14, x_2, x_6, x_1, x_4, x_22, x_23, x_18);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_22, 7);
x_27 = lean_ctor_get(x_22, 5);
lean_dec(x_27);
x_28 = lean_ctor_get(x_22, 4);
lean_dec(x_28);
x_29 = lean_ctor_get(x_22, 3);
lean_dec(x_29);
x_30 = lean_ctor_get(x_22, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_22, 0);
lean_dec(x_31);
x_32 = l_Lean_Elab_runFrontend___closed__2;
x_33 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_2, x_32);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = 1;
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_35);
x_36 = l_Lean_Elab_runFrontend___closed__1;
x_37 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_22, 5, x_37);
lean_ctor_set(x_22, 4, x_33);
lean_ctor_set(x_22, 3, x_36);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 0, x_21);
x_38 = lean_box(0);
x_39 = l_Lean_Elab_runFrontend___lambda__2(x_8, x_14, x_2, x_6, x_1, x_4, x_22, x_38, x_18);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = 1;
x_43 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_42);
x_44 = l_Lean_Elab_runFrontend___closed__1;
x_45 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_22, 7, x_43);
lean_ctor_set(x_22, 5, x_45);
lean_ctor_set(x_22, 4, x_33);
lean_ctor_set(x_22, 3, x_44);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 0, x_21);
x_46 = lean_box(0);
x_47 = l_Lean_Elab_runFrontend___lambda__2(x_8, x_14, x_2, x_6, x_1, x_4, x_22, x_46, x_18);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_48 = lean_ctor_get(x_22, 2);
x_49 = lean_ctor_get(x_22, 6);
x_50 = lean_ctor_get(x_22, 7);
x_51 = lean_ctor_get(x_22, 8);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_22);
x_52 = l_Lean_Elab_runFrontend___closed__2;
x_53 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_2, x_52);
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_56 = x_50;
} else {
 lean_dec_ref(x_50);
 x_56 = lean_box(0);
}
x_57 = 1;
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 1);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_57);
x_59 = l_Lean_Elab_runFrontend___closed__1;
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_21);
lean_ctor_set(x_61, 1, x_20);
lean_ctor_set(x_61, 2, x_48);
lean_ctor_set(x_61, 3, x_59);
lean_ctor_set(x_61, 4, x_53);
lean_ctor_set(x_61, 5, x_60);
lean_ctor_set(x_61, 6, x_49);
lean_ctor_set(x_61, 7, x_58);
lean_ctor_set(x_61, 8, x_51);
x_62 = lean_box(0);
x_63 = l_Lean_Elab_runFrontend___lambda__2(x_8, x_14, x_2, x_6, x_1, x_4, x_61, x_62, x_18);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_16);
if (x_64 == 0)
{
return x_16;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_16, 0);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_16);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_9);
if (x_68 == 0)
{
return x_9;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get(x_9, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_9);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_runFrontend___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_loop___at_Lean_Elab_runFrontend___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_runFrontend___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_runFrontend___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_8; lean_object* x_9; 
x_8 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_9 = lean_run_frontend(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Import(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Profile(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_References(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Profile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_References(builtin, lean_io_mk_world());
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
l_Lean_Elab_Frontend_processCommand___closed__1 = _init_l_Lean_Elab_Frontend_processCommand___closed__1();
lean_mark_persistent(l_Lean_Elab_Frontend_processCommand___closed__1);
l_Lean_Elab_Frontend_processCommand___closed__2 = _init_l_Lean_Elab_Frontend_processCommand___closed__2();
lean_mark_persistent(l_Lean_Elab_Frontend_processCommand___closed__2);
l_Lean_Elab_process___closed__1 = _init_l_Lean_Elab_process___closed__1();
lean_mark_persistent(l_Lean_Elab_process___closed__1);
l_Lean_Elab_process___closed__2 = _init_l_Lean_Elab_process___closed__2();
lean_mark_persistent(l_Lean_Elab_process___closed__2);
l_Lean_Elab_process___closed__3 = _init_l_Lean_Elab_process___closed__3();
lean_mark_persistent(l_Lean_Elab_process___closed__3);
l_Lean_Elab_process___closed__4 = _init_l_Lean_Elab_process___closed__4();
lean_mark_persistent(l_Lean_Elab_process___closed__4);
l_Lean_Elab_process___closed__5 = _init_l_Lean_Elab_process___closed__5();
lean_mark_persistent(l_Lean_Elab_process___closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__1 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__1();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__1);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__2 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__2();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__2);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__3 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__3();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__3);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__4 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__4();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__4);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__5 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__5();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__5);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__6 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__6();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__6);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__7 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__7();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__7);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__8 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__8();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__8);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__9 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__9();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__9);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__10 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__10();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__10);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__11 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__11();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__11);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__12 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__12();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__12);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__13 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__13();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__13);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__14 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__14();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__14);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__15 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__15();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__15);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__16 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__16();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__16);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__17 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__17();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__17);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__18 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__18();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__18);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__19 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__19();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__19);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__20 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__20();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__20);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__21 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__21();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__21);
l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__22 = _init_l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__22();
lean_mark_persistent(l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031____closed__22);
res = l_Lean_Elab_initFn____x40_Lean_Elab_Frontend___hyg_1031_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_runFrontend___closed__1 = _init_l_Lean_Elab_runFrontend___closed__1();
lean_mark_persistent(l_Lean_Elab_runFrontend___closed__1);
l_Lean_Elab_runFrontend___closed__2 = _init_l_Lean_Elab_runFrontend___closed__2();
lean_mark_persistent(l_Lean_Elab_runFrontend___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
