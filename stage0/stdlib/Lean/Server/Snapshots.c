// Lean compiler output
// Module: Lean.Server.Snapshots
// Imports: Init Init.System.IO Lean.Elab.Import Lean.Elab.Command
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
lean_object* l_Lean_Server_Snapshots_Snapshot_toCmdState_match__1(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(lean_object*);
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty_match__1(lean_object*, uint8_t);
lean_object* l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_withLogging___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_toCmdState(lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty(uint8_t);
lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
extern lean_object* l_Lean_Elab_parseImports___closed__1;
lean_object* l_Lean_Server_Snapshots_compileHeader_match__2(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__2(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env_match__1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileHeader_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileHeader_match__1(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog_match__1(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileHeader(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos___boxed(lean_object*);
lean_object* l_IO_mkRef___at_Lean_Server_Snapshots_compileNextCmd___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileNextCmd_match__1(lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__4;
lean_object* l_Lean_Parser_parseCommand_parse(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty___boxed(lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isExitCommand(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty_match__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortExceptionId;
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__1(lean_object*);
uint8_t l_Lean_Parser_isEOI(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileHeader_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileNextCmd_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_toCmdState_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileNextCmd(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSourceInfo;
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Snapshots_Snapshot_endPos(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_env_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_apply_5(x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_apply_3(x_3, x_11, x_12, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_env_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_Snapshot_env_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_env___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Snapshots_Snapshot_env(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_apply_5(x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_apply_3(x_3, x_11, x_12, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_Snapshot_msgLog_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_toCmdState_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_apply_5(x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_apply_3(x_3, x_11, x_12, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_toCmdState_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_Snapshot_toCmdState_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_toCmdState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Elab_Command_mkState(x_3, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
return x_7;
}
}
}
lean_object* l_Lean_Server_Snapshots_compileHeader_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Server_Snapshots_compileHeader_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_compileHeader_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Snapshots_compileHeader_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Server_Snapshots_compileHeader_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_compileHeader_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Snapshots_compileHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Elab_parseImports___closed__1;
x_5 = l_Lean_Parser_mkInputContext(x_1, x_4);
lean_inc(x_5);
x_6 = l_Lean_Parser_parseHeader(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = 0;
lean_inc(x_2);
x_14 = l_Lean_Elab_processHeader(x_10, x_2, x_12, x_5, x_13, x_9);
lean_dec(x_5);
lean_dec(x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_2);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
return x_6;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_6);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty_match__1(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_panic_unreachable();
}
}
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty_match__1(x_1, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty(uint8_t x_1) {
_start:
{
lean_panic_unreachable();
}
}
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty(x_2);
return x_3;
}
}
lean_object* l_Lean_Server_Snapshots_compileNextCmd_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Server_Snapshots_compileNextCmd_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_compileNextCmd_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_IO_mkRef___at_Lean_Server_Snapshots_compileNextCmd___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Snapshots_compileNextCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_4 = l_Lean_Elab_parseImports___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Parser_mkInputContext(x_1, x_4);
lean_inc(x_2);
x_6 = l_Lean_Server_Snapshots_Snapshot_toCmdState(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 6);
lean_inc(x_12);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 x_13 = x_6;
} else {
 lean_dec_ref(x_6);
 x_13 = lean_box(0);
}
x_14 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_8);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 3);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_7);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_2);
x_20 = l_Lean_Parser_parseCommand_parse(x_5, x_17, x_18, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Syntax_getHeadInfo(x_22);
lean_inc(x_22);
x_26 = l_Lean_Parser_isEOI(x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = l_Lean_instInhabitedSourceInfo;
x_82 = l_Option_get_x21___rarg___closed__4;
x_83 = lean_panic_fn(x_81, x_82);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_instInhabitedNat;
x_86 = lean_panic_fn(x_85, x_82);
x_27 = x_86;
goto block_80;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
x_27 = x_87;
goto block_80;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_25, 0);
lean_inc(x_88);
lean_dec(x_25);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = l_instInhabitedNat;
x_91 = l_Option_get_x21___rarg___closed__4;
x_92 = lean_panic_fn(x_90, x_91);
x_27 = x_92;
goto block_80;
}
else
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
lean_dec(x_89);
x_27 = x_93;
goto block_80;
}
}
block_80:
{
if (x_26 == 0)
{
uint8_t x_28; 
lean_inc(x_22);
x_28 = l_Lean_Parser_isExitCommand(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
if (lean_is_scalar(x_13)) {
 x_29 = lean_alloc_ctor(0, 7, 0);
} else {
 x_29 = x_13;
}
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_8);
lean_ctor_set(x_29, 3, x_9);
lean_ctor_set(x_29, 4, x_10);
lean_ctor_set(x_29, 5, x_11);
lean_ctor_set(x_29, 6, x_12);
x_30 = l_IO_mkRef___at_Lean_Server_Snapshots_compileNextCmd___spec__1(x_29, x_3);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_47 = l_Lean_FileMap_ofString(x_1);
x_48 = l_Lean_Server_Snapshots_Snapshot_endPos(x_2);
lean_dec(x_2);
x_49 = lean_box(0);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_firstFrontendMacroScope;
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_47);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_48);
lean_ctor_set(x_53, 4, x_49);
lean_ctor_set(x_53, 5, x_51);
lean_ctor_set(x_53, 6, x_52);
lean_inc(x_31);
x_54 = l_Lean_Elab_Command_elabCommand(x_22, x_53, x_31, x_32);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_33 = x_55;
goto block_46;
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_56, x_53, x_31, x_57);
lean_dec(x_53);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_33 = x_59;
goto block_46;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
x_62 = l_Lean_Elab_abortExceptionId;
x_63 = lean_nat_dec_eq(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Lean_InternalExceptionId_getName(x_61, x_60);
lean_dec(x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_67, 0, x_65);
x_68 = l_Lean_Elab_Command_withLogging___closed__2;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_KernelException_toMessageData___closed__15;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = 2;
x_73 = l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(x_71, x_72, x_53, x_31, x_66);
lean_dec(x_53);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_33 = x_74;
goto block_46;
}
else
{
lean_object* x_75; 
lean_dec(x_53);
x_75 = lean_ctor_get(x_64, 1);
lean_inc(x_75);
lean_dec(x_64);
x_33 = x_75;
goto block_46;
}
}
else
{
lean_dec(x_61);
lean_dec(x_53);
x_33 = x_60;
goto block_46;
}
}
}
block_46:
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_st_ref_get(x_31, x_33);
lean_dec(x_31);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_27);
lean_ctor_set(x_43, 1, x_23);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_24);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_3);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_24);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_3);
return x_79;
}
}
}
}
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_compileCmdsAfter_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_compileCmdsAfter_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = l_Lean_Server_Snapshots_compileNextCmd(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_7);
x_8 = l_Lean_Server_Snapshots_compileCmdsAfter(x_1, x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_20);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_4, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_4, 0, x_30);
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_dec(x_4);
x_32 = lean_ctor_get(x_5, 0);
lean_inc(x_32);
lean_dec(x_5);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Lean_Elab_Import(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Server_Snapshots(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
