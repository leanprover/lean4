// Lean compiler output
// Module: Lean.Server.Snapshots
// Imports: Init Init.System.IO Lean.Elab.Frontend
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
lean_object* l_Lean_Server_Snapshots_reparseHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(lean_object*);
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty_match__1(lean_object*, uint8_t);
lean_object* l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Elab_Command_withLogging___closed__2;
lean_object* l_Std_PersistentArray_append___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__1;
lean_object* l_Lean_Server_Snapshots_parseAhead_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_parseAhead_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty(uint8_t);
extern lean_object* l_Lean_Elab_parseImports___closed__1;
lean_object* l_Lean_Server_Snapshots_reparseHeader_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__2(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Frontend_showPartialSyntaxErrors;
lean_object* l_Lean_Server_Snapshots_parseAhead(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedState___closed__1;
lean_object* l_Lean_Server_Snapshots_reparseHeader_match__1(lean_object*);
lean_object* l_Lean_Server_Snapshots_reparseHeader(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env___boxed(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_ppExpr___spec__1(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_instInhabitedModuleParserState___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot;
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos___boxed(lean_object*);
lean_object* l_IO_mkRef___at_Lean_Server_Snapshots_compileNextCmd___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_parseNextCmd(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
extern lean_object* l_Option_get_x21___rarg___closed__4;
lean_object* l_Lean_Parser_parseCommand_parse(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty___boxed(lean_object*);
uint8_t l_Lean_Parser_isExitCommand(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__1(lean_object*);
uint8_t l_Lean_Parser_isEOI(lean_object*);
lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1;
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileNextCmd(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = l_Lean_Parser_instInhabitedModuleParserState___closed__1;
x_4 = l_Lean_Elab_Command_instInhabitedState___closed__1;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1;
return x_1;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
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
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
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
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
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
lean_object* l_Lean_Server_Snapshots_reparseHeader_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Server_Snapshots_reparseHeader_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_reparseHeader_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Snapshots_reparseHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Elab_parseImports___closed__1;
x_6 = l_Lean_Parser_mkInputContext(x_1, x_5);
x_7 = l_Lean_Parser_parseHeader(x_6, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_2, 2);
lean_dec(x_14);
lean_ctor_set(x_2, 2, x_12);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_24 = x_2;
} else {
 lean_dec_ref(x_2);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 4, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Server_Snapshots_reparseHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Snapshots_reparseHeader(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty_match__1(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_internal_panic_unreachable();
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
lean_internal_panic_unreachable();
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
lean_object* l_Lean_Server_Snapshots_parseNextCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = l_Lean_Elab_parseImports___closed__1;
x_5 = l_Lean_Parser_mkInputContext(x_1, x_4);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 3);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
x_15 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_2);
lean_dec(x_2);
x_16 = l_Lean_Parser_parseCommand_parse(x_5, x_13, x_14, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
lean_object* l_Lean_Server_Snapshots_parseAhead_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Parser_parseCommand_parse(x_2, x_3, x_4, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Parser_isEOI(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_inc(x_10);
x_13 = l_Lean_Parser_isExitCommand(x_10);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_10);
x_4 = x_11;
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_array_push(x_5, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_array_push(x_5, x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
lean_object* l_Lean_Server_Snapshots_parseAhead_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Snapshots_parseAhead_go(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Server_Snapshots_parseAhead(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = l_Lean_Elab_parseImports___closed__1;
x_5 = l_Lean_Parser_mkInputContext(x_1, x_4);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 3);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
x_15 = l_Array_empty___closed__1;
x_16 = l_Lean_Server_Snapshots_parseAhead_go(x_2, x_5, x_13, x_14, x_15, x_3);
lean_dec(x_2);
return x_16;
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
lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
lean_object* l_Lean_Server_Snapshots_compileNextCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_4 = l_Lean_Elab_parseImports___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Parser_mkInputContext(x_1, x_4);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
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
x_13 = lean_ctor_get(x_6, 7);
lean_inc(x_13);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 x_14 = x_6;
} else {
 lean_dec_ref(x_6);
 x_14 = lean_box(0);
}
x_15 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 3);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_16);
lean_inc(x_7);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = l_Std_PersistentArray_empty___closed__1;
x_22 = l_Lean_Parser_parseCommand_parse(x_5, x_19, x_20, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = 0;
x_28 = l_Lean_Syntax_getPos_x3f(x_24, x_27);
lean_inc(x_24);
x_29 = l_Lean_Parser_isEOI(x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = l_instInhabitedNat;
x_102 = l_Option_get_x21___rarg___closed__4;
x_103 = lean_panic_fn(x_101, x_102);
x_30 = x_103;
goto block_100;
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_28, 0);
lean_inc(x_104);
lean_dec(x_28);
x_30 = x_104;
goto block_100;
}
block_100:
{
if (x_29 == 0)
{
uint8_t x_31; 
lean_inc(x_24);
x_31 = l_Lean_Parser_isExitCommand(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_32 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_2);
x_33 = l_Std_PersistentArray_append___rarg(x_32, x_26);
lean_inc(x_33);
if (lean_is_scalar(x_14)) {
 x_34 = lean_alloc_ctor(0, 8, 0);
} else {
 x_34 = x_14;
}
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_8);
lean_ctor_set(x_34, 3, x_9);
lean_ctor_set(x_34, 4, x_10);
lean_ctor_set(x_34, 5, x_11);
lean_ctor_set(x_34, 6, x_12);
lean_ctor_set(x_34, 7, x_13);
x_35 = l_IO_mkRef___at_Lean_Server_Snapshots_compileNextCmd___spec__1(x_34, x_3);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_64 = l_Lean_FileMap_ofString(x_1);
x_65 = l_Lean_Server_Snapshots_Snapshot_endPos(x_2);
lean_dec(x_2);
x_66 = lean_box(0);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Lean_firstFrontendMacroScope;
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_70, 0, x_4);
lean_ctor_set(x_70, 1, x_64);
lean_ctor_set(x_70, 2, x_67);
lean_ctor_set(x_70, 3, x_65);
lean_ctor_set(x_70, 4, x_66);
lean_ctor_set(x_70, 5, x_68);
lean_ctor_set(x_70, 6, x_69);
lean_inc(x_36);
lean_inc(x_24);
x_71 = l_Lean_Elab_Command_elabCommand(x_24, x_70, x_36, x_37);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_38 = x_72;
goto block_63;
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(x_73, x_70, x_36, x_74);
lean_dec(x_70);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_38 = x_76;
goto block_63;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_dec(x_71);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
lean_dec(x_73);
x_79 = l_Lean_Elab_isAbortExceptionId(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = l_Lean_InternalExceptionId_getName(x_78, x_77);
lean_dec(x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_83, 0, x_81);
x_84 = l_Lean_Elab_Command_withLogging___closed__2;
x_85 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Lean_KernelException_toMessageData___closed__15;
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = 2;
x_89 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_87, x_88, x_70, x_36, x_82);
lean_dec(x_70);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_38 = x_90;
goto block_63;
}
else
{
lean_object* x_91; 
lean_dec(x_70);
x_91 = lean_ctor_get(x_80, 1);
lean_inc(x_91);
lean_dec(x_80);
x_38 = x_91;
goto block_63;
}
}
else
{
lean_dec(x_78);
lean_dec(x_70);
x_38 = x_77;
goto block_63;
}
}
}
block_63:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_st_ref_get(x_36, x_38);
lean_dec(x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_26);
lean_dec(x_26);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_33);
lean_dec(x_16);
x_43 = lean_box(0);
x_44 = l_Lean_Server_Snapshots_compileNextCmd___lambda__1(x_30, x_24, x_25, x_40, x_43, x_41);
return x_44;
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_Elab_Frontend_showPartialSyntaxErrors;
x_46 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_16, x_45);
lean_dec(x_16);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 1);
lean_dec(x_48);
lean_ctor_set(x_40, 1, x_33);
x_49 = lean_box(0);
x_50 = l_Lean_Server_Snapshots_compileNextCmd___lambda__1(x_30, x_24, x_25, x_40, x_49, x_41);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_40, 0);
x_52 = lean_ctor_get(x_40, 2);
x_53 = lean_ctor_get(x_40, 3);
x_54 = lean_ctor_get(x_40, 4);
x_55 = lean_ctor_get(x_40, 5);
x_56 = lean_ctor_get(x_40, 6);
x_57 = lean_ctor_get(x_40, 7);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_40);
x_58 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_33);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_53);
lean_ctor_set(x_58, 4, x_54);
lean_ctor_set(x_58, 5, x_55);
lean_ctor_set(x_58, 6, x_56);
lean_ctor_set(x_58, 7, x_57);
x_59 = lean_box(0);
x_60 = l_Lean_Server_Snapshots_compileNextCmd___lambda__1(x_30, x_24, x_25, x_58, x_59, x_41);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_33);
x_61 = lean_box(0);
x_62 = l_Lean_Server_Snapshots_compileNextCmd___lambda__1(x_30, x_24, x_25, x_40, x_61, x_41);
return x_62;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_92 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_2);
lean_dec(x_2);
x_93 = l_Std_PersistentArray_append___rarg(x_92, x_26);
lean_dec(x_26);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_3);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_96 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_2);
lean_dec(x_2);
x_97 = l_Std_PersistentArray_append___rarg(x_96, x_26);
lean_dec(x_26);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_3);
return x_99;
}
}
}
}
lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Snapshots_compileNextCmd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
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
lean_object* initialize_Lean_Elab_Frontend(lean_object*);
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
res = initialize_Lean_Elab_Frontend(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1);
l_Lean_Server_Snapshots_instInhabitedSnapshot = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
