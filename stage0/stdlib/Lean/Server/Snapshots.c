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
lean_object* l_Lean_Server_Snapshots_reparseHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_catchExceptions(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(lean_object*);
lean_object* l_IO_FS_withIsolatedStreams___rarg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty_match__1(lean_object*, uint8_t);
lean_object* l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__6;
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_parseAhead_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_parseAhead_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__14;
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty(uint8_t);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__10;
lean_object* l_Lean_Server_Snapshots_reparseHeader_match__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__5;
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__2(lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__15;
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__18;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__16;
lean_object* l_EIO_toIO___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_parseAhead(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__2___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__7;
lean_object* l_Lean_Server_Snapshots_reparseHeader_match__1(lean_object*);
lean_object* l_Lean_Server_Snapshots_reparseHeader(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_env___boxed(lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_compileNextCmd___closed__6;
static lean_object* l_Lean_Server_Snapshots_reparseHeader___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot;
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos___boxed(lean_object*);
lean_object* l_IO_mkRef___at_Lean_Server_Snapshots_compileNextCmd___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_compileNextCmd_match__1(lean_object*);
lean_object* l_Lean_Server_Snapshots_parseNextCmd(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Parser_parseCommand_parse(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
uint8_t l_String_isEmpty(lean_object*);
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty___boxed(lean_object*);
uint8_t l_Lean_Parser_isExitCommand(lean_object*);
static size_t l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__12;
static lean_object* l_Lean_Server_Snapshots_compileNextCmd___closed__5;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_compileNextCmd___closed__3;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__11;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__17;
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
static uint32_t l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__8;
lean_object* l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty_match__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_compileNextCmd___closed__1;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__4;
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object*);
static lean_object* l_Lean_Server_Snapshots_compileNextCmd___closed__4;
lean_object* l_Lean_Server_Snapshots_compileCmdsAfter_match__1(lean_object*);
uint8_t l_Lean_Parser_isEOI(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileNextCmd_match__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_compileNextCmd___closed__2;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__13;
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__9;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__2;
lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Server_Snapshots_compileNextCmd(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1() {
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
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__2;
x_3 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__5;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static uint32_t _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__8() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__9() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__8;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__7;
x_5 = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_uint32(x_5, sizeof(void*)*4, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4 + 4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__2;
x_2 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__6;
x_3 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__7;
x_4 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__9;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__12() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__11;
x_2 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__7;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__12;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__15() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__5;
x_3 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__13;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__16() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__13;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__10;
x_3 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__13;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__14;
x_6 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__15;
x_7 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__16;
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_4);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_5);
lean_ctor_set(x_8, 7, x_6);
lean_ctor_set(x_8, 8, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1;
x_4 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__17;
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
x_1 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__18;
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
static lean_object* _init_l_Lean_Server_Snapshots_reparseHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<input>");
return x_1;
}
}
lean_object* l_Lean_Server_Snapshots_reparseHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Server_Snapshots_reparseHeader___closed__1;
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
x_4 = l_Lean_Server_Snapshots_reparseHeader___closed__1;
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
x_4 = l_Lean_Server_Snapshots_reparseHeader___closed__1;
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
x_15 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__7;
x_16 = l_Lean_Server_Snapshots_parseAhead_go(x_2, x_5, x_13, x_14, x_15, x_3);
lean_dec(x_2);
return x_16;
}
}
lean_object* l_Lean_Server_Snapshots_compileNextCmd_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Server_Snapshots_compileNextCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Snapshots_0__Lean_Server_Snapshots_ioErrorFromEmpty___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_compileNextCmd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_compileNextCmd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.Option.BasicAux");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_compileNextCmd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Option.get!");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_compileNextCmd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("value is none");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_compileNextCmd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Server_Snapshots_compileNextCmd___closed__3;
x_2 = l_Lean_Server_Snapshots_compileNextCmd___closed__4;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Server_Snapshots_compileNextCmd___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Server_Snapshots_compileNextCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_4 = l_Lean_Server_Snapshots_reparseHeader___closed__1;
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
x_14 = lean_ctor_get(x_6, 8);
lean_inc(x_14);
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
 x_15 = x_6;
} else {
 lean_dec_ref(x_6);
 x_15 = lean_box(0);
}
x_16 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_8);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 3);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_7);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
x_22 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_2);
x_23 = l_Lean_Parser_parseCommand_parse(x_5, x_20, x_21, x_22);
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
x_28 = 0;
x_29 = l_Lean_Syntax_getPos_x3f(x_25, x_28);
lean_inc(x_25);
x_30 = l_Lean_Parser_isEOI(x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = l_instInhabitedNat;
x_100 = l_Lean_Server_Snapshots_compileNextCmd___closed__6;
x_101 = lean_panic_fn(x_99, x_100);
x_31 = x_101;
goto block_98;
}
else
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_29, 0);
lean_inc(x_102);
lean_dec(x_29);
x_31 = x_102;
goto block_98;
}
block_98:
{
if (x_30 == 0)
{
uint8_t x_32; 
lean_inc(x_25);
x_32 = l_Lean_Parser_isExitCommand(x_25);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
if (lean_is_scalar(x_15)) {
 x_33 = lean_alloc_ctor(0, 9, 0);
} else {
 x_33 = x_15;
}
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_8);
lean_ctor_set(x_33, 3, x_9);
lean_ctor_set(x_33, 4, x_10);
lean_ctor_set(x_33, 5, x_11);
lean_ctor_set(x_33, 6, x_12);
lean_ctor_set(x_33, 7, x_13);
lean_ctor_set(x_33, 8, x_14);
x_34 = l_IO_mkRef___at_Lean_Server_Snapshots_compileNextCmd___spec__1(x_33, x_3);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_FileMap_ofString(x_1);
x_38 = l_Lean_Server_Snapshots_Snapshot_endPos(x_2);
lean_dec(x_2);
x_39 = lean_box(0);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_firstFrontendMacroScope;
x_42 = lean_box(0);
lean_inc(x_38);
lean_inc(x_37);
x_43 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_39);
lean_ctor_set(x_43, 5, x_41);
lean_ctor_set(x_43, 6, x_42);
lean_inc(x_25);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand___boxed), 4, 1);
lean_closure_set(x_44, 0, x_25);
lean_inc(x_35);
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Command_catchExceptions), 4, 3);
lean_closure_set(x_45, 0, x_44);
lean_closure_set(x_45, 1, x_43);
lean_closure_set(x_45, 2, x_35);
x_46 = l_Lean_Server_Snapshots_compileNextCmd___closed__1;
x_47 = lean_alloc_closure((void*)(l_EIO_toIO___rarg), 3, 2);
lean_closure_set(x_47, 0, x_46);
lean_closure_set(x_47, 1, x_45);
x_48 = l_IO_FS_withIsolatedStreams___rarg(x_47, x_36);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_st_ref_get(x_35, x_50);
lean_dec(x_35);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_String_isEmpty(x_51);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_53, 1);
x_58 = l_Lean_FileMap_toPosition(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_51);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = 0;
x_63 = l_Lean_Server_Snapshots_compileNextCmd___closed__2;
x_64 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_64, 0, x_4);
lean_ctor_set(x_64, 1, x_58);
lean_ctor_set(x_64, 2, x_59);
lean_ctor_set(x_64, 3, x_63);
lean_ctor_set(x_64, 4, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*5, x_62);
x_65 = l_Std_PersistentArray_push___rarg(x_57, x_64);
lean_ctor_set(x_53, 1, x_65);
x_66 = lean_box(0);
x_67 = l_Lean_Server_Snapshots_compileNextCmd___lambda__1(x_31, x_25, x_26, x_53, x_66, x_54);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_68 = lean_ctor_get(x_53, 0);
x_69 = lean_ctor_get(x_53, 1);
x_70 = lean_ctor_get(x_53, 2);
x_71 = lean_ctor_get(x_53, 3);
x_72 = lean_ctor_get(x_53, 4);
x_73 = lean_ctor_get(x_53, 5);
x_74 = lean_ctor_get(x_53, 6);
x_75 = lean_ctor_get(x_53, 7);
x_76 = lean_ctor_get(x_53, 8);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_53);
x_77 = l_Lean_FileMap_toPosition(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_51);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = 0;
x_82 = l_Lean_Server_Snapshots_compileNextCmd___closed__2;
x_83 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_83, 0, x_4);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 4, x_80);
lean_ctor_set_uint8(x_83, sizeof(void*)*5, x_81);
x_84 = l_Std_PersistentArray_push___rarg(x_69, x_83);
x_85 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_85, 0, x_68);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_70);
lean_ctor_set(x_85, 3, x_71);
lean_ctor_set(x_85, 4, x_72);
lean_ctor_set(x_85, 5, x_73);
lean_ctor_set(x_85, 6, x_74);
lean_ctor_set(x_85, 7, x_75);
lean_ctor_set(x_85, 8, x_76);
x_86 = lean_box(0);
x_87 = l_Lean_Server_Snapshots_compileNextCmd___lambda__1(x_31, x_25, x_26, x_85, x_86, x_54);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_37);
x_88 = lean_box(0);
x_89 = l_Lean_Server_Snapshots_compileNextCmd___lambda__1(x_31, x_25, x_26, x_53, x_88, x_54);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
x_90 = !lean_is_exclusive(x_48);
if (x_90 == 0)
{
return x_48;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_48, 0);
x_92 = lean_ctor_get(x_48, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_48);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_27);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_3);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_27);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_3);
return x_97;
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
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_Server_Snapshots_compileNextCmd(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_7);
x_8 = l_Lean_Server_Snapshots_compileCmdsAfter(x_1, x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
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
lean_dec(x_7);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_4, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_5, 0);
lean_inc(x_32);
lean_dec(x_5);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_4, 0, x_34);
return x_4;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_dec(x_4);
x_36 = lean_ctor_get(x_5, 0);
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_4);
if (x_40 == 0)
{
return x_4;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_4, 0);
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_4);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__2 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__2();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__2);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__3 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__3();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__3);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__4 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__4();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__4);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__5 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__5();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__5);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__6 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__6();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__6);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__7 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__7();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__7);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__8 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__8();
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__9 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__9();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__9);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__10 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__10();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__10);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__11 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__11();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__11);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__12 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__12();
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__13 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__13();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__13);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__14 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__14();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__14);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__15 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__15();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__15);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__16 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__16();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__16);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__17 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__17();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__17);
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__18 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__18();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__18);
l_Lean_Server_Snapshots_instInhabitedSnapshot = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot);
l_Lean_Server_Snapshots_reparseHeader___closed__1 = _init_l_Lean_Server_Snapshots_reparseHeader___closed__1();
lean_mark_persistent(l_Lean_Server_Snapshots_reparseHeader___closed__1);
l_Lean_Server_Snapshots_compileNextCmd___closed__1 = _init_l_Lean_Server_Snapshots_compileNextCmd___closed__1();
lean_mark_persistent(l_Lean_Server_Snapshots_compileNextCmd___closed__1);
l_Lean_Server_Snapshots_compileNextCmd___closed__2 = _init_l_Lean_Server_Snapshots_compileNextCmd___closed__2();
lean_mark_persistent(l_Lean_Server_Snapshots_compileNextCmd___closed__2);
l_Lean_Server_Snapshots_compileNextCmd___closed__3 = _init_l_Lean_Server_Snapshots_compileNextCmd___closed__3();
lean_mark_persistent(l_Lean_Server_Snapshots_compileNextCmd___closed__3);
l_Lean_Server_Snapshots_compileNextCmd___closed__4 = _init_l_Lean_Server_Snapshots_compileNextCmd___closed__4();
lean_mark_persistent(l_Lean_Server_Snapshots_compileNextCmd___closed__4);
l_Lean_Server_Snapshots_compileNextCmd___closed__5 = _init_l_Lean_Server_Snapshots_compileNextCmd___closed__5();
lean_mark_persistent(l_Lean_Server_Snapshots_compileNextCmd___closed__5);
l_Lean_Server_Snapshots_compileNextCmd___closed__6 = _init_l_Lean_Server_Snapshots_compileNextCmd___closed__6();
lean_mark_persistent(l_Lean_Server_Snapshots_compileNextCmd___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
