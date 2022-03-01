// Lean compiler output
// Module: Lean.Server.Snapshots
// Imports: Init Init.System.IO Lean.Elab.Import Lean.Elab.Command Lean.Widget.InteractiveDiagnostic
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
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_reparseHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lean_Server_Snapshots_compileNextCmd___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__6;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_parseAhead_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_parseAhead_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__4(size_t, size_t, lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__14;
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__10;
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Server_Snapshots_compileNextCmd___spec__1___closed__1;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__5;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__15;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__18;
extern lean_object* l_ByteArray_empty;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__16;
lean_object* l_Lean_Widget_msgToInteractiveDiagnostic(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_parseAhead(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__6;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__7;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_reparseHeader(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__2(lean_object*);
lean_object* l_Std_PersistentArray_get_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Server_Snapshots_compileNextCmd___spec__1(lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedMessage;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lean_Server_Snapshots_compileNextCmd___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withLogging(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_diagnostics(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_parseNextCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_isAtEnd___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__19;
lean_object* l_Lean_Parser_parseCommand_parse(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree;
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lean_Server_Snapshots_compileNextCmd___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t l_String_isEmpty(lean_object*);
uint8_t l_Lean_Parser_isExitCommand(lean_object*);
static size_t l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__12;
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__4;
static lean_object* l_Lean_Server_Snapshots_compileNextCmd___closed__5;
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__1(lean_object*);
static lean_object* l_Lean_Server_Snapshots_compileNextCmd___closed__3;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__11;
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_Snapshots_Snapshot_isAtEnd(lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__17;
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
static uint32_t l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__8;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_compileNextCmd___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Server_Snapshots_Snapshot_infoTree___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object*);
static lean_object* l_Lean_Server_Snapshots_compileNextCmd___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__3(size_t, size_t, lean_object*);
uint8_t l_Lean_Parser_isEOI(lean_object*);
static lean_object* l_Lean_Server_Snapshots_compileNextCmd___closed__2;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__13;
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__5;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__9;
static lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__2;
lean_object* l_List_iotaTR(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_panic___at_Lean_Elab_InfoTree_smallestInfo_x3f___spec__1(lean_object*);
lean_object* l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg(lean_object*, lean_object*);
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
x_1 = lean_unsigned_to_nat(0u);
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
x_5 = lean_alloc_ctor(0, 5, 5);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set_uint32(x_5, sizeof(void*)*5, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*5 + 4, x_2);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__16() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__15;
x_3 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__13;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__17() {
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
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__10;
x_3 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__13;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__14;
x_6 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__16;
x_7 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__17;
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
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__1;
x_4 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__18;
x_5 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__13;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_instInhabitedSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__19;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Snapshots_Snapshot_endPos(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Snapshots_Snapshot_env(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Std_PersistentArray_mapMAux___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__2(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__3(x_5, x_6, x_3);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__3(x_10, x_11, x_8);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__4(x_17, x_18, x_15);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_array_get_size(x_20);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__4(x_22, x_23, x_20);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_mapM___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Std_PersistentArray_mapMAux___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__2(x_3);
x_6 = lean_array_get_size(x_4);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__4(x_7, x_8, x_4);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get_usize(x_1, 4);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_15 = l_Std_PersistentArray_mapMAux___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__2(x_10);
x_16 = lean_array_get_size(x_11);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__4(x_17, x_18, x_11);
x_20 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_12);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set_usize(x_20, 4, x_13);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_diagnostics(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Std_PersistentArray_mapM___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__1(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_Snapshots_Snapshot_diagnostics___spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Server_Snapshots_Snapshot_infoTree___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_instInhabitedInfoTree;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assertion violation: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("s.cmdState.infoState.trees.size == 1\n  ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1;
x_2 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Server.Snapshots");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Server.Snapshots.Snapshot.infoTree");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__4;
x_2 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__5;
x_3 = lean_unsigned_to_nat(55u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 7);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__6;
x_9 = l_panic___at_Lean_Server_Snapshots_Snapshot_infoTree___spec__1(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Elab_instInhabitedInfoTree;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Std_PersistentArray_get_x21___rarg(x_10, x_4, x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_Snapshots_Snapshot_isAtEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
lean_inc(x_2);
x_3 = l_Lean_Parser_isEOI(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Parser_isExitCommand(x_2);
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_isAtEnd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_Snapshots_Snapshot_isAtEnd(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_reparseHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_parseHeader(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
lean_ctor_set(x_2, 2, x_11);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 3);
x_17 = lean_ctor_get(x_2, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set(x_18, 4, x_17);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 4);
lean_inc(x_24);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_25 = x_2;
} else {
 lean_dec_ref(x_2);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 5, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_reparseHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Snapshots_reparseHeader(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_parseNextCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Command_instInhabitedScope;
x_8 = l_List_head_x21___rarg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 3);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set(x_12, 3, x_11);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_2);
lean_dec(x_2);
x_15 = l_Lean_Parser_parseCommand_parse(x_1, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_parseAhead_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_parseAhead_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Snapshots_parseAhead_go(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_parseAhead(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Command_instInhabitedScope;
x_8 = l_List_head_x21___rarg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 3);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set(x_12, 3, x_11);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__7;
x_15 = l_Lean_Server_Snapshots_parseAhead_go(x_2, x_1, x_12, x_13, x_14, x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_nat_sub(x_4, x_9);
x_12 = l_Lean_instInhabitedMessage;
lean_inc(x_3);
x_13 = l_Std_PersistentArray_get_x21___rarg(x_12, x_3, x_11);
lean_dec(x_11);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = l_Lean_Widget_msgToInteractiveDiagnostic(x_14, x_13, x_2, x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Std_PersistentArray_push___rarg(x_6, x_16);
x_5 = x_10;
x_6 = x_18;
x_7 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
x_7 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_nat_sub(x_6, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_2, 4);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_List_iotaTR(x_9);
x_12 = l_List_forIn_loop___at_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags___spec__1(x_1, x_3, x_4, x_6, x_11, x_10, x_5);
lean_dec(x_11);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_List_forIn_loop___at_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags___spec__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lean_Server_Snapshots_compileNextCmd___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stderr(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stderr(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stderr(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lean_Server_Snapshots_compileNextCmd___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stdout(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stdout(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stdout(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lean_Server_Snapshots_compileNextCmd___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_get_set_stdin(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stdin(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_get_set_stdin(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lean_Server_Snapshots_compileNextCmd___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ByteArray_empty;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Server_Snapshots_compileNextCmd___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l_IO_FS_withIsolatedStreams___at_Lean_Server_Snapshots_compileNextCmd___spec__1___closed__1;
x_4 = lean_st_mk_ref(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_st_mk_ref(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_IO_FS_Stream_ofBuffer(x_5);
lean_inc(x_8);
x_11 = l_IO_FS_Stream_ofBuffer(x_8);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lean_Server_Snapshots_compileNextCmd___spec__2), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
x_13 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lean_Server_Snapshots_compileNextCmd___spec__3), 3, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_IO_withStdin___at_Lean_Server_Snapshots_compileNextCmd___spec__4(x_10, x_13, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_8, x_16);
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_string_from_utf8_unchecked(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_string_from_utf8_unchecked(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_15);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Command_elabCommandTopLevel(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_withLogging(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = l_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags(x_1, x_2, x_3, x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set(x_14, 3, x_7);
lean_ctor_set(x_14, 4, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 2, x_6);
lean_ctor_set(x_17, 3, x_7);
lean_ctor_set(x_17, 4, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Server_Snapshots_compileNextCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_compileNextCmd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.Option.BasicAux");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_compileNextCmd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Option.get!");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_compileNextCmd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("value is none");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_compileNextCmd___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Server_Snapshots_compileNextCmd___closed__2;
x_2 = l_Lean_Server_Snapshots_compileNextCmd___closed__3;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Server_Snapshots_compileNextCmd___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 6);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 7);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 8);
lean_inc(x_14);
x_15 = l_Lean_Elab_Command_instInhabitedScope;
x_16 = l_List_head_x21___rarg(x_15, x_8);
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
x_21 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_2);
lean_inc(x_1);
x_22 = l_Lean_Parser_parseCommand_parse(x_1, x_20, x_6, x_21);
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
lean_object* x_185; lean_object* x_186; 
x_185 = l_Lean_Server_Snapshots_compileNextCmd___closed__5;
x_186 = l_panic___at_Lean_Elab_InfoTree_smallestInfo_x3f___spec__1(x_185);
x_30 = x_186;
goto block_184;
}
else
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_28, 0);
lean_inc(x_187);
lean_dec(x_28);
x_30 = x_187;
goto block_184;
}
block_184:
{
if (x_29 == 0)
{
uint8_t x_31; 
lean_inc(x_24);
x_31 = l_Lean_Parser_isExitCommand(x_24);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_33 = lean_ctor_get(x_5, 8);
lean_dec(x_33);
x_34 = lean_ctor_get(x_5, 7);
lean_dec(x_34);
x_35 = lean_ctor_get(x_5, 6);
lean_dec(x_35);
x_36 = lean_ctor_get(x_5, 5);
lean_dec(x_36);
x_37 = lean_ctor_get(x_5, 4);
lean_dec(x_37);
x_38 = lean_ctor_get(x_5, 3);
lean_dec(x_38);
x_39 = lean_ctor_get(x_5, 2);
lean_dec(x_39);
x_40 = lean_ctor_get(x_5, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_5, 0);
lean_dec(x_41);
lean_ctor_set(x_5, 1, x_26);
x_42 = lean_st_mk_ref(x_5, x_4);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
x_47 = l_Lean_Server_Snapshots_Snapshot_endPos(x_2);
x_48 = lean_box(0);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Lean_firstFrontendMacroScope;
x_51 = lean_box(0);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
x_52 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_46);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_47);
lean_ctor_set(x_52, 4, x_48);
lean_ctor_set(x_52, 5, x_50);
lean_ctor_set(x_52, 6, x_51);
lean_inc(x_24);
x_53 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_compileNextCmd___lambda__1), 4, 1);
lean_closure_set(x_53, 0, x_24);
lean_inc(x_43);
x_54 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_compileNextCmd___lambda__2), 4, 3);
lean_closure_set(x_54, 0, x_53);
lean_closure_set(x_54, 1, x_52);
lean_closure_set(x_54, 2, x_43);
x_55 = l_IO_FS_withIsolatedStreams___at_Lean_Server_Snapshots_compileNextCmd___spec__1(x_54, x_44);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_43, x_57);
lean_dec(x_43);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_String_isEmpty(x_58);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_60, 1);
x_65 = l_Lean_FileMap_toPosition(x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_58);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = 0;
x_70 = l_Lean_Server_Snapshots_compileNextCmd___closed__1;
x_71 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_71, 0, x_45);
lean_ctor_set(x_71, 1, x_65);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set(x_71, 4, x_68);
lean_ctor_set_uint8(x_71, sizeof(void*)*5, x_69);
x_72 = l_Std_PersistentArray_push___rarg(x_64, x_71);
lean_ctor_set(x_60, 1, x_72);
x_73 = lean_box(0);
x_74 = l_Lean_Server_Snapshots_compileNextCmd___lambda__3(x_1, x_2, x_3, x_30, x_24, x_25, x_60, x_73, x_61);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_75 = lean_ctor_get(x_60, 0);
x_76 = lean_ctor_get(x_60, 1);
x_77 = lean_ctor_get(x_60, 2);
x_78 = lean_ctor_get(x_60, 3);
x_79 = lean_ctor_get(x_60, 4);
x_80 = lean_ctor_get(x_60, 5);
x_81 = lean_ctor_get(x_60, 6);
x_82 = lean_ctor_get(x_60, 7);
x_83 = lean_ctor_get(x_60, 8);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_60);
x_84 = l_Lean_FileMap_toPosition(x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_86, 0, x_58);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = 0;
x_89 = l_Lean_Server_Snapshots_compileNextCmd___closed__1;
x_90 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_90, 0, x_45);
lean_ctor_set(x_90, 1, x_84);
lean_ctor_set(x_90, 2, x_85);
lean_ctor_set(x_90, 3, x_89);
lean_ctor_set(x_90, 4, x_87);
lean_ctor_set_uint8(x_90, sizeof(void*)*5, x_88);
x_91 = l_Std_PersistentArray_push___rarg(x_76, x_90);
x_92 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_92, 0, x_75);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_92, 2, x_77);
lean_ctor_set(x_92, 3, x_78);
lean_ctor_set(x_92, 4, x_79);
lean_ctor_set(x_92, 5, x_80);
lean_ctor_set(x_92, 6, x_81);
lean_ctor_set(x_92, 7, x_82);
lean_ctor_set(x_92, 8, x_83);
x_93 = lean_box(0);
x_94 = l_Lean_Server_Snapshots_compileNextCmd___lambda__3(x_1, x_2, x_3, x_30, x_24, x_25, x_92, x_93, x_61);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_58);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_95 = lean_box(0);
x_96 = l_Lean_Server_Snapshots_compileNextCmd___lambda__3(x_1, x_2, x_3, x_30, x_24, x_25, x_60, x_95, x_61);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_55);
if (x_97 == 0)
{
return x_55;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_55, 0);
x_99 = lean_ctor_get(x_55, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_55);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_5);
x_101 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_101, 0, x_7);
lean_ctor_set(x_101, 1, x_26);
lean_ctor_set(x_101, 2, x_8);
lean_ctor_set(x_101, 3, x_9);
lean_ctor_set(x_101, 4, x_10);
lean_ctor_set(x_101, 5, x_11);
lean_ctor_set(x_101, 6, x_12);
lean_ctor_set(x_101, 7, x_13);
lean_ctor_set(x_101, 8, x_14);
x_102 = lean_st_mk_ref(x_101, x_4);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_1, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_1, 2);
lean_inc(x_106);
x_107 = l_Lean_Server_Snapshots_Snapshot_endPos(x_2);
x_108 = lean_box(0);
x_109 = lean_unsigned_to_nat(0u);
x_110 = l_Lean_firstFrontendMacroScope;
x_111 = lean_box(0);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
x_112 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_112, 0, x_105);
lean_ctor_set(x_112, 1, x_106);
lean_ctor_set(x_112, 2, x_109);
lean_ctor_set(x_112, 3, x_107);
lean_ctor_set(x_112, 4, x_108);
lean_ctor_set(x_112, 5, x_110);
lean_ctor_set(x_112, 6, x_111);
lean_inc(x_24);
x_113 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_compileNextCmd___lambda__1), 4, 1);
lean_closure_set(x_113, 0, x_24);
lean_inc(x_103);
x_114 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_compileNextCmd___lambda__2), 4, 3);
lean_closure_set(x_114, 0, x_113);
lean_closure_set(x_114, 1, x_112);
lean_closure_set(x_114, 2, x_103);
x_115 = l_IO_FS_withIsolatedStreams___at_Lean_Server_Snapshots_compileNextCmd___spec__1(x_114, x_104);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_st_ref_get(x_103, x_117);
lean_dec(x_103);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_String_isEmpty(x_118);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_120, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_120, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_120, 5);
lean_inc(x_128);
x_129 = lean_ctor_get(x_120, 6);
lean_inc(x_129);
x_130 = lean_ctor_get(x_120, 7);
lean_inc(x_130);
x_131 = lean_ctor_get(x_120, 8);
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
 x_132 = x_120;
} else {
 lean_dec_ref(x_120);
 x_132 = lean_box(0);
}
x_133 = l_Lean_FileMap_toPosition(x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_118);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = 0;
x_138 = l_Lean_Server_Snapshots_compileNextCmd___closed__1;
x_139 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_139, 0, x_105);
lean_ctor_set(x_139, 1, x_133);
lean_ctor_set(x_139, 2, x_134);
lean_ctor_set(x_139, 3, x_138);
lean_ctor_set(x_139, 4, x_136);
lean_ctor_set_uint8(x_139, sizeof(void*)*5, x_137);
x_140 = l_Std_PersistentArray_push___rarg(x_124, x_139);
if (lean_is_scalar(x_132)) {
 x_141 = lean_alloc_ctor(0, 9, 0);
} else {
 x_141 = x_132;
}
lean_ctor_set(x_141, 0, x_123);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_125);
lean_ctor_set(x_141, 3, x_126);
lean_ctor_set(x_141, 4, x_127);
lean_ctor_set(x_141, 5, x_128);
lean_ctor_set(x_141, 6, x_129);
lean_ctor_set(x_141, 7, x_130);
lean_ctor_set(x_141, 8, x_131);
x_142 = lean_box(0);
x_143 = l_Lean_Server_Snapshots_compileNextCmd___lambda__3(x_1, x_2, x_3, x_30, x_24, x_25, x_141, x_142, x_121);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_118);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
x_144 = lean_box(0);
x_145 = l_Lean_Server_Snapshots_compileNextCmd___lambda__3(x_1, x_2, x_3, x_30, x_24, x_25, x_120, x_144, x_121);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_146 = lean_ctor_get(x_115, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_115, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_148 = x_115;
} else {
 lean_dec_ref(x_115);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
else
{
lean_object* x_150; uint8_t x_151; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_inc(x_2);
x_150 = l_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags(x_1, x_2, x_3, x_26, x_4);
x_151 = !lean_is_exclusive(x_2);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_152 = lean_ctor_get(x_2, 4);
lean_dec(x_152);
x_153 = lean_ctor_get(x_2, 3);
lean_dec(x_153);
x_154 = lean_ctor_get(x_2, 2);
lean_dec(x_154);
x_155 = lean_ctor_get(x_2, 1);
lean_dec(x_155);
x_156 = lean_ctor_get(x_2, 0);
lean_dec(x_156);
x_157 = !lean_is_exclusive(x_150);
if (x_157 == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_150, 0);
lean_ctor_set(x_2, 4, x_158);
lean_ctor_set(x_2, 2, x_25);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_30);
lean_ctor_set(x_150, 0, x_2);
return x_150;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_150, 0);
x_160 = lean_ctor_get(x_150, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_150);
lean_ctor_set(x_2, 4, x_159);
lean_ctor_set(x_2, 2, x_25);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_30);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_2);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_2);
x_162 = lean_ctor_get(x_150, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_150, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_164 = x_150;
} else {
 lean_dec_ref(x_150);
 x_164 = lean_box(0);
}
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_30);
lean_ctor_set(x_165, 1, x_24);
lean_ctor_set(x_165, 2, x_25);
lean_ctor_set(x_165, 3, x_5);
lean_ctor_set(x_165, 4, x_162);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
}
}
else
{
lean_object* x_167; uint8_t x_168; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_inc(x_2);
x_167 = l_Lean_Server_Snapshots_compileNextCmd_withNewInteractiveDiags(x_1, x_2, x_3, x_26, x_4);
x_168 = !lean_is_exclusive(x_2);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_169 = lean_ctor_get(x_2, 4);
lean_dec(x_169);
x_170 = lean_ctor_get(x_2, 3);
lean_dec(x_170);
x_171 = lean_ctor_get(x_2, 2);
lean_dec(x_171);
x_172 = lean_ctor_get(x_2, 1);
lean_dec(x_172);
x_173 = lean_ctor_get(x_2, 0);
lean_dec(x_173);
x_174 = !lean_is_exclusive(x_167);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_167, 0);
lean_ctor_set(x_2, 4, x_175);
lean_ctor_set(x_2, 2, x_25);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_30);
lean_ctor_set(x_167, 0, x_2);
return x_167;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_167, 0);
x_177 = lean_ctor_get(x_167, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_167);
lean_ctor_set(x_2, 4, x_176);
lean_ctor_set(x_2, 2, x_25);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_30);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_2);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_2);
x_179 = lean_ctor_get(x_167, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_167, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_181 = x_167;
} else {
 lean_dec_ref(x_167);
 x_181 = lean_box(0);
}
x_182 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_182, 0, x_30);
lean_ctor_set(x_182, 1, x_24);
lean_ctor_set(x_182, 2, x_25);
lean_ctor_set(x_182, 3, x_5);
lean_ctor_set(x_182, 4, x_179);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Server_Snapshots_compileNextCmd___lambda__3(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_compileNextCmd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Server_Snapshots_compileNextCmd(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Import(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_InteractiveDiagnostic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Snapshots(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_InteractiveDiagnostic(builtin, lean_io_mk_world());
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
l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__19 = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__19();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot___closed__19);
l_Lean_Server_Snapshots_instInhabitedSnapshot = _init_l_Lean_Server_Snapshots_instInhabitedSnapshot();
lean_mark_persistent(l_Lean_Server_Snapshots_instInhabitedSnapshot);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__4 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__4();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__4);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__5 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__5();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__5);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__6 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__6();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__6);
l_IO_FS_withIsolatedStreams___at_Lean_Server_Snapshots_compileNextCmd___spec__1___closed__1 = _init_l_IO_FS_withIsolatedStreams___at_Lean_Server_Snapshots_compileNextCmd___spec__1___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lean_Server_Snapshots_compileNextCmd___spec__1___closed__1);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
