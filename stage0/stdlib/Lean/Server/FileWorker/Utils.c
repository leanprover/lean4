// Lean compiler output
// Module: Lean.Server.FileWorker.Utils
// Imports: Init Lean.Server.Utils Lean.Server.Snapshots Lean.Server.AsyncList Lean.Server.Rpc.Basic
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Server_FileWorker_instMonadRpcSession___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_logSnapContent___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_store(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_mono_ms_now(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Server_FileWorker_instMonadRpcSession___spec__2(lean_object*, size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Server_FileWorker_RpcSession_store___spec__1(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_logSnapContent___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__6___boxed(lean_object*, lean_object*);
uint64_t l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_hashRpcRef____x40_Lean_Data_Lsp_Extra___hyg_966_(size_t);
LEAN_EXPORT lean_object* l_Array_indexOfAux___at_Lean_Server_FileWorker_RpcSession_release___spec__6___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Server_FileWorker_logSnapContent___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_logSnapContent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOfAux___at_Lean_Server_FileWorker_RpcSession_release___spec__6(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_FileWorker_RpcSession_store___spec__4(lean_object*, lean_object*, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Server_FileWorker_instMonadRpcSession___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_logSnapContent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__4(lean_object*, lean_object*, size_t);
static lean_object* l_Lean_Server_FileWorker_logSnapContent___closed__4;
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadLiftIOEIOElabTaskError___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_allSnaps___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_new(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static size_t l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__2;
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_FileWorker_RpcSession_release___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Server_FileWorker_RpcSession_store___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_erase___at_Lean_Server_FileWorker_RpcSession_release___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_Server_FileWorker_RpcSession_release___spec__1(lean_object*, size_t);
lean_object* l_Std_PersistentHashMap_isUnaryNode___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check(lean_object*);
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__1;
static size_t l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__5___boxed(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadLiftIOEIOElabTaskError(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_FileWorker_RpcSession_store___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Server_FileWorker_RpcSession_release___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_release___boxed(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_FileWorker_RpcSession_store___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_Server_FileWorker_RpcSession_release___spec__1___boxed(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_Server_FileWorker_RpcSession_release___spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Server_FileWorker_RpcSession_release___spec__2(lean_object*, size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___rarg___lambda__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2(lean_object*, size_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instCoeErrorElabTaskError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Server_FileWorker_instMonadRpcSession___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_allSnaps(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_erase___at_Lean_Server_FileWorker_RpcSession_release___spec__4(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_FileWorker_RpcSession_store___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx_x27___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_FileWorker_RpcSession_release___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Server_FileWorker_instMonadRpcSession___spec__1(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_release(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_set___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_Server_FileWorker_RpcSession_release___spec__5(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Server_FileWorker_instMonadRpcSession___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__3(lean_object*, size_t, lean_object*);
lean_object* l_ByteArray_toUInt64LE_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__6(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__5(size_t, lean_object*);
static lean_object* _init_l_Lean_Server_FileWorker_logSnapContent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_logSnapContent___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_logSnapContent___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]: ```\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_logSnapContent___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n```");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_logSnapContent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_inc(x_4);
x_5 = l_Nat_repr(x_4);
x_6 = l_Lean_Server_FileWorker_logSnapContent___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_Server_FileWorker_logSnapContent___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_Server_Snapshots_Snapshot_endPos(x_1);
lean_dec(x_1);
lean_inc(x_10);
x_11 = l_Nat_repr(x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = l_Lean_Server_FileWorker_logSnapContent___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_10, x_16);
lean_dec(x_10);
x_18 = lean_string_utf8_extract(x_15, x_4, x_17);
lean_dec(x_17);
lean_dec(x_4);
x_19 = lean_string_append(x_14, x_18);
lean_dec(x_18);
x_20 = l_Lean_Server_FileWorker_logSnapContent___closed__4;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_21, x_3);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_logSnapContent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_logSnapContent(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instCoeErrorElabTaskError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadLiftIOEIOElabTaskError___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
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
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadLiftIOEIOElabTaskError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_instMonadLiftIOEIOElabTaskError___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_new(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_st_mk_ref(x_3, x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_CancelToken_check___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_CancelToken_check___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Server_FileWorker_CancelToken_check___rarg___lambda__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_set(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_st_ref_set(x_1, x_4, x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_set___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_CancelToken_set(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_allSnaps(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_allSnaps___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_EditableDocument_allSnaps(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(30000u);
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = 8;
x_3 = lean_io_get_random_bytes(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_ByteArray_toUInt64LE_x21(x_4);
x_7 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_8 = lean_io_mono_ms_now(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = 0;
x_12 = l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
x_13 = lean_nat_add(x_10, x_12);
lean_dec(x_10);
x_14 = l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1;
x_15 = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_usize(x_15, 2, x_11);
x_16 = lean_box_uint64(x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = 0;
x_21 = l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
x_22 = lean_nat_add(x_18, x_21);
lean_dec(x_18);
x_23 = l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1;
x_24 = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set_usize(x_24, 2, x_20);
x_25 = lean_box_uint64(x_7);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
return x_3;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_3);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_FileWorker_RpcSession_store___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; size_t x_10; lean_object* x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_11 = lean_array_fget(x_3, x_5);
x_12 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_hashRpcRef____x40_Lean_Data_Lsp_Extra___hyg_966_(x_10);
x_13 = lean_uint64_to_usize(x_12);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = 5;
x_17 = lean_usize_mul(x_16, x_15);
x_18 = lean_usize_shift_right(x_13, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2(x_6, x_18, x_1, x_10, x_11);
x_4 = lean_box(0);
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_FileWorker_RpcSession_store___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_box_usize(x_3);
x_13 = lean_array_push(x_5, x_12);
x_14 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_15 = lean_box_usize(x_3);
x_16 = lean_array_push(x_5, x_15);
x_17 = lean_array_push(x_6, x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_array_fget(x_5, x_2);
x_20 = lean_unbox_usize(x_19);
lean_dec(x_19);
x_21 = lean_usize_dec_eq(x_3, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_1, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_1, 0);
lean_dec(x_27);
x_28 = lean_box_usize(x_3);
x_29 = lean_array_fset(x_5, x_2, x_28);
x_30 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_30);
lean_ctor_set(x_1, 0, x_29);
return x_1;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_31 = lean_box_usize(x_3);
x_32 = lean_array_fset(x_5, x_2, x_31);
x_33 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2(lean_object* x_1, size_t x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_unbox_usize(x_19);
x_22 = lean_usize_dec_eq(x_4, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_15);
x_23 = lean_box_usize(x_4);
x_24 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_23, x_5);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_array_fset(x_17, x_12, x_25);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_20);
lean_dec(x_19);
x_27 = lean_box_usize(x_4);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_27);
x_28 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_unbox_usize(x_29);
x_32 = lean_usize_dec_eq(x_4, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box_usize(x_4);
x_34 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_29, x_30, x_33, x_5);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_array_fset(x_17, x_12, x_35);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_36);
return x_1;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_30);
lean_dec(x_29);
x_37 = lean_box_usize(x_4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
x_39 = lean_array_fset(x_17, x_12, x_38);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
}
}
case 1:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_usize_shift_right(x_2, x_9);
x_43 = lean_usize_add(x_3, x_8);
x_44 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2(x_41, x_42, x_43, x_4, x_5);
lean_ctor_set(x_15, 0, x_44);
x_45 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
else
{
lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
lean_dec(x_15);
x_47 = lean_usize_shift_right(x_2, x_9);
x_48 = lean_usize_add(x_3, x_8);
x_49 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2(x_46, x_47, x_48, x_4, x_5);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_array_fset(x_17, x_12, x_50);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_51);
return x_1;
}
}
default: 
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_box_usize(x_4);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_5);
x_54 = lean_array_fset(x_17, x_12, x_53);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_54);
return x_1;
}
}
}
}
else
{
lean_object* x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
x_56 = 1;
x_57 = 5;
x_58 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__2;
x_59 = lean_usize_land(x_2, x_58);
x_60 = lean_usize_to_nat(x_59);
x_61 = lean_array_get_size(x_55);
x_62 = lean_nat_dec_lt(x_60, x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_60);
lean_dec(x_5);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_55);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_array_fget(x_55, x_60);
x_65 = lean_box(0);
x_66 = lean_array_fset(x_55, x_60, x_65);
switch (lean_obj_tag(x_64)) {
case 0:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_69 = x_64;
} else {
 lean_dec_ref(x_64);
 x_69 = lean_box(0);
}
x_70 = lean_unbox_usize(x_67);
x_71 = lean_usize_dec_eq(x_4, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_69);
x_72 = lean_box_usize(x_4);
x_73 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_67, x_68, x_72, x_5);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_array_fset(x_66, x_60, x_74);
lean_dec(x_60);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_68);
lean_dec(x_67);
x_77 = lean_box_usize(x_4);
if (lean_is_scalar(x_69)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_69;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_5);
x_79 = lean_array_fset(x_66, x_60, x_78);
lean_dec(x_60);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
case 1:
{
lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_ctor_get(x_64, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_82 = x_64;
} else {
 lean_dec_ref(x_64);
 x_82 = lean_box(0);
}
x_83 = lean_usize_shift_right(x_2, x_57);
x_84 = lean_usize_add(x_3, x_56);
x_85 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2(x_81, x_83, x_84, x_4, x_5);
if (lean_is_scalar(x_82)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_82;
}
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_array_fset(x_66, x_60, x_86);
lean_dec(x_60);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
default: 
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_box_usize(x_4);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_5);
x_91 = lean_array_fset(x_66, x_60, x_90);
lean_dec(x_60);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
}
}
else
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_1);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; size_t x_96; uint8_t x_97; 
x_94 = lean_unsigned_to_nat(0u);
x_95 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_FileWorker_RpcSession_store___spec__4(x_1, x_94, x_4, x_5);
x_96 = 7;
x_97 = lean_usize_dec_le(x_96, x_3);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_95);
x_99 = lean_unsigned_to_nat(4u);
x_100 = lean_nat_dec_lt(x_98, x_99);
lean_dec(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_95, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_dec(x_95);
x_103 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__3;
x_104 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_FileWorker_RpcSession_store___spec__3(x_3, x_101, x_102, lean_box(0), x_94, x_103);
lean_dec(x_102);
lean_dec(x_101);
return x_104;
}
else
{
return x_95;
}
}
else
{
return x_95;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; uint8_t x_111; 
x_105 = lean_ctor_get(x_1, 0);
x_106 = lean_ctor_get(x_1, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_1);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_unsigned_to_nat(0u);
x_109 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_FileWorker_RpcSession_store___spec__4(x_107, x_108, x_4, x_5);
x_110 = 7;
x_111 = lean_usize_dec_le(x_110, x_3);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_109);
x_113 = lean_unsigned_to_nat(4u);
x_114 = lean_nat_dec_lt(x_112, x_113);
lean_dec(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
lean_dec(x_109);
x_117 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__3;
x_118 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_FileWorker_RpcSession_store___spec__3(x_3, x_115, x_116, lean_box(0), x_108, x_117);
lean_dec(x_116);
lean_dec(x_115);
return x_118;
}
else
{
return x_109;
}
}
else
{
return x_109;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Server_FileWorker_RpcSession_store___spec__1(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_hashRpcRef____x40_Lean_Data_Lsp_Extra___hyg_966_(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_hashRpcRef____x40_Lean_Data_Lsp_Extra___hyg_966_(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_store(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_usize(x_1, 2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
x_8 = l_Std_PersistentHashMap_insert___at_Lean_Server_FileWorker_RpcSession_store___spec__1(x_5, x_6, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_6, x_9);
lean_ctor_set(x_1, 0, x_8);
lean_ctor_set_usize(x_1, 2, x_10);
x_11 = lean_box_usize(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_1);
return x_12;
}
else
{
lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get_usize(x_1, 2);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_13);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
x_17 = l_Std_PersistentHashMap_insert___at_Lean_Server_FileWorker_RpcSession_store___spec__1(x_13, x_14, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_14, x_18);
x_20 = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set_usize(x_20, 2, x_19);
x_21 = lean_box_usize(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_FileWorker_RpcSession_store___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Server_FileWorker_RpcSession_store___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_FileWorker_RpcSession_store___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Server_FileWorker_RpcSession_store___spec__4(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2(x_1, x_6, x_7, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Server_FileWorker_RpcSession_store___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_insert___at_Lean_Server_FileWorker_RpcSession_store___spec__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_FileWorker_RpcSession_release___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; size_t x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_11 = lean_usize_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = 1;
return x_15;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Server_FileWorker_RpcSession_release___spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; size_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_13 = lean_usize_dec_eq(x_3, x_12);
return x_13;
}
case 1:
{
lean_object* x_14; size_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_usize_shift_right(x_2, x_5);
x_1 = x_14;
x_2 = x_15;
goto _start;
}
default: 
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_FileWorker_RpcSession_release___spec__3(x_18, x_19, lean_box(0), x_20, x_3);
lean_dec(x_19);
lean_dec(x_18);
return x_21;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_Server_FileWorker_RpcSession_release___spec__1(lean_object* x_1, size_t x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_hashRpcRef____x40_Lean_Data_Lsp_Extra___hyg_966_(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_containsAux___at_Lean_Server_FileWorker_RpcSession_release___spec__2(x_3, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_indexOfAux___at_Lean_Server_FileWorker_RpcSession_release___spec__6(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; size_t x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_9 = lean_usize_dec_eq(x_8, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_Server_FileWorker_RpcSession_release___spec__5(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; size_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_13 = lean_usize_dec_eq(x_3, x_12);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_4);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
x_19 = lean_array_set(x_4, x_8, x_9);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_19);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_23 = lean_array_set(x_4, x_8, x_9);
lean_dec(x_8);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
case 1:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_array_set(x_4, x_8, x_9);
x_31 = lean_usize_shift_right(x_2, x_5);
x_32 = l_Std_PersistentHashMap_eraseAux___at_Lean_Server_FileWorker_RpcSession_release___spec__5(x_29, x_31, x_3);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
lean_dec(x_30);
lean_free_object(x_10);
lean_dec(x_8);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = 0;
x_39 = lean_box(x_38);
lean_ctor_set(x_32, 1, x_39);
lean_ctor_set(x_32, 0, x_1);
return x_32;
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_32);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_1, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_dec(x_47);
x_48 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; 
lean_ctor_set(x_10, 0, x_46);
x_49 = lean_array_set(x_30, x_8, x_10);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_49);
x_50 = 1;
x_51 = lean_box(x_50);
lean_ctor_set(x_32, 1, x_51);
lean_ctor_set(x_32, 0, x_1);
return x_32;
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_free_object(x_32);
lean_dec(x_46);
lean_free_object(x_10);
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
lean_dec(x_48);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_array_set(x_30, x_8, x_56);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_57);
x_58 = 1;
x_59 = lean_box(x_58);
lean_ctor_set(x_52, 1, x_59);
lean_ctor_set(x_52, 0, x_1);
return x_52;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_52, 0);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_52);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_array_set(x_30, x_8, x_62);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_63);
x_64 = 1;
x_65 = lean_box(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_32, 0);
lean_inc(x_67);
lean_dec(x_32);
x_68 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
lean_ctor_set(x_10, 0, x_67);
x_69 = lean_array_set(x_30, x_8, x_10);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_69);
x_70 = 1;
x_71 = lean_box(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_67);
lean_free_object(x_10);
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
lean_dec(x_68);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_set(x_30, x_8, x_77);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_78);
x_79 = 1;
x_80 = lean_box(x_79);
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_1);
x_82 = lean_ctor_get(x_32, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_83 = x_32;
} else {
 lean_dec_ref(x_32);
 x_83 = lean_box(0);
}
x_84 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_ctor_set(x_10, 0, x_82);
x_85 = lean_array_set(x_30, x_8, x_10);
lean_dec(x_8);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = 1;
x_88 = lean_box(x_87);
if (lean_is_scalar(x_83)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_83;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_83);
lean_dec(x_82);
lean_free_object(x_10);
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
lean_dec(x_84);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_array_set(x_30, x_8, x_94);
lean_dec(x_8);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = 1;
x_98 = lean_box(x_97);
if (lean_is_scalar(x_93)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_93;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; size_t x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_100 = lean_ctor_get(x_10, 0);
lean_inc(x_100);
lean_dec(x_10);
x_101 = lean_array_set(x_4, x_8, x_9);
x_102 = lean_usize_shift_right(x_2, x_5);
x_103 = l_Std_PersistentHashMap_eraseAux___at_Lean_Server_FileWorker_RpcSession_release___spec__5(x_100, x_102, x_3);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_101);
lean_dec(x_8);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = 0;
x_108 = lean_box(x_107);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_110 = x_1;
} else {
 lean_dec_ref(x_1);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_103, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_112 = x_103;
} else {
 lean_dec_ref(x_103);
 x_112 = lean_box(0);
}
x_113 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_111);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_111);
x_115 = lean_array_set(x_101, x_8, x_114);
lean_dec(x_8);
if (lean_is_scalar(x_110)) {
 x_116 = lean_alloc_ctor(0, 1, 0);
} else {
 x_116 = x_110;
}
lean_ctor_set(x_116, 0, x_115);
x_117 = 1;
x_118 = lean_box(x_117);
if (lean_is_scalar(x_112)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_112;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_112);
lean_dec(x_111);
x_120 = lean_ctor_get(x_113, 0);
lean_inc(x_120);
lean_dec(x_113);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_array_set(x_101, x_8, x_124);
lean_dec(x_8);
if (lean_is_scalar(x_110)) {
 x_126 = lean_alloc_ctor(0, 1, 0);
} else {
 x_126 = x_110;
}
lean_ctor_set(x_126, 0, x_125);
x_127 = 1;
x_128 = lean_box(x_127);
if (lean_is_scalar(x_123)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_123;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
default: 
{
uint8_t x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_8);
lean_dec(x_4);
x_130 = 0;
x_131 = lean_box(x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_1, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_1, 1);
lean_inc(x_134);
x_135 = lean_unsigned_to_nat(0u);
x_136 = l_Array_indexOfAux___at_Lean_Server_FileWorker_RpcSession_release___spec__6(x_133, x_3, x_135);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_134);
lean_dec(x_133);
x_137 = 0;
x_138 = lean_box(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_1);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
else
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_1);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_1, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_1, 0);
lean_dec(x_142);
x_143 = lean_ctor_get(x_136, 0);
lean_inc(x_143);
lean_dec(x_136);
x_144 = l_Array_eraseIdx_x27___rarg(x_133, x_143);
x_145 = l_Array_eraseIdx_x27___rarg(x_134, x_143);
lean_dec(x_143);
lean_ctor_set(x_1, 1, x_145);
lean_ctor_set(x_1, 0, x_144);
x_146 = 1;
x_147 = lean_box(x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_1);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_1);
x_149 = lean_ctor_get(x_136, 0);
lean_inc(x_149);
lean_dec(x_136);
x_150 = l_Array_eraseIdx_x27___rarg(x_133, x_149);
x_151 = l_Array_eraseIdx_x27___rarg(x_134, x_149);
lean_dec(x_149);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = 1;
x_154 = lean_box(x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_erase___at_Lean_Server_FileWorker_RpcSession_release___spec__4(lean_object* x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_hashRpcRef____x40_Lean_Data_Lsp_Extra___hyg_966_(x_2);
x_7 = lean_uint64_to_usize(x_6);
x_8 = l_Std_PersistentHashMap_eraseAux___at_Lean_Server_FileWorker_RpcSession_release___spec__5(x_4, x_7, x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_5, x_13);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_hashRpcRef____x40_Lean_Data_Lsp_Extra___hyg_966_(x_2);
x_18 = lean_uint64_to_usize(x_17);
x_19 = l_Std_PersistentHashMap_eraseAux___at_Lean_Server_FileWorker_RpcSession_release___spec__5(x_15, x_18, x_2);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_16, x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_release(lean_object* x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Std_PersistentHashMap_contains___at_Lean_Server_FileWorker_RpcSession_release___spec__1(x_4, x_2);
x_6 = l_Std_PersistentHashMap_erase___at_Lean_Server_FileWorker_RpcSession_release___spec__4(x_4, x_2);
lean_ctor_set(x_1, 0, x_6);
x_7 = lean_box(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
lean_object* x_9; size_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get_usize(x_1, 2);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_9);
x_12 = l_Std_PersistentHashMap_contains___at_Lean_Server_FileWorker_RpcSession_release___spec__1(x_9, x_2);
x_13 = l_Std_PersistentHashMap_erase___at_Lean_Server_FileWorker_RpcSession_release___spec__4(x_9, x_2);
x_14 = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set_usize(x_14, 2, x_10);
x_15 = lean_box(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_FileWorker_RpcSession_release___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_7 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_FileWorker_RpcSession_release___spec__3(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Server_FileWorker_RpcSession_release___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_containsAux___at_Lean_Server_FileWorker_RpcSession_release___spec__2(x_1, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_Server_FileWorker_RpcSession_release___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_4 = l_Std_PersistentHashMap_contains___at_Lean_Server_FileWorker_RpcSession_release___spec__1(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_indexOfAux___at_Lean_Server_FileWorker_RpcSession_release___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Array_indexOfAux___at_Lean_Server_FileWorker_RpcSession_release___spec__6(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_eraseAux___at_Lean_Server_FileWorker_RpcSession_release___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_eraseAux___at_Lean_Server_FileWorker_RpcSession_release___spec__5(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_erase___at_Lean_Server_FileWorker_RpcSession_release___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_4 = l_Std_PersistentHashMap_erase___at_Lean_Server_FileWorker_RpcSession_release___spec__4(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_release___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_4 = l_Lean_Server_FileWorker_RpcSession_release(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
x_5 = l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
x_6 = lean_nat_add(x_1, x_5);
lean_ctor_set(x_2, 1, x_6);
return x_2;
}
else
{
lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get_usize(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
x_9 = l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
x_10 = lean_nat_add(x_1, x_9);
x_11 = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_usize(x_11, 2, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_RpcSession_keptAlive(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_io_mono_ms_now(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_nat_dec_le(x_6, x_5);
lean_dec(x_5);
x_8 = lean_box(x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_nat_dec_le(x_11, x_9);
lean_dec(x_9);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_RpcSession_hasExpired(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Server_FileWorker_instMonadRpcSession___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; size_t x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_11 = lean_usize_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Server_FileWorker_instMonadRpcSession___spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; size_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_14 = lean_usize_dec_eq(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_usize_shift_right(x_2, x_5);
x_1 = x_17;
x_2 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Std_PersistentHashMap_findAtAux___at_Lean_Server_FileWorker_instMonadRpcSession___spec__3(x_21, x_22, lean_box(0), x_23, x_3);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Server_FileWorker_instMonadRpcSession___spec__1(lean_object* x_1, size_t x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_hashRpcRef____x40_Lean_Data_Lsp_Extra___hyg_966_(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Server_FileWorker_instMonadRpcSession___spec__2(x_3, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_RpcSession_store(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__1), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Std_PersistentHashMap_find_x3f___at_Lean_Server_FileWorker_instMonadRpcSession___spec__1(x_6, x_2);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__4(lean_object* x_1, lean_object* x_2, size_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box_usize(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__3___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__5(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_RpcSession_release(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__6(lean_object* x_1, size_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box_usize(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__5___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__2), 3, 1);
lean_closure_set(x_3, 0, x_2);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__4___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__6___boxed), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_instMonadRpcSession___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Server_FileWorker_instMonadRpcSession___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_7 = l_Std_PersistentHashMap_findAtAux___at_Lean_Server_FileWorker_instMonadRpcSession___spec__3(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Server_FileWorker_instMonadRpcSession___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Server_FileWorker_instMonadRpcSession___spec__2(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Server_FileWorker_instMonadRpcSession___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_4 = l_Std_PersistentHashMap_find_x3f___at_Lean_Server_FileWorker_instMonadRpcSession___spec__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__3(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_5 = l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__4(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__5(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_4 = l_Lean_Server_FileWorker_instMonadRpcSession___rarg___lambda__6(x_1, x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Snapshots(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_AsyncList(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Snapshots(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_AsyncList(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_FileWorker_logSnapContent___closed__1 = _init_l_Lean_Server_FileWorker_logSnapContent___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_logSnapContent___closed__1);
l_Lean_Server_FileWorker_logSnapContent___closed__2 = _init_l_Lean_Server_FileWorker_logSnapContent___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_logSnapContent___closed__2);
l_Lean_Server_FileWorker_logSnapContent___closed__3 = _init_l_Lean_Server_FileWorker_logSnapContent___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_logSnapContent___closed__3);
l_Lean_Server_FileWorker_logSnapContent___closed__4 = _init_l_Lean_Server_FileWorker_logSnapContent___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_logSnapContent___closed__4);
l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs = _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs();
lean_mark_persistent(l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs);
l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__1 = _init_l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__1);
l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__2 = _init_l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__2();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__2);
l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__3 = _init_l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__3();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1___closed__3);
l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1 = _init_l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Server_FileWorker_RpcSession_new___spec__1);
l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__1();
l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__2 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__2();
l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__3 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__3();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Server_FileWorker_RpcSession_store___spec__2___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
