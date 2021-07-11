// Lean compiler output
// Module: Lean.Server.FileWorker.Utils
// Imports: Init Lean.Server.Utils Lean.Server.Snapshots Lean.Server.AsyncList
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
static lean_object* l_Lean_Server_FileWorker_logSnapContent___closed__3;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__12;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Server_FileWorker_logSnapContent___closed__2;
static lean_object* l_Lean_Server_FileWorker_logSnapContent___closed__1;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__13;
lean_object* l_Lean_Server_FileWorker_logSnapContent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_logSnapContent(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_logSnapContent___closed__4;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__2;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__21;
lean_object* l_Lean_Server_FileWorker_instInhabitedCancelToken;
lean_object* l_Lean_Server_FileWorker_CancelToken_new(lean_object*);
lean_object* l_Lean_Server_FileWorker_CancelToken_check___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__17;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__4;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__14;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__8;
lean_object* l_Lean_Server_FileWorker_CancelToken_check(lean_object*);
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__9;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__6;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__3;
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
static size_t l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__15;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__1;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__18;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__5;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__22;
lean_object* l_Lean_Server_FileWorker_CancelToken_check___rarg___lambda__1(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Server_FileWorker_instCoeErrorElabTaskError(lean_object*);
lean_object* l_Lean_Server_FileWorker_CancelToken_check___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__7;
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__20;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__10;
static uint32_t l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__11;
lean_object* l_Lean_Server_FileWorker_CancelToken_set___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__16;
lean_object* l_Lean_Server_FileWorker_CancelToken_set(lean_object*, lean_object*);
lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__19;
uint32_t lean_uint32_of_nat(lean_object*);
size_t lean_usize_of_nat(lean_object*);
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
lean_object* l_Lean_Server_FileWorker_logSnapContent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Server_FileWorker_logSnapContent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_logSnapContent(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_FileWorker_instCoeErrorElabTaskError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedCancelToken() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Server_FileWorker_CancelToken_new(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = l_IO_mkRef___rarg(x_3, x_1);
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
lean_object* l_Lean_Server_FileWorker_CancelToken_check___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
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
lean_object* l_Lean_Server_FileWorker_CancelToken_check___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Server_FileWorker_CancelToken_check(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_CancelToken_check___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Server_FileWorker_CancelToken_check___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Server_FileWorker_CancelToken_check___rarg___lambda__1(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Server_FileWorker_CancelToken_set(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Server_FileWorker_CancelToken_set___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_CancelToken_set(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__2;
x_2 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__5() {
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
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__10() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__6;
x_3 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__9;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static uint32_t _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__11() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__12() {
_start:
{
uint32_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__11;
x_2 = 0;
x_3 = lean_box(0);
x_4 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__1;
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
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__6;
x_2 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__10;
x_3 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__1;
x_4 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__12;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__15() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__14;
x_2 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__15;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__17() {
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
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__18() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__9;
x_3 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__16;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__19() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__16;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__13;
x_3 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__16;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__17;
x_6 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__18;
x_7 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__19;
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
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__5;
x_4 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__20;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(2);
x_2 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__4;
x_3 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__21;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__22;
return x_1;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Server_Utils(lean_object*);
lean_object* initialize_Lean_Server_Snapshots(lean_object*);
lean_object* initialize_Lean_Server_AsyncList(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Server_FileWorker_Utils(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Snapshots(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_AsyncList(lean_io_mk_world());
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
l_Lean_Server_FileWorker_instInhabitedCancelToken = _init_l_Lean_Server_FileWorker_instInhabitedCancelToken();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedCancelToken);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__1 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__1);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__2 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__2);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__3 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__3);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__4 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__4);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__5 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__5);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__6 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__6);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__7 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__7);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__8 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__8();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__8);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__9 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__9();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__9);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__10 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__10();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__10);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__11 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__11();
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__12 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__12();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__12);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__13 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__13();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__13);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__14 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__14();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__14);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__15 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__15();
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__16 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__16();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__16);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__17 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__17();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__17);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__18 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__18();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__18);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__19 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__19();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__19);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__20 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__20();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__20);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__21 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__21();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__21);
l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__22 = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__22();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument___closed__22);
l_Lean_Server_FileWorker_instInhabitedEditableDocument = _init_l_Lean_Server_FileWorker_instInhabitedEditableDocument();
lean_mark_persistent(l_Lean_Server_FileWorker_instInhabitedEditableDocument);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
