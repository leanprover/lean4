// Lean compiler output
// Module: Lean.Server.FileWorker.Utils
// Imports: Lean.Language.Lean Lean.Server.Utils Lean.Server.Snapshots Lean.Server.AsyncList Lean.Server.Rpc.Basic
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_RpcSession_new___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___closed__2;
static lean_object* l_Lean_Server_FileWorker_RpcSession_new___closed__3;
lean_object* lean_io_mono_ms_now(lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_cmdSnaps___default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(lean_object*);
static lean_object* l_Lean_Server_FileWorker_RpcSession_new___closed__1;
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object*, lean_object*);
lean_object* l_ByteArray_toUInt64LE_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier___boxed(lean_object*);
static lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_dec(x_5);
lean_inc(x_4);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(2);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___closed__1;
x_16 = l_Task_Priority_default;
x_17 = 0;
x_18 = lean_task_bind(x_14, x_15, x_16, x_17);
lean_ctor_set(x_6, 0, x_18);
lean_ctor_set(x_1, 0, x_9);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___closed__1;
x_23 = l_Task_Priority_default;
x_24 = 0;
x_25 = lean_task_bind(x_21, x_22, x_23, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_9);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_28);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_box(2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___closed__1;
x_41 = l_Task_Priority_default;
x_42 = 0;
x_43 = lean_task_bind(x_39, x_40, x_41, x_42);
if (lean_is_scalar(x_38)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_38;
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 4);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Task_Priority_default;
x_7 = 0;
x_8 = lean_task_map(x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(2);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___closed__1;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___closed__2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___closed__1;
x_15 = l_Task_Priority_default;
x_16 = 0;
x_17 = lean_task_bind(x_13, x_14, x_15, x_16);
lean_ctor_set(x_4, 0, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_4);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_task_pure(x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___closed__1;
x_29 = l_Task_Priority_default;
x_30 = 0;
x_31 = lean_task_bind(x_27, x_28, x_29, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_task_pure(x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_5);
x_9 = l_Task_Priority_default;
x_10 = 0;
x_11 = lean_task_bind(x_7, x_8, x_9, x_10);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___boxed), 3, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_12);
x_16 = l_Task_Priority_default;
x_17 = 0;
x_18 = lean_task_bind(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_cmdSnaps___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_1);
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
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_RpcSession_new___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Server_FileWorker_RpcSession_new___closed__2;
x_3 = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_usize(x_3, 1, x_1);
return x_3;
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
lean_dec(x_4);
x_7 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_8 = lean_io_mono_ms_now(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_10);
x_13 = l_Lean_Server_FileWorker_RpcSession_new___closed__3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_box_uint64(x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
x_20 = lean_nat_add(x_17, x_19);
lean_dec(x_17);
x_21 = l_Lean_Server_FileWorker_RpcSession_new___closed__3;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_box_uint64(x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
return x_3;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_3);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
x_9 = lean_nat_add(x_1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
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
lean_object* initialize_Lean_Language_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Snapshots(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_AsyncList(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Language_Lean(builtin, lean_io_mk_world());
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
l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___closed__1 = _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lambda__1___closed__1);
l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___closed__1 = _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___closed__1);
l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___closed__2 = _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lambda__1___closed__2);
l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs = _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs();
lean_mark_persistent(l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs);
l_Lean_Server_FileWorker_RpcSession_new___closed__1 = _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_RpcSession_new___closed__1);
l_Lean_Server_FileWorker_RpcSession_new___closed__2 = _init_l_Lean_Server_FileWorker_RpcSession_new___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_RpcSession_new___closed__2);
l_Lean_Server_FileWorker_RpcSession_new___closed__3 = _init_l_Lean_Server_FileWorker_RpcSession_new___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_RpcSession_new___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
