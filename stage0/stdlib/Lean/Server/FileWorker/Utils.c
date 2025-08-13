// Lean compiler output
// Module: Lean.Server.FileWorker.Utils
// Imports: Lean.Language.Lean.Types Lean.Server.Utils Lean.Server.Snapshots Lean.Server.AsyncList Lean.Server.Rpc.Basic
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
static lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0;
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
lean_object* lean_task_pure(lean_object*);
static lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(lean_object*);
static lean_object* l_Lean_Server_FileWorker_RpcSession_new___closed__1;
static lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object*, lean_object*);
uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_RpcSession_new___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_io_get_random_bytes(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_6 = x_4;
} else {
 lean_dec_ref(x_4);
 x_6 = lean_box(0);
}
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_5);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; 
x_12 = lean_box(2);
x_8 = x_12;
goto block_11;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_14, 3);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go), 1, 0);
x_17 = l_Lean_Server_ServerTask_bindCheap___redArg(x_15, x_16);
lean_ctor_set(x_3, 0, x_17);
x_8 = x_3;
goto block_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_18, 3);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go), 1, 0);
x_21 = l_Lean_Server_ServerTask_bindCheap___redArg(x_19, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_8 = x_22;
goto block_11;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
if (lean_is_scalar(x_6)) {
 x_9 = lean_alloc_ctor(0, 2, 0);
} else {
 x_9 = x_6;
}
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_7);
lean_dec_ref(x_3);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lam__0), 4, 3);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
lean_closure_set(x_8, 2, x_6);
x_9 = l_Lean_Server_ServerTask_mapCheap___redArg(x_8, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(2);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get(x_3, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; 
lean_free_object(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_14);
lean_dec_ref(x_12);
lean_ctor_set(x_3, 2, x_13);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
x_15 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2;
x_16 = l_Lean_Server_ServerTask_bindCheap___redArg(x_14, x_15);
lean_ctor_set(x_5, 0, x_16);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 0, x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_10);
x_18 = lean_task_pure(x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_19, 3);
lean_inc_ref(x_21);
lean_dec_ref(x_19);
lean_ctor_set(x_3, 2, x_20);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
x_22 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2;
x_23 = l_Lean_Server_ServerTask_bindCheap___redArg(x_21, x_22);
lean_ctor_set(x_5, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_5);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_task_pure(x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_31);
lean_dec_ref(x_28);
lean_ctor_set(x_3, 2, x_29);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
x_32 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2;
x_33 = l_Lean_Server_ServerTask_bindCheap___redArg(x_31, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_30)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_30;
}
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_task_pure(x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_3, 2);
lean_inc(x_38);
lean_dec(x_3);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_39 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1;
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 3);
lean_inc_ref(x_45);
lean_dec_ref(x_42);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_2);
lean_ctor_set(x_46, 2, x_43);
x_47 = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2;
x_48 = l_Lean_Server_ServerTask_bindCheap___redArg(x_45, x_47);
if (lean_is_scalar(x_41)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_41;
}
lean_ctor_set(x_49, 0, x_48);
if (lean_is_scalar(x_44)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_44;
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_task_pure(x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_9);
lean_dec_ref(x_6);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_8);
x_11 = l_Lean_Server_ServerTask_bindCheap___redArg(x_9, x_10);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 3);
lean_inc_ref(x_16);
lean_dec_ref(x_13);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0), 3, 2);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_15);
x_18 = l_Lean_Server_ServerTask_bindCheap___redArg(x_16, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore___private__1(lean_object* x_1) {
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
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
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
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_RpcSession_new___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Server_FileWorker_RpcSession_new___closed__1;
x_3 = lean_alloc_ctor(0, 2, sizeof(size_t)*1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set_usize(x_3, 2, x_1);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_io_mono_ms_now(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_ByteArray_toUInt64LE_x21(x_4);
lean_dec(x_4);
x_10 = l_Lean_Server_FileWorker_RpcSession_new___closed__2;
x_11 = lean_unsigned_to_nat(30000u);
x_12 = lean_nat_add(x_8, x_11);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box_uint64(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
else
{
lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = l_ByteArray_toUInt64LE_x21(x_4);
lean_dec(x_4);
x_19 = l_Lean_Server_FileWorker_RpcSession_new___closed__2;
x_20 = lean_unsigned_to_nat(30000u);
x_21 = lean_nat_add(x_16, x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box_uint64(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
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
x_5 = lean_unsigned_to_nat(30000u);
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
x_8 = lean_unsigned_to_nat(30000u);
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
lean_dec_ref(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Language_Lean_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Snapshots(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_AsyncList(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Language_Lean_Types(builtin, lean_io_mk_world());
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
l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0 = _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0);
l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1 = _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1);
l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2 = _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2);
l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs = _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs();
lean_mark_persistent(l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs);
l_Lean_Server_FileWorker_RpcSession_new___closed__0 = _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_RpcSession_new___closed__0);
l_Lean_Server_FileWorker_RpcSession_new___closed__1 = _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_RpcSession_new___closed__1);
l_Lean_Server_FileWorker_RpcSession_new___closed__2 = _init_l_Lean_Server_FileWorker_RpcSession_new___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_RpcSession_new___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
