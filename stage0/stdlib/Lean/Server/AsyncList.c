// Lean compiler output
// Module: Lean.Server.AsyncList
// Imports: public import Lean.Server.ServerTask
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
static lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_IO_AsyncList_waitUntil___redArg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Server_ServerTask_hasFinished___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_cons_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_getFinishedPrefix___redArg___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00IO_AsyncList_ofList_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00IO_AsyncList_ofList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_getFinishedPrefix___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorElim___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx___redArg___boxed(lean_object*);
static lean_object* l_IO_AsyncList_instCoeList___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___redArg___lam__0___boxed(lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* lean_task_pure(lean_object*);
static lean_object* l_IO_AsyncList_waitUntil___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_delayed_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(lean_object*);
static lean_object* l_IO_AsyncList_waitAll___redArg___closed__0;
lean_object* l_IO_sleep(uint32_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00IO_AsyncList_ofList_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_nil_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(lean_object*, uint32_t);
LEAN_EXPORT uint8_t l_IO_AsyncList_waitAll___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_sleep___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00IO_AsyncList_ofList_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instCoeList(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout(lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_IO_AsyncList_waitFind_x3f___redArg___closed__0;
lean_object* l_Lean_Server_ServerTask_waitAny___redArg(lean_object*);
lean_object* l_Lean_Server_ServerTask_BaseIO_asTask___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitFind_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_cons_elim___redArg(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00IO_AsyncList_ofList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_AsyncList_nil_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(uint32_t);
lean_object* lean_io_wait(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_delayed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00IO_AsyncList_ofList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0;
lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_AsyncList_ctorIdx___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_AsyncList_ctorIdx___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_AsyncList_ctorIdx(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
default: 
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_IO_AsyncList_ctorElim___redArg(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_IO_AsyncList_ctorElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_cons_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_AsyncList_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_cons_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_AsyncList_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_delayed_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_AsyncList_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_delayed_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_AsyncList_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_nil_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_AsyncList_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_nil_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_AsyncList_ctorElim___redArg(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_instInhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00IO_AsyncList_ofList_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00IO_AsyncList_ofList_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00IO_AsyncList_ofList_spec__0_spec__0___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00IO_AsyncList_ofList_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_mk(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec_ref(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_4);
x_8 = 0;
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00IO_AsyncList_ofList_spec__0_spec__0___redArg(x_3, x_7, x_8, x_1);
lean_dec_ref(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(2);
x_3 = l_List_foldrTR___at___00IO_AsyncList_ofList_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_AsyncList_ofList___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00IO_AsyncList_ofList_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldrTR___at___00IO_AsyncList_ofList_spec__0___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00IO_AsyncList_ofList_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00IO_AsyncList_ofList_spec__0_spec__0___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00IO_AsyncList_ofList_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00IO_AsyncList_ofList_spec__0_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
return x_9;
}
}
static lean_object* _init_l_IO_AsyncList_instCoeList___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_ofList), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_instCoeList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_AsyncList_instCoeList___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
static lean_object* _init_l_IO_AsyncList_waitUntil___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_IO_AsyncList_waitUntil___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_AsyncList_waitUntil___redArg___closed__0;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_1);
lean_inc(x_4);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_free_object(x_2);
x_8 = lean_alloc_closure((void*)(l_IO_AsyncList_waitUntil___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_4);
x_9 = l_IO_AsyncList_waitUntil___redArg(x_1, x_5);
x_10 = l_Lean_Server_ServerTask_mapCheap___redArg(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_11 = lean_box(0);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_task_pure(x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
lean_inc_ref(x_1);
lean_inc(x_15);
x_17 = lean_apply_1(x_1, x_15);
x_18 = lean_unbox(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_alloc_closure((void*)(l_IO_AsyncList_waitUntil___redArg___lam__0), 2, 1);
lean_closure_set(x_19, 0, x_15);
x_20 = l_IO_AsyncList_waitUntil___redArg(x_1, x_16);
x_21 = l_Lean_Server_ServerTask_mapCheap___redArg(x_19, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_16);
lean_dec_ref(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_task_pure(x_25);
return x_26;
}
}
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_27);
lean_dec_ref(x_2);
x_28 = lean_alloc_closure((void*)(l_IO_AsyncList_waitUntil___redArg___lam__1), 2, 1);
lean_closure_set(x_28, 0, x_1);
x_29 = l_Lean_Server_ServerTask_bindCheap___redArg(x_27, x_28);
return x_29;
}
default: 
{
lean_object* x_30; 
lean_dec_ref(x_1);
x_30 = l_IO_AsyncList_waitUntil___redArg___closed__1;
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec_ref(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
lean_ctor_set_tag(x_2, 1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_task_pure(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_task_pure(x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = l_IO_AsyncList_waitUntil___redArg(x_1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_AsyncList_waitUntil___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_IO_AsyncList_waitAll___redArg___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_IO_AsyncList_waitAll___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_AsyncList_waitAll___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_waitAll___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_AsyncList_waitAll___redArg___closed__0;
x_3 = l_IO_AsyncList_waitUntil___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_AsyncList_waitAll___redArg(x_3);
return x_4;
}
}
static lean_object* _init_l_IO_AsyncList_waitFind_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_AsyncList_waitFind_x3f___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_AsyncList_waitFind_x3f___redArg___closed__0;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_3);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_task_pure(x_9);
return x_10;
}
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_2);
x_12 = lean_alloc_closure((void*)(l_IO_AsyncList_waitFind_x3f___redArg___lam__0), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_Server_ServerTask_bindCheap___redArg(x_11, x_12);
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec_ref(x_1);
x_14 = l_IO_AsyncList_waitFind_x3f___redArg___closed__1;
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec_ref(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_task_pure(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_task_pure(x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = l_IO_AsyncList_waitFind_x3f___redArg(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_AsyncList_waitFind_x3f___redArg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefix___redArg___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = lean_box(0);
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefix___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_AsyncList_getFinishedPrefix___redArg___closed__0;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_IO_AsyncList_getFinishedPrefix___redArg(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_5);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l_IO_AsyncList_getFinishedPrefix___redArg(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_14);
if (lean_is_scalar(x_16)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_16;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
case 1:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_1);
x_20 = l_Lean_Server_ServerTask_hasFinished___redArg(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_19);
x_21 = lean_box(0);
x_22 = lean_box(0);
x_23 = lean_box(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_io_wait(x_19);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_box(0);
lean_ctor_set_tag(x_26, 1);
x_29 = lean_box(x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_box(x_20);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
lean_dec_ref(x_26);
x_1 = x_38;
goto _start;
}
}
}
default: 
{
lean_object* x_40; 
x_40 = l_IO_AsyncList_getFinishedPrefix___redArg___closed__1;
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_AsyncList_getFinishedPrefix___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_AsyncList_getFinishedPrefix___redArg(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_AsyncList_getFinishedPrefix(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0;
x_8 = l_Lean_Server_ServerTask_mapCheap___redArg(x_7, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0;
x_13 = l_Lean_Server_ServerTask_mapCheap___redArg(x_12, x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(x_1, x_2, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(x_1, x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
case 1:
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_3);
x_22 = l_Lean_Server_ServerTask_hasFinished___redArg(x_21);
x_23 = 1;
if (x_22 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0;
x_25 = l_Lean_Server_ServerTask_mapCheap___redArg(x_24, x_21);
x_26 = lean_box(0);
lean_inc(x_1);
x_27 = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(x_1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_inc_ref(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_26);
x_30 = l_List_appendTR___redArg(x_28, x_29);
x_31 = l_Lean_Server_ServerTask_waitAny___redArg(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_31);
lean_dec_ref(x_2);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_box(x_22);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec_ref(x_31);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_ctor_set_tag(x_36, 1);
x_38 = lean_box(x_23);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_box(x_23);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_26);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_36, 0);
lean_inc(x_46);
lean_dec_ref(x_36);
x_3 = x_46;
goto _start;
}
}
}
else
{
lean_object* x_48; 
x_48 = lean_io_wait(x_21);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_box(0);
lean_ctor_set_tag(x_48, 1);
x_51 = lean_box(x_23);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_box(x_23);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_48, 0);
lean_inc(x_60);
lean_dec_ref(x_48);
x_3 = x_60;
goto _start;
}
}
}
default: 
{
lean_object* x_62; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_62 = l_IO_AsyncList_getFinishedPrefix___redArg___closed__1;
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_sleep(x_1);
x_4 = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0;
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(x_3);
return x_4;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
uint32_t x_5; uint8_t x_6; 
x_5 = 0;
x_6 = lean_uint32_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_box_uint32(x_2);
x_8 = lean_alloc_closure((void*)(l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(x_8);
x_10 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(x_3, x_9, x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0;
x_12 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(x_3, x_11, x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint32_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_8 = l_IO_AsyncList_getFinishedPrefixWithTimeout(x_1, x_2, x_3, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT uint8_t l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Server_ServerTask_hasFinished___redArg(x_4);
if (x_6 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(x_1);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(lean_object* x_1, uint32_t x_2) {
_start:
{
uint32_t x_4; uint8_t x_5; 
x_4 = 0;
x_5 = lean_uint32_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_List_isEmpty___redArg(x_1);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box_uint32(x_2);
x_9 = lean_alloc_closure((void*)(l_IO_sleep___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = l_Lean_Server_ServerTask_waitAny___redArg(x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = l_IO_sleep(x_2);
x_15 = lean_box(0);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; 
x_5 = lean_io_mono_ms_now();
lean_inc(x_3);
x_6 = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(x_1, x_2, x_3);
x_7 = lean_io_mono_ms_now();
x_8 = lean_nat_sub(x_7, x_5);
lean_dec(x_5);
lean_dec(x_7);
x_9 = lean_uint32_to_nat(x_2);
x_10 = lean_nat_sub(x_9, x_8);
lean_dec(x_8);
lean_dec(x_9);
x_11 = lean_uint32_of_nat(x_10);
lean_dec(x_10);
x_12 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(x_3, x_11);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint32_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint32_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_8 = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency(x_1, x_2, x_3, x_7, x_5);
return x_8;
}
}
lean_object* initialize_Lean_Server_ServerTask(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_AsyncList(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_ServerTask(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_IO_AsyncList_instCoeList___closed__0 = _init_l_IO_AsyncList_instCoeList___closed__0();
lean_mark_persistent(l_IO_AsyncList_instCoeList___closed__0);
l_IO_AsyncList_waitUntil___redArg___closed__0 = _init_l_IO_AsyncList_waitUntil___redArg___closed__0();
lean_mark_persistent(l_IO_AsyncList_waitUntil___redArg___closed__0);
l_IO_AsyncList_waitUntil___redArg___closed__1 = _init_l_IO_AsyncList_waitUntil___redArg___closed__1();
lean_mark_persistent(l_IO_AsyncList_waitUntil___redArg___closed__1);
l_IO_AsyncList_waitAll___redArg___closed__0 = _init_l_IO_AsyncList_waitAll___redArg___closed__0();
lean_mark_persistent(l_IO_AsyncList_waitAll___redArg___closed__0);
l_IO_AsyncList_waitFind_x3f___redArg___closed__0 = _init_l_IO_AsyncList_waitFind_x3f___redArg___closed__0();
lean_mark_persistent(l_IO_AsyncList_waitFind_x3f___redArg___closed__0);
l_IO_AsyncList_waitFind_x3f___redArg___closed__1 = _init_l_IO_AsyncList_waitFind_x3f___redArg___closed__1();
lean_mark_persistent(l_IO_AsyncList_waitFind_x3f___redArg___closed__1);
l_IO_AsyncList_getFinishedPrefix___redArg___closed__0 = _init_l_IO_AsyncList_getFinishedPrefix___redArg___closed__0();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefix___redArg___closed__0);
l_IO_AsyncList_getFinishedPrefix___redArg___closed__1 = _init_l_IO_AsyncList_getFinishedPrefix___redArg___closed__1();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefix___redArg___closed__1);
l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0 = _init_l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0();
lean_mark_persistent(l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0);
l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0 = _init_l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0);
l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0 = _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0);
l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0 = _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
