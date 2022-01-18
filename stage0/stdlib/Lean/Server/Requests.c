// Lean compiler output
// Module: Lean.Server.Requests
// Imports: Init Lean.DeclarationRange Lean.Data.Json Lean.Data.Lsp Lean.Server.FileSource Lean.Server.FileWorker.Utils Lean.Server.Rpc.Basic
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
static lean_object* l_Lean_Server_handleLspRequest___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instHashableString;
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Server_handleLspRequest___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRequestM___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTask(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_RequestM_asTask___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Server_instInhabitedRequestM___closed__2;
static lean_object* l_Lean_Server_RequestError_methodNotFound___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRequestM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Server_parseRequestParams___rarg___closed__1;
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__1;
static lean_object* l_Lean_Server_instInhabitedRequestM___closed__1;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
static lean_object* l_Lean_Server_instInhabitedRequestM___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Server_instInhabitedRequestM___closed__4;
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2(lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502_(lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map___rarg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_RequestM_mapTask___spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerLspRequestHandler___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_parseRequestParams___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__5;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap(lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_requestHandlers;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTask(lean_object*, lean_object*);
static lean_object* l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRequestM(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerLspRequestHandler___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTask___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_instCoeErrorRequestError(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_fileChanged;
static lean_object* l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1;
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___boxed(lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
static lean_object* l_Lean_Server_parseRequestParams___rarg___closed__3;
static lean_object* l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_RequestM_asTask___spec__1(lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_RequestError_fileChanged___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams(lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_RequestM_mapTask___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2___closed__1;
static lean_object* l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__2___closed__1;
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Server_RequestError_fileChanged___closed__1;
lean_object* l_EIO_toBaseIO___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound___boxed(lean_object*);
static lean_object* l_Lean_Server_RequestError_methodNotFound___closed__1;
static lean_object* l_Lean_Server_registerLspRequestHandler___closed__1;
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___rarg(lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTask___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Server_RequestError_fileChanged___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("File changed.");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestError_fileChanged___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 7;
x_2 = l_Lean_Server_RequestError_fileChanged___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_RequestError_fileChanged() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_RequestError_fileChanged___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestError_methodNotFound___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("No request handler found for '");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_RequestError_methodNotFound___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = l_Lean_Server_RequestError_methodNotFound___closed__1;
x_3 = lean_string_append(x_2, x_1);
x_4 = l_Lean_Server_RequestError_methodNotFound___closed__2;
x_5 = lean_string_append(x_3, x_4);
x_6 = 2;
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_methodNotFound___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_RequestError_methodNotFound(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_instCoeErrorRequestError(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_io_error_to_string(x_1);
x_3 = 4;
x_4 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(0);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestError_toLspResponseError___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestError_toLspResponseError(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_parseRequestParams___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Cannot parse request params: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_parseRequestParams___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_parseRequestParams___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Json_compress(x_2);
x_7 = l_Lean_Server_parseRequestParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_parseRequestParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_parseRequestParams___rarg___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = 0;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = l_Lean_Json_compress(x_2);
x_18 = l_Lean_Server_parseRequestParams___rarg___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_Server_parseRequestParams___rarg___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_16);
lean_dec(x_16);
x_23 = l_Lean_Server_parseRequestParams___rarg___closed__3;
x_24 = lean_string_append(x_22, x_23);
x_25 = 0;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
return x_3;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
lean_dec(x_3);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_parseRequestParams___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRequestM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedRequestM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("executing Inhabited instance?!");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedRequestM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_instInhabitedRequestM___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedRequestM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_instInhabitedRequestM___closed__2;
x_2 = lean_io_error_to_string(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedRequestM___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 4;
x_2 = l_Lean_Server_instInhabitedRequestM___closed__3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRequestM(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_instInhabitedRequestM___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_Server_instInhabitedRequestM___lambda__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedRequestM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_instInhabitedRequestM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
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
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_io_error_to_string(x_10);
x_12 = 4;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_io_error_to_string(x_14);
x_17 = 4;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_instMonadLiftIORequestM___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_instMonadLiftIORequestM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_instMonadLiftIORequestM___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_readDoc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_RequestM_readDoc(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_RequestM_asTask___spec__1___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_RequestM_asTask___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_liftExcept___at_Lean_Server_RequestM_asTask___spec__1___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_apply_1(x_1, x_2);
x_5 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Task_Priority_default;
x_7 = lean_io_as_task(x_5, x_6, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_closure((void*)(l_liftExcept___at_Lean_Server_RequestM_asTask___spec__1___rarg), 1, 0);
x_11 = lean_task_map(x_10, x_9, x_6);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_closure((void*)(l_liftExcept___at_Lean_Server_RequestM_asTask___spec__1___rarg), 1, 0);
x_15 = lean_task_map(x_14, x_12, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_asTask(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_asTask___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_RequestM_mapTask___spec__1___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_RequestM_mapTask___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_liftExcept___at_Lean_Server_RequestM_mapTask___spec__1___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTask___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_3, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTask___rarg___lambda__1), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Task_Priority_default;
x_7 = lean_io_map_task(x_5, x_1, x_6, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_closure((void*)(l_liftExcept___at_Lean_Server_RequestM_mapTask___spec__1___rarg), 1, 0);
x_11 = lean_task_map(x_10, x_9, x_6);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_closure((void*)(l_liftExcept___at_Lean_Server_RequestM_mapTask___spec__1___rarg), 1, 0);
x_15 = lean_task_map(x_14, x_12, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_mapTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_mapTask___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTask___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_3, x_2, x_4);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_task_pure(x_12);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_task_pure(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTask___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTask___rarg___lambda__1), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = l_Task_Priority_default;
x_7 = lean_io_bind_task(x_1, x_5, x_6, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_bindTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_bindTask___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
return x_8;
}
}
}
static lean_object* _init_l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2___closed__1;
x_3 = l_Task_Priority_default;
x_4 = lean_task_map(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_task_pure(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_task_pure(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1(x_1, x_13, x_3);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__2___closed__1;
x_18 = l_Task_Priority_default;
x_19 = lean_task_map(x_17, x_16, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__2___closed__1;
x_23 = l_Task_Priority_default;
x_24 = lean_task_map(x_22, x_20, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___closed__1;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_4);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_task_pure(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_closure((void*)(l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__2), 3, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = l_Task_Priority_default;
x_16 = lean_io_bind_task(x_13, x_14, x_15, x_3);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2___lambda__1), 1, 0);
x_20 = lean_task_map(x_19, x_18, x_15);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2___lambda__1), 1, 0);
x_24 = lean_task_map(x_23, x_21, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
default: 
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___closed__2;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_1);
x_7 = l_Lean_Server_RequestError_fileChanged;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
case 1:
{
lean_object* x_9; 
x_9 = lean_apply_2(x_1, x_4, x_5);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_io_error_to_string(x_10);
x_12 = 4;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_apply_2(x_1, x_4, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_apply_3(x_2, x_17, x_4, x_5);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1(x_2, x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnap___rarg___lambda__1), 5, 2);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_4);
x_12 = l_Lean_Server_RequestM_mapTask___rarg(x_9, x_11, x_5, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_withWaitFindSnap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_RequestM_withWaitFindSnap___rarg), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_decEq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__1;
x_2 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__5;
x_3 = lean_st_mk_ref(x_2, x_1);
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
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerLspRequestHandler___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_string_dec_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
static size_t _init_l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_string_dec_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_usize_shift_right(x_2, x_5);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerLspRequestHandler___spec__4(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_string_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_parseRequestParams___rarg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_apply_1(x_2, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Server_parseRequestParams___rarg(x_1, x_4);
x_8 = l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg(x_7, x_5, x_6);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_3(x_2, x_9, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_14, 0, x_3);
x_15 = l_Task_Priority_default;
x_16 = lean_task_map(x_14, x_13, x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_19, 0, x_3);
x_20 = l_Task_Priority_default;
x_21 = lean_task_map(x_19, x_17, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___lambda__2), 6, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_4);
x_10 = l_Lean_Server_requestHandlers;
x_11 = lean_st_ref_take(x_10, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
x_15 = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__2;
x_16 = l_instHashableString;
x_17 = l_Std_PersistentHashMap_insert___rarg(x_15, x_16, x_12, x_5, x_14);
x_18 = lean_st_ref_set(x_10, x_17, x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Failed to register LSP request handler for '");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("': already registered");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
x_8 = l_Lean_Server_requestHandlers;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_5);
x_13 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__2(x_11, x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_9);
x_14 = lean_box(0);
x_15 = l_Lean_Server_registerLspRequestHandler___lambda__3(x_1, x_2, x_3, x_4, x_5, x_14, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1;
x_17 = lean_string_append(x_16, x_5);
lean_dec(x_5);
x_18 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
lean_inc(x_5);
x_23 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__2(x_21, x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Server_registerLspRequestHandler___lambda__3(x_1, x_2, x_3, x_4, x_5, x_24, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1;
x_27 = lean_string_append(x_26, x_5);
lean_dec(x_5);
x_28 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("': only possible during initialization");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_io_initializing(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1;
x_15 = lean_string_append(x_14, x_1);
lean_dec(x_1);
x_16 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1;
x_21 = lean_string_append(x_20, x_1);
lean_dec(x_1);
x_22 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_box(0);
x_28 = l_Lean_Server_registerLspRequestHandler___lambda__4(x_3, x_4, x_7, x_6, x_1, x_27, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_liftExcept___at_Lean_Server_registerLspRequestHandler___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerLspRequestHandler___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerLspRequestHandler___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerLspRequestHandler___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_registerLspRequestHandler___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_lookupLspRequestHandler(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Server_requestHandlers;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__2;
x_8 = l_instHashableString;
x_9 = l_Std_PersistentHashMap_find_x3f___rarg(x_7, x_8, x_6, x_1);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__2;
x_13 = l_instHashableString;
x_14 = l_Std_PersistentHashMap_find_x3f___rarg(x_12, x_13, x_10, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Failed to parse original LSP response for `");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("` when chaining: ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_apply_1(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1;
x_12 = lean_string_append(x_11, x_2);
x_13 = l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_10);
lean_dec(x_10);
x_16 = l_Lean_Server_parseRequestParams___rarg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_io_error_to_string(x_18);
x_20 = 4;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
x_23 = l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1;
x_24 = lean_string_append(x_23, x_2);
x_25 = l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_22);
lean_dec(x_22);
x_28 = l_Lean_Server_parseRequestParams___rarg___closed__3;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_io_error_to_string(x_30);
x_32 = 4;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_8, 0);
lean_inc(x_36);
lean_dec(x_8);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
x_11 = lean_apply_3(x_10, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___lambda__1___boxed), 3, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
x_15 = l_Task_Priority_default;
x_16 = lean_task_map(x_14, x_12, x_15);
x_17 = l_Lean_Server_parseRequestParams___rarg(x_4, x_7);
x_18 = l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg(x_17, x_8, x_13);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_apply_4(x_5, x_19, x_16, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_24, 0, x_6);
x_25 = lean_task_map(x_24, x_23, x_15);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_28, 0, x_6);
x_29 = lean_task_map(x_28, x_26, x_15);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
static lean_object* _init_l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Failed to chain LSP request handler for '");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("': no initial handler registered");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = l_Lean_Server_lookupLspRequestHandler(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1;
x_13 = lean_string_append(x_12, x_1);
lean_dec(x_1);
x_14 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1;
x_19 = lean_string_append(x_18, x_1);
lean_dec(x_1);
x_20 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_ctor_get(x_9, 0);
lean_inc(x_25);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l_Lean_Server_chainLspRequestHandler___lambda__2), 9, 6);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_1);
lean_closure_set(x_26, 3, x_3);
lean_closure_set(x_26, 4, x_4);
lean_closure_set(x_26, 5, x_5);
x_27 = l_Lean_Server_requestHandlers;
x_28 = lean_st_ref_take(x_27, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_25, 1);
lean_dec(x_32);
lean_ctor_set(x_25, 1, x_26);
x_33 = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__2;
x_34 = l_instHashableString;
x_35 = l_Std_PersistentHashMap_insert___rarg(x_33, x_34, x_29, x_1, x_25);
x_36 = lean_st_ref_set(x_27, x_35, x_30);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
lean_dec(x_25);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_26);
x_43 = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__2;
x_44 = l_instHashableString;
x_45 = l_Std_PersistentHashMap_insert___rarg(x_43, x_44, x_29, x_1, x_42);
x_46 = lean_st_ref_set(x_27, x_45, x_30);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_io_initializing(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1;
x_15 = lean_string_append(x_14, x_1);
lean_dec(x_1);
x_16 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1;
x_21 = lean_string_append(x_20, x_1);
lean_dec(x_1);
x_22 = l_Lean_Server_registerLspRequestHandler___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_box(0);
x_28 = l_Lean_Server_chainLspRequestHandler___lambda__3(x_1, x_5, x_3, x_7, x_6, x_27, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_liftExcept___at_Lean_Server_chainLspRequestHandler___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_chainLspRequestHandler___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_chainLspRequestHandler___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_chainLspRequestHandler___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_routeLspRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = l_Lean_Server_lookupLspRequestHandler(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = l_Lean_Server_RequestError_methodNotFound(x_1);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_Server_RequestError_methodNotFound(x_1);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_apply_1(x_17, x_2);
lean_ctor_set(x_4, 0, x_18);
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_1(x_21, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Server_handleLspRequest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("internal server error: request '");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_handleLspRequest___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' routed through watchdog but unknown in worker; are both using the same plugins?");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_handleLspRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_5 = l_Lean_Server_lookupLspRequestHandler(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_Server_handleLspRequest___closed__1;
x_10 = lean_string_append(x_9, x_1);
lean_dec(x_1);
x_11 = l_Lean_Server_handleLspRequest___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_io_error_to_string(x_13);
x_15 = 4;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = l_Lean_Server_handleLspRequest___closed__1;
x_19 = lean_string_append(x_18, x_1);
lean_dec(x_1);
x_20 = l_Lean_Server_handleLspRequest___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_io_error_to_string(x_22);
x_24 = 4;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_apply_3(x_29, x_2, x_3, x_27);
return x_30;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_DeclarationRange(lean_object*);
lean_object* initialize_Lean_Data_Json(lean_object*);
lean_object* initialize_Lean_Data_Lsp(lean_object*);
lean_object* initialize_Lean_Server_FileSource(lean_object*);
lean_object* initialize_Lean_Server_FileWorker_Utils(lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Requests(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DeclarationRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileSource(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_Utils(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_RequestError_fileChanged___closed__1 = _init_l_Lean_Server_RequestError_fileChanged___closed__1();
lean_mark_persistent(l_Lean_Server_RequestError_fileChanged___closed__1);
l_Lean_Server_RequestError_fileChanged___closed__2 = _init_l_Lean_Server_RequestError_fileChanged___closed__2();
lean_mark_persistent(l_Lean_Server_RequestError_fileChanged___closed__2);
l_Lean_Server_RequestError_fileChanged = _init_l_Lean_Server_RequestError_fileChanged();
lean_mark_persistent(l_Lean_Server_RequestError_fileChanged);
l_Lean_Server_RequestError_methodNotFound___closed__1 = _init_l_Lean_Server_RequestError_methodNotFound___closed__1();
lean_mark_persistent(l_Lean_Server_RequestError_methodNotFound___closed__1);
l_Lean_Server_RequestError_methodNotFound___closed__2 = _init_l_Lean_Server_RequestError_methodNotFound___closed__2();
lean_mark_persistent(l_Lean_Server_RequestError_methodNotFound___closed__2);
l_Lean_Server_parseRequestParams___rarg___closed__1 = _init_l_Lean_Server_parseRequestParams___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_parseRequestParams___rarg___closed__1);
l_Lean_Server_parseRequestParams___rarg___closed__2 = _init_l_Lean_Server_parseRequestParams___rarg___closed__2();
lean_mark_persistent(l_Lean_Server_parseRequestParams___rarg___closed__2);
l_Lean_Server_parseRequestParams___rarg___closed__3 = _init_l_Lean_Server_parseRequestParams___rarg___closed__3();
lean_mark_persistent(l_Lean_Server_parseRequestParams___rarg___closed__3);
l_Lean_Server_instInhabitedRequestM___closed__1 = _init_l_Lean_Server_instInhabitedRequestM___closed__1();
lean_mark_persistent(l_Lean_Server_instInhabitedRequestM___closed__1);
l_Lean_Server_instInhabitedRequestM___closed__2 = _init_l_Lean_Server_instInhabitedRequestM___closed__2();
lean_mark_persistent(l_Lean_Server_instInhabitedRequestM___closed__2);
l_Lean_Server_instInhabitedRequestM___closed__3 = _init_l_Lean_Server_instInhabitedRequestM___closed__3();
lean_mark_persistent(l_Lean_Server_instInhabitedRequestM___closed__3);
l_Lean_Server_instInhabitedRequestM___closed__4 = _init_l_Lean_Server_instInhabitedRequestM___closed__4();
lean_mark_persistent(l_Lean_Server_instInhabitedRequestM___closed__4);
l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2___closed__1 = _init_l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2___closed__1();
lean_mark_persistent(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___at_Lean_Server_RequestM_withWaitFindSnap___spec__2___closed__1);
l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__2___closed__1 = _init_l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___lambda__2___closed__1);
l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___closed__1 = _init_l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___closed__1();
lean_mark_persistent(l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___closed__1);
l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___closed__2 = _init_l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___closed__2();
lean_mark_persistent(l_IO_AsyncList_waitFind_x3f___at_Lean_Server_RequestM_withWaitFindSnap___spec__1___closed__2);
l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__1 = _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__1();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__1);
l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__2 = _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__2();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__2);
l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__3 = _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__3();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__3);
l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__4 = _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__4();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__4);
l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__5 = _init_l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__5();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502____closed__5);
res = l_Lean_Server_initFn____x40_Lean_Server_Requests___hyg_502_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_requestHandlers = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_requestHandlers);
lean_dec_ref(res);
l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__1 = _init_l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__1();
l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2 = _init_l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerLspRequestHandler___spec__3___closed__2();
l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___lambda__4___closed__1);
l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2 = _init_l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___lambda__4___closed__2);
l_Lean_Server_registerLspRequestHandler___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___closed__1);
l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1 = _init_l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_chainLspRequestHandler___lambda__1___closed__1);
l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2 = _init_l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_chainLspRequestHandler___lambda__1___closed__2);
l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1 = _init_l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_chainLspRequestHandler___lambda__3___closed__1);
l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2 = _init_l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Server_chainLspRequestHandler___lambda__3___closed__2);
l_Lean_Server_handleLspRequest___closed__1 = _init_l_Lean_Server_handleLspRequest___closed__1();
lean_mark_persistent(l_Lean_Server_handleLspRequest___closed__1);
l_Lean_Server_handleLspRequest___closed__2 = _init_l_Lean_Server_handleLspRequest___closed__2();
lean_mark_persistent(l_Lean_Server_handleLspRequest___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
