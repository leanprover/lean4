// Lean compiler output
// Module: Lean.Server.Rpc.RequestHandling
// Imports: Init Lean.Data.Lsp.Extra Lean.Server.Requests Lean.Server.Rpc.Basic
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
lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instHashableString;
uint8_t l_UInt64_decEq(uint64_t, uint64_t);
lean_object* l_Lean_Server_registerRpcCallHandler_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124_(lean_object*);
lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21_(lean_object*);
uint8_t l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__2;
static lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__1;
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__2;
uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerRpcCallHandler___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
static lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__1;
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Server_instMonadRpcSessionRequestM;
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__2;
lean_object* l_ReaderT_bind___at_Lean_Server_instMonadRpcSessionRequestM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__2;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
static lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__3;
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__1(lean_object*);
lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_rpcProcedures;
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__1;
size_t l_UInt64_toUSize(uint64_t);
lean_object* l_ExceptT_instMonadExceptT___rarg(lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__2;
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____closed__2;
lean_object* l_Except_map___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___closed__1;
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__1;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__2;
lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerRpcCallHandler___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2___closed__1;
lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcCallHandler___lambda__3___closed__3;
uint64_t l_Lean_Name_hash(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__1;
lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
lean_object* l_Lean_Server_RequestM_bindTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTask___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcCallHandler___closed__1;
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_EStateM_instMonadEStateM(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Server_registerRpcCallHandler_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__3;
static lean_object* l_Lean_Server_registerRpcCallHandler___lambda__2___closed__3;
uint8_t l_Std_PersistentHashMap_contains___at_Lean_Server_registerRpcCallHandler___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2(lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2___closed__2;
static lean_object* l_Lean_Server_registerRpcCallHandler___lambda__3___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_instBEq___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcCallHandler___lambda__3___closed__1;
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__3;
lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall_match__1(lean_object*);
lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcCallHandler___lambda__8___closed__1;
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l_Lean_Server_RequestM_asTask___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerRpcCallHandler___lambda__2___closed__2;
static lean_object* l_Lean_Server_registerRpcCallHandler___lambda__2___closed__1;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__1;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcCallParams____x40_Lean_Data_Lsp_Extra___hyg_1002_(lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_parseRequestParams___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_registerRpcCallHandler_match__2(lean_object*, lean_object*);
lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_contains___at_Lean_Server_registerRpcCallHandler___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEqName;
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__3;
x_3 = l_IO_mkRef___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("No RPC method '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' bound");
return x_1;
}
}
lean_object* l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Server_rpcProcedures;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_Name_instBEqName;
x_11 = l_Lean_instHashableName;
lean_inc(x_9);
x_12 = l_Std_PersistentHashMap_find_x3f___rarg(x_10, x_11, x_7, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = 1;
x_14 = l_Lean_Name_toString(x_9, x_13);
x_15 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = 2;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_5, 0, x_21);
return x_5;
}
else
{
lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_free_object(x_5);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_box_uint64(x_23);
x_26 = lean_apply_4(x_22, x_25, x_24, x_2, x_8);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = l_Lean_Name_instBEqName;
x_31 = l_Lean_instHashableName;
lean_inc(x_29);
x_32 = l_Std_PersistentHashMap_find_x3f___rarg(x_30, x_31, x_27, x_29);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = 1;
x_34 = l_Lean_Name_toString(x_29, x_33);
x_35 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__2;
x_38 = lean_string_append(x_36, x_37);
x_39 = 2;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_28);
return x_42;
}
else
{
lean_object* x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_29);
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_box_uint64(x_44);
x_47 = lean_apply_4(x_43, x_46, x_45, x_2, x_28);
return x_47;
}
}
}
}
static lean_object* _init_l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Cannot parse request params: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
lean_object* l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_inc(x_1);
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcCallParams____x40_Lean_Data_Lsp_Extra___hyg_1002_(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_4);
lean_dec(x_4);
x_11 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__3;
x_12 = lean_string_append(x_10, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_Json_compress(x_1);
x_17 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_append(x_20, x_15);
lean_dec(x_15);
x_22 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__1;
x_2 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2(x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_apply_3(x_1, x_11, x_3, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_21 = x_13;
} else {
 lean_dec_ref(x_13);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_12, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__2;
x_29 = l_Task_Priority_default;
x_30 = lean_task_map(x_28, x_27, x_29);
lean_ctor_set(x_13, 0, x_30);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__2;
x_33 = l_Task_Priority_default;
x_34 = lean_task_map(x_32, x_31, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_12, 0, x_35);
return x_12;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_dec(x_12);
x_37 = lean_ctor_get(x_13, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_38 = x_13;
} else {
 lean_dec_ref(x_13);
 x_38 = lean_box(0);
}
x_39 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__2;
x_40 = l_Task_Priority_default;
x_41 = lean_task_map(x_39, x_37, x_40);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_12);
if (x_44 == 0)
{
return x_12;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_12);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_decEq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__1;
x_2 = lean_alloc_closure((void*)(l_instBEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Server_requestHandlers;
x_7 = lean_st_ref_take(x_6, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
x_12 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__2;
x_13 = l_instHashableString;
x_14 = l_Std_PersistentHashMap_insert___rarg(x_12, x_13, x_8, x_2, x_11);
x_15 = lean_st_ref_set(x_6, x_14, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Failed to register LSP request handler for '");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("': already registered");
return x_1;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_5 = l_Lean_Server_requestHandlers;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_2);
x_10 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__1(x_8, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_6);
x_11 = lean_box(0);
x_12 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3(x_1, x_2, x_11, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_13 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__1;
x_14 = lean_string_append(x_13, x_2);
lean_dec(x_2);
x_15 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_17);
return x_6;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
lean_inc(x_2);
x_20 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerLspRequestHandler___spec__1(x_18, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3(x_1, x_2, x_21, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_23 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__1;
x_24 = lean_string_append(x_23, x_2);
lean_dec(x_2);
x_25 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("': only possible during initialization");
return x_1;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_initializing(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__1;
x_10 = lean_string_append(x_9, x_1);
lean_dec(x_1);
x_11 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__1;
x_16 = lean_string_append(x_15, x_1);
lean_dec(x_1);
x_17 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_box(0);
x_23 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4(x_2, x_1, x_22, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
return x_4;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("$/lean/rpc/call");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____closed__1;
x_3 = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____closed__2;
x_4 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Server_registerRpcCallHandler_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_registerRpcCallHandler_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcCallHandler_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Server_registerRpcCallHandler_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Server_registerRpcCallHandler_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcCallHandler_match__2___rarg), 3, 0);
return x_3;
}
}
uint8_t l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerRpcCallHandler___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_name_eq(x_5, x_9);
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
static size_t _init_l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = x_1 << x_2 % (sizeof(size_t) * 8);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2___closed__1;
x_3 = x_2 - x_1;
return x_3;
}
}
uint8_t l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2___closed__2;
x_7 = x_2 & x_6;
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
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5 % (sizeof(size_t) * 8);
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
x_20 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerRpcCallHandler___spec__3(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
uint8_t l_Std_PersistentHashMap_contains___at_Lean_Server_registerRpcCallHandler___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = (size_t)x_4;
x_6 = l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_registerRpcCallHandler___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" in RPC call '");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcCallHandler___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcCallHandler___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")'");
return x_1;
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Server_instMonadRpcSessionRequestM;
x_11 = lean_apply_6(x_9, lean_box(0), x_2, x_10, x_3, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_20 = x_12;
} else {
 lean_dec_ref(x_12);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__3;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_Server_registerRpcCallHandler___lambda__2___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = 1;
x_33 = l_Lean_Name_toString(x_4, x_32);
x_34 = lean_string_append(x_31, x_33);
lean_dec(x_33);
x_35 = l_Lean_Server_registerRpcCallHandler___lambda__2___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_unsigned_to_nat(80u);
x_38 = l_Lean_Json_pretty(x_5, x_37);
x_39 = lean_string_append(x_36, x_38);
lean_dec(x_38);
x_40 = l_Lean_Server_registerRpcCallHandler___lambda__2___closed__3;
x_41 = lean_string_append(x_39, x_40);
x_42 = 3;
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
lean_ctor_set(x_23, 0, x_43);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_44 = lean_ctor_get(x_23, 0);
lean_inc(x_44);
lean_dec(x_23);
x_45 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__3;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lean_Server_registerRpcCallHandler___lambda__2___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = 1;
x_50 = l_Lean_Name_toString(x_4, x_49);
x_51 = lean_string_append(x_48, x_50);
lean_dec(x_50);
x_52 = l_Lean_Server_registerRpcCallHandler___lambda__2___closed__2;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_unsigned_to_nat(80u);
x_55 = l_Lean_Json_pretty(x_5, x_54);
x_56 = lean_string_append(x_53, x_55);
lean_dec(x_55);
x_57 = l_Lean_Server_registerRpcCallHandler___lambda__2___closed__3;
x_58 = lean_string_append(x_56, x_57);
x_59 = 3;
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_11, 0, x_61);
return x_11;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_62 = lean_ctor_get(x_11, 1);
lean_inc(x_62);
lean_dec(x_11);
x_63 = lean_ctor_get(x_23, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_64 = x_23;
} else {
 lean_dec_ref(x_23);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__3;
x_66 = lean_string_append(x_65, x_63);
lean_dec(x_63);
x_67 = l_Lean_Server_registerRpcCallHandler___lambda__2___closed__1;
x_68 = lean_string_append(x_66, x_67);
x_69 = 1;
x_70 = l_Lean_Name_toString(x_4, x_69);
x_71 = lean_string_append(x_68, x_70);
lean_dec(x_70);
x_72 = l_Lean_Server_registerRpcCallHandler___lambda__2___closed__2;
x_73 = lean_string_append(x_71, x_72);
x_74 = lean_unsigned_to_nat(80u);
x_75 = l_Lean_Json_pretty(x_5, x_74);
x_76 = lean_string_append(x_73, x_75);
lean_dec(x_75);
x_77 = l_Lean_Server_registerRpcCallHandler___lambda__2___closed__3;
x_78 = lean_string_append(x_76, x_77);
x_79 = 3;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
if (lean_is_scalar(x_64)) {
 x_81 = lean_alloc_ctor(0, 1, 0);
} else {
 x_81 = x_64;
}
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_62);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_5);
lean_dec(x_4);
x_83 = !lean_is_exclusive(x_11);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_11, 0);
lean_dec(x_84);
x_85 = !lean_is_exclusive(x_23);
if (x_85 == 0)
{
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_23, 0);
lean_inc(x_86);
lean_dec(x_23);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_11, 0, x_87);
return x_11;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_11, 1);
lean_inc(x_88);
lean_dec(x_11);
x_89 = lean_ctor_get(x_23, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_90 = x_23;
} else {
 lean_dec_ref(x_23);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_5);
lean_dec(x_4);
x_93 = !lean_is_exclusive(x_11);
if (x_93 == 0)
{
return x_11;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_11, 0);
x_95 = lean_ctor_get(x_11, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_11);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerRpcCallHandler___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Outdated RPC session");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_registerRpcCallHandler___lambda__3___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 9;
x_2 = l_Lean_Server_registerRpcCallHandler___lambda__3___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_registerRpcCallHandler___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_registerRpcCallHandler___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint64_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint64_t x_11; uint8_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get_uint64(x_10, sizeof(void*)*1);
lean_dec(x_10);
x_12 = x_6 == x_11;
x_13 = l_instDecidableNot___rarg(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Server_registerRpcCallHandler___lambda__2(x_1, x_2, x_7, x_3, x_4, x_14, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Server_registerRpcCallHandler___lambda__3___closed__3;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_3(x_1, x_10, x_3, x_4);
return x_11;
}
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Server_instMonadRpcSessionRequestM;
x_15 = lean_apply_6(x_13, lean_box(0), x_2, x_14, x_12, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_24 = x_16;
} else {
 lean_dec_ref(x_16);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_15, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_apply_1(x_3, x_30);
lean_ctor_set(x_16, 0, x_31);
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_apply_1(x_3, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_15, 0, x_34);
return x_15;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_dec(x_15);
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_37 = x_16;
} else {
 lean_dec_ref(x_16);
 x_37 = lean_box(0);
}
x_38 = lean_apply_1(x_3, x_36);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_15);
if (x_41 == 0)
{
return x_15;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_15);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint64_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_ExceptT_instMonadExceptT___rarg(x_1);
x_13 = l_ReaderT_instMonadReaderT___rarg(x_12);
lean_inc(x_9);
x_14 = l_Lean_Server_parseRequestParams___rarg(x_2, x_9);
x_15 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcCallHandler___lambda__1___boxed), 3, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_box_uint64(x_8);
lean_inc(x_10);
lean_inc(x_13);
x_17 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcCallHandler___lambda__3___boxed), 9, 6);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_13);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_9);
lean_closure_set(x_17, 4, x_10);
lean_closure_set(x_17, 5, x_16);
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Server_instMonadRpcSessionRequestM___spec__2___rarg), 4, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_17);
lean_inc(x_10);
x_19 = l_Lean_Server_RequestM_asTask___rarg(x_18, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_28 = x_20;
} else {
 lean_dec_ref(x_20);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcCallHandler___lambda__4), 4, 1);
lean_closure_set(x_33, 0, x_5);
lean_inc(x_10);
x_34 = l_Lean_Server_RequestM_bindTask___rarg(x_32, x_33, x_10, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_34, 0, x_40);
return x_34;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_43 = x_35;
} else {
 lean_dec_ref(x_35);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_dec(x_34);
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
lean_dec(x_35);
x_48 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcCallHandler___lambda__5), 6, 3);
lean_closure_set(x_48, 0, x_6);
lean_closure_set(x_48, 1, x_13);
lean_closure_set(x_48, 2, x_7);
x_49 = l_Lean_Server_RequestM_mapTask___rarg(x_47, x_48, x_10, x_46);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_50 = !lean_is_exclusive(x_34);
if (x_50 == 0)
{
return x_34;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_34, 0);
x_52 = lean_ctor_get(x_34, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_34);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_19);
if (x_54 == 0)
{
return x_19;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_19, 0);
x_56 = lean_ctor_get(x_19, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_19);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Server_registerRpcCallHandler___lambda__6___boxed), 11, 7);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
lean_closure_set(x_10, 5, x_6);
lean_closure_set(x_10, 6, x_7);
x_11 = l_Lean_Server_rpcProcedures;
x_12 = lean_st_ref_take(x_11, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Name_instBEqName;
x_16 = l_Lean_instHashableName;
x_17 = l_Std_PersistentHashMap_insert___rarg(x_15, x_16, x_13, x_4, x_10);
x_18 = lean_st_ref_set(x_11, x_17, x_14);
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
static lean_object* _init_l_Lean_Server_registerRpcCallHandler___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Failed to register RPC call handler for '");
return x_1;
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_8);
x_10 = l_Lean_Server_rpcProcedures;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_4);
x_15 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerRpcCallHandler___spec__1(x_13, x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_11);
x_16 = lean_box(0);
x_17 = l_Lean_Server_registerRpcCallHandler___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_14);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = 1;
x_19 = l_Lean_Name_toString(x_4, x_18);
x_20 = l_Lean_Server_registerRpcCallHandler___lambda__8___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
lean_inc(x_4);
x_27 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerRpcCallHandler___spec__1(x_25, x_4);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Server_registerRpcCallHandler___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_28, x_26);
return x_29;
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = 1;
x_31 = l_Lean_Name_toString(x_4, x_30);
x_32 = l_Lean_Server_registerRpcCallHandler___lambda__8___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
return x_37;
}
}
}
}
static lean_object* _init_l_Lean_Server_registerRpcCallHandler___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_instMonadEStateM(lean_box(0), lean_box(0));
return x_1;
}
}
lean_object* l_Lean_Server_registerRpcCallHandler(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_io_initializing(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = l_Lean_Name_toString(x_1, x_17);
x_19 = l_Lean_Server_registerRpcCallHandler___lambda__8___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_23);
return x_12;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_25 = 1;
x_26 = l_Lean_Name_toString(x_1, x_25);
x_27 = l_Lean_Server_registerRpcCallHandler___lambda__8___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = l_Lean_Server_registerRpcCallHandler___closed__1;
x_35 = lean_box(0);
x_36 = l_Lean_Server_registerRpcCallHandler___lambda__8(x_34, x_6, x_5, x_1, x_10, x_8, x_9, x_35, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_12);
if (x_37 == 0)
{
return x_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerRpcCallHandler___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_PersistentHashMap_containsAtAux___at_Lean_Server_registerRpcCallHandler___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_contains___at_Lean_Server_registerRpcCallHandler___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_PersistentHashMap_contains___at_Lean_Server_registerRpcCallHandler___spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_registerRpcCallHandler___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Server_registerRpcCallHandler___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; lean_object* x_11; 
x_10 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_11 = l_Lean_Server_registerRpcCallHandler___lambda__3(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint64_t x_12; lean_object* x_13; 
x_12 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_13 = l_Lean_Server_registerRpcCallHandler___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Server_registerRpcCallHandler___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_registerRpcCallHandler___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Extra(lean_object*);
lean_object* initialize_Lean_Server_Requests(lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Server_Rpc_RequestHandling(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Requests(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__1 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__1();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__1);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__2 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__2();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__2);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__3 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__3();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21____closed__3);
res = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_21_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Server_rpcProcedures = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Server_rpcProcedures);
lean_dec_ref(res);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__1 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__1();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__1);
l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__2 = _init_l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__2();
lean_mark_persistent(l___private_Lean_Server_Rpc_RequestHandling_0__Lean_Server_handleRpcCall___closed__2);
l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__1 = _init_l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__1();
lean_mark_persistent(l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__1);
l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__2 = _init_l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__2();
lean_mark_persistent(l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__2);
l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__3 = _init_l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__3();
lean_mark_persistent(l_Lean_Server_parseRequestParams___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__2___closed__3);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__1);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__2 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__2___closed__2);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__1);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__2 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__2);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__3 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__3___closed__3);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__1);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__2 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___lambda__4___closed__2);
l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___closed__1 = _init_l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___closed__1();
lean_mark_persistent(l_Lean_Server_registerLspRequestHandler___at_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____spec__1___closed__1);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____closed__1 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____closed__1();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____closed__1);
l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____closed__2 = _init_l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____closed__2();
lean_mark_persistent(l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124____closed__2);
res = l_Lean_Server_initFn____x40_Lean_Server_Rpc_RequestHandling___hyg_124_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2___closed__1 = _init_l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2___closed__1();
l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2___closed__2 = _init_l_Std_PersistentHashMap_containsAux___at_Lean_Server_registerRpcCallHandler___spec__2___closed__2();
l_Lean_Server_registerRpcCallHandler___lambda__2___closed__1 = _init_l_Lean_Server_registerRpcCallHandler___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_registerRpcCallHandler___lambda__2___closed__1);
l_Lean_Server_registerRpcCallHandler___lambda__2___closed__2 = _init_l_Lean_Server_registerRpcCallHandler___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Server_registerRpcCallHandler___lambda__2___closed__2);
l_Lean_Server_registerRpcCallHandler___lambda__2___closed__3 = _init_l_Lean_Server_registerRpcCallHandler___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Server_registerRpcCallHandler___lambda__2___closed__3);
l_Lean_Server_registerRpcCallHandler___lambda__3___closed__1 = _init_l_Lean_Server_registerRpcCallHandler___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_registerRpcCallHandler___lambda__3___closed__1);
l_Lean_Server_registerRpcCallHandler___lambda__3___closed__2 = _init_l_Lean_Server_registerRpcCallHandler___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Server_registerRpcCallHandler___lambda__3___closed__2);
l_Lean_Server_registerRpcCallHandler___lambda__3___closed__3 = _init_l_Lean_Server_registerRpcCallHandler___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Server_registerRpcCallHandler___lambda__3___closed__3);
l_Lean_Server_registerRpcCallHandler___lambda__8___closed__1 = _init_l_Lean_Server_registerRpcCallHandler___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Server_registerRpcCallHandler___lambda__8___closed__1);
l_Lean_Server_registerRpcCallHandler___closed__1 = _init_l_Lean_Server_registerRpcCallHandler___closed__1();
lean_mark_persistent(l_Lean_Server_registerRpcCallHandler___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
