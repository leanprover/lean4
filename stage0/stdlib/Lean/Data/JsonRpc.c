// Lean compiler output
// Module: Lean.Data.JsonRpc
// Imports: Init Init.Control Init.System.IO Std.Data.RBTree Lean.Data.Json
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
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___boxed(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__10;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__1;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__15;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__8;
lean_object* l_IO_FS_Stream_writeMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__5___boxed(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__32;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_aux2___boxed(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__4;
lean_object* l_IO_FS_Stream_readRequestAs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__20;
lean_object* l_IO_FS_Stream_readRequestAs_match__1(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readMessage___closed__1;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__9;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__25;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__37;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__29;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__6_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__11;
lean_object* l_IO_FS_Stream_readRequestAs_match__2(lean_object*);
lean_object* l_Lean_JsonRpc_aux1(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__42;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__6_match__1(lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__5;
lean_object* l_IO_FS_Stream_writeResponse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__3;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__8___boxed(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__18;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__2;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__43;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__30;
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readNotificationAs_match__3(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__6___boxed(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__22;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__41;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__13;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__14;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__8_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__10;
lean_object* l_IO_FS_Stream_readMessage_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__33;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__6;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__24;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__7;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__3(lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Int_zero___closed__1;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__4;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__10;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__8;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__17;
lean_object* l_IO_FS_Stream_readRequestAs___closed__7;
lean_object* l_IO_FS_Stream_readRequestAs___closed__3;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__34;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__13;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_IO_FS_Stream_readRequestAs___closed__5;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__23;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__5;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__28;
lean_object* l_IO_FS_Stream_writeMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__38;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__21;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__19;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__8(lean_object*);
lean_object* l_IO_FS_Stream_readNotificationAs_match__2(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___boxed(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__1;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__44;
lean_object* l_Lean_JsonRpc_aux3___boxed(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readNotificationAs_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readNotificationAs___closed__2;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__40;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__2;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__7;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__6;
lean_object* l_IO_FS_Stream_readNotificationAs___closed__1;
lean_object* l_IO_FS_Stream_readNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_aux2(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__6(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__27;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__9;
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__3;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__5(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__35;
lean_object* l_IO_FS_Stream_readMessage_match__1(lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs___closed__6;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__39;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux4___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_aux4___boxed(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__5_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs_match__3(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__4(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux4___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__5_match__1(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__36;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__5;
lean_object* l_Lean_JsonRpc_aux3(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__3;
lean_object* l_IO_FS_Stream_readRequestAs___closed__2;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__2;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__31;
lean_object* l_IO_FS_Stream_readRequestAs___closed__1;
lean_object* l_Lean_JsonRpc_aux1___boxed(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__11;
lean_object* l_IO_FS_Stream_readNotificationAs_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs___closed__4;
uint8_t l_Lean_JsonNumber_decEq(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7(lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__26;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__1;
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2_match__1(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___boxed(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__9;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__12;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1_match__1(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__16;
lean_object* l_IO_FS_Stream_writeJson(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__12;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7_match__1(lean_object*);
lean_object* l_IO_FS_Stream_writeResponse(lean_object*);
lean_object* l_IO_FS_Stream_readNotificationAs_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__8_match__1(lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readNotificationAs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__11;
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2(uint8_t);
lean_object* l_Lean_JsonRpc_aux4(lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__8;
lean_object* l_IO_FS_Stream_readMessage___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
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
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_zero___closed__1;
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__1;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_zero___closed__1;
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__4;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_zero___closed__1;
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__7;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_zero___closed__1;
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__10;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__11;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_zero___closed__1;
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__13;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__14;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32099u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_zero___closed__1;
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__16;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__17;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_zero___closed__1;
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__19;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__20;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_zero___closed__1;
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__22;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__23;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_zero___closed__1;
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__25;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__26;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_zero___closed__1;
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__28;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__29;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_zero___closed__1;
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__31;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__32;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__34() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 10;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__35() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 9;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__36() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 8;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__37() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 7;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__38() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 6;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__39() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 5;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__40() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 4;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__41() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__42() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__43() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__44() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__3;
x_4 = l_Lean_JsonNumber_decEq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__6;
x_6 = l_Lean_JsonNumber_decEq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__9;
x_8 = l_Lean_JsonNumber_decEq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__12;
x_10 = l_Lean_JsonNumber_decEq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__15;
x_12 = l_Lean_JsonNumber_decEq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__18;
x_14 = l_Lean_JsonNumber_decEq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__21;
x_16 = l_Lean_JsonNumber_decEq(x_2, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__24;
x_18 = l_Lean_JsonNumber_decEq(x_2, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__27;
x_20 = l_Lean_JsonNumber_decEq(x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__30;
x_22 = l_Lean_JsonNumber_decEq(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__33;
x_24 = l_Lean_JsonNumber_decEq(x_2, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_box(0);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__34;
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__35;
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__36;
return x_28;
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__37;
return x_29;
}
}
else
{
lean_object* x_30; 
x_30 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__38;
return x_30;
}
}
else
{
lean_object* x_31; 
x_31 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__39;
return x_31;
}
}
else
{
lean_object* x_32; 
x_32 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__40;
return x_32;
}
}
else
{
lean_object* x_33; 
x_33 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__41;
return x_33;
}
}
else
{
lean_object* x_34; 
x_34 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__42;
return x_34;
}
}
else
{
lean_object* x_35; 
x_35 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__43;
return x_35;
}
}
else
{
lean_object* x_36; 
x_36 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__44;
return x_36;
}
}
else
{
lean_object* x_37; 
x_37 = lean_box(0);
return x_37;
}
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_2, x_13);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_3, x_15);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = lean_apply_1(x_4, x_17);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_apply_1(x_5, x_19);
return x_20;
}
case 4:
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_apply_1(x_6, x_21);
return x_22;
}
case 5:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_apply_1(x_7, x_23);
return x_24;
}
case 6:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = lean_apply_1(x_8, x_25);
return x_26;
}
case 7:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_apply_1(x_9, x_27);
return x_28;
}
case 8:
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_apply_1(x_10, x_29);
return x_30;
}
case 9:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = lean_apply_1(x_11, x_31);
return x_32;
}
default: 
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_apply_1(x_12, x_33);
return x_34;
}
}
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2_match__1___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2_match__1___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__18;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__21;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__24;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__27;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__30;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__33;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__2;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__3;
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__4;
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__5;
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__6;
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__7;
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__8;
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__9;
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__10;
return x_11;
}
default: 
{
lean_object* x_12; 
x_12 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__11;
return x_12;
}
}
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2(x_2);
return x_3;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__5_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_apply_1(x_4, x_1);
return x_9;
}
}
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__5_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__5_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__5(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
case 3:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__5(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__6_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__6_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__6_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__6(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__6(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_2, x_6, x_7, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_3, x_10, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_4, x_13, x_14);
return x_15;
}
default: 
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_box(x_17);
x_21 = lean_apply_4(x_5, x_16, x_20, x_18, x_19);
return x_21;
}
}
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
}
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("2.0");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("jsonrpc");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__3;
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("method");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("params");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("id");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("message");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("data");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("code");
return x_1;
}
}
static lean_object* _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("error");
return x_1;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__5;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6;
x_11 = l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__1(x_10, x_4);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
x_17 = l_List_append___rarg(x_16, x_11);
x_18 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Json_mkObj(x_19);
return x_20;
}
case 1:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_9);
x_26 = l_List_append___rarg(x_25, x_11);
x_27 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Json_mkObj(x_28);
return x_29;
}
default: 
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__8;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
x_32 = l_List_append___rarg(x_31, x_11);
x_33 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Json_mkObj(x_34);
return x_35;
}
}
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__5;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6;
x_42 = l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__1(x_41, x_37);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Json_mkObj(x_45);
return x_46;
}
case 2:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_ctor_get(x_1, 1);
x_49 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__9;
lean_inc(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
switch (lean_obj_tag(x_47)) {
case 0:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
x_58 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Json_mkObj(x_59);
return x_60;
}
case 1:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_52);
x_66 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_Json_mkObj(x_67);
return x_68;
}
default: 
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__8;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_52);
x_71 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Json_mkObj(x_72);
return x_73;
}
}
}
default: 
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_74 = lean_ctor_get(x_1, 0);
x_75 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_76 = lean_ctor_get(x_1, 1);
x_77 = lean_ctor_get(x_1, 2);
lean_inc(x_76);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_76);
x_79 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__10;
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__11;
x_84 = l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__2(x_83, x_77);
switch (lean_obj_tag(x_74)) {
case 0:
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_74, 0);
lean_inc(x_114);
x_115 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_85 = x_115;
goto block_113;
}
case 1:
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_74, 0);
lean_inc(x_116);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_85 = x_117;
goto block_113;
}
default: 
{
lean_object* x_118; 
x_118 = lean_box(0);
x_85 = x_118;
goto block_113;
}
}
block_113:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
switch (x_75) {
case 0:
{
lean_object* x_102; 
x_102 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__1;
x_88 = x_102;
goto block_101;
}
case 1:
{
lean_object* x_103; 
x_103 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__2;
x_88 = x_103;
goto block_101;
}
case 2:
{
lean_object* x_104; 
x_104 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__3;
x_88 = x_104;
goto block_101;
}
case 3:
{
lean_object* x_105; 
x_105 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__4;
x_88 = x_105;
goto block_101;
}
case 4:
{
lean_object* x_106; 
x_106 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__5;
x_88 = x_106;
goto block_101;
}
case 5:
{
lean_object* x_107; 
x_107 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__6;
x_88 = x_107;
goto block_101;
}
case 6:
{
lean_object* x_108; 
x_108 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__7;
x_88 = x_108;
goto block_101;
}
case 7:
{
lean_object* x_109; 
x_109 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__8;
x_88 = x_109;
goto block_101;
}
case 8:
{
lean_object* x_110; 
x_110 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__9;
x_88 = x_110;
goto block_101;
}
case 9:
{
lean_object* x_111; 
x_111 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__10;
x_88 = x_111;
goto block_101;
}
default: 
{
lean_object* x_112; 
x_112 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__11;
x_88 = x_112;
goto block_101;
}
}
block_101:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_89 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__12;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_82);
x_92 = l_List_append___rarg(x_91, x_84);
x_93 = l_Lean_Json_mkObj(x_92);
x_94 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__13;
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_81);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Lean_Json_mkObj(x_99);
return x_100;
}
}
}
}
}
}
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_6)) {
case 2:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
case 3:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
default: 
{
lean_object* x_11; 
lean_free_object(x_3);
lean_dec(x_6);
x_11 = lean_box(0);
return x_11;
}
}
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
switch (lean_obj_tag(x_12)) {
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
default: 
{
lean_object* x_19; 
lean_dec(x_12);
x_19 = lean_box(0);
return x_19;
}
}
}
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Json_getStr_x3f(x_5);
lean_dec(x_5);
return x_6;
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_6)) {
case 4:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
case 5:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
default: 
{
lean_object* x_11; 
lean_free_object(x_3);
lean_dec(x_6);
x_11 = lean_box(0);
return x_11;
}
}
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
switch (lean_obj_tag(x_12)) {
case 4:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
case 5:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
default: 
{
lean_object* x_19; 
lean_dec(x_12);
x_19 = lean_box(0);
return x_19;
}
}
}
}
}
}
lean_object* l_Lean_JsonRpc_aux1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__5;
x_7 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__2(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6;
x_12 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__3(x_1, x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6;
x_16 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__3(x_1, x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_JsonRpc_aux1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_aux1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_aux2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__5;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__2(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6;
x_8 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__3(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6;
x_12 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__3(x_1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_JsonRpc_aux2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_aux2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_aux3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__9;
x_7 = l_Lean_Json_getObjVal_x3f(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
lean_object* l_Lean_JsonRpc_aux3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_aux3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux4___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__3;
x_8 = l_Lean_JsonNumber_decEq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__6;
x_10 = l_Lean_JsonNumber_decEq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__9;
x_12 = l_Lean_JsonNumber_decEq(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__12;
x_14 = l_Lean_JsonNumber_decEq(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__15;
x_16 = l_Lean_JsonNumber_decEq(x_6, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__18;
x_18 = l_Lean_JsonNumber_decEq(x_6, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__21;
x_20 = l_Lean_JsonNumber_decEq(x_6, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__24;
x_22 = l_Lean_JsonNumber_decEq(x_6, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__27;
x_24 = l_Lean_JsonNumber_decEq(x_6, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__30;
x_26 = l_Lean_JsonNumber_decEq(x_6, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__33;
x_28 = l_Lean_JsonNumber_decEq(x_6, x_27);
lean_dec(x_6);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__34;
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_6);
x_31 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__35;
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_6);
x_32 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__36;
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_6);
x_33 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__37;
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_6);
x_34 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__38;
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_6);
x_35 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__39;
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_6);
x_36 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__40;
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_6);
x_37 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__41;
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_6);
x_38 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__42;
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_6);
x_39 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__43;
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_6);
x_40 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__44;
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_5);
x_41 = lean_box(0);
return x_41;
}
}
}
}
lean_object* l_Lean_JsonRpc_aux4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__13;
x_7 = l_Lean_Json_getObjVal_x3f(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__12;
x_11 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux4___spec__1(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__10;
x_15 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux1___spec__2(x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__11;
x_20 = l_Lean_Json_getObjVal_x3f(x_9, x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_unbox(x_13);
lean_dec(x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_22);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__11;
x_25 = l_Lean_Json_getObjVal_x3f(x_9, x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_unbox(x_13);
lean_dec(x_13);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
}
}
}
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux4___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_aux4___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_JsonRpc_aux4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_aux4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__8_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__8_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__8_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__8(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__3;
x_3 = l_Lean_Json_getObjVal_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 3)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__1;
x_8 = lean_string_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_JsonRpc_aux1(x_1);
x_11 = l_Lean_JsonRpc_aux2(x_1);
x_12 = l_Lean_JsonRpc_aux3(x_1);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; 
x_13 = l_Lean_JsonRpc_aux4(x_1);
return x_13;
}
else
{
return x_10;
}
}
else
{
if (lean_obj_tag(x_10) == 0)
{
return x_11;
}
else
{
lean_dec(x_11);
return x_10;
}
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_10) == 0)
{
return x_12;
}
else
{
lean_dec(x_12);
return x_10;
}
}
else
{
lean_dec(x_12);
if (lean_obj_tag(x_10) == 0)
{
return x_11;
}
else
{
lean_dec(x_11);
return x_10;
}
}
}
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
x_14 = lean_box(0);
return x_14;
}
}
}
}
lean_object* l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__8(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_IO_FS_Stream_readMessage_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
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
lean_object* l_IO_FS_Stream_readMessage_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_readMessage_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("JSON '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readMessage___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' did not have the format of a JSON-RPC message");
return x_1;
}
}
lean_object* l_IO_FS_Stream_readMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readJson(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_19 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__3;
x_20 = l_Lean_Json_getObjVal_x3f(x_5, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
x_8 = x_21;
goto block_18;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 3)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__1;
x_25 = lean_string_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_box(0);
x_8 = x_26;
goto block_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Lean_JsonRpc_aux1(x_5);
x_28 = l_Lean_JsonRpc_aux2(x_5);
x_29 = l_Lean_JsonRpc_aux3(x_5);
if (lean_obj_tag(x_29) == 0)
{
if (lean_obj_tag(x_28) == 0)
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_30; 
x_30 = l_Lean_JsonRpc_aux4(x_5);
x_8 = x_30;
goto block_18;
}
else
{
x_8 = x_27;
goto block_18;
}
}
else
{
if (lean_obj_tag(x_27) == 0)
{
x_8 = x_28;
goto block_18;
}
else
{
lean_dec(x_28);
x_8 = x_27;
goto block_18;
}
}
}
else
{
if (lean_obj_tag(x_28) == 0)
{
if (lean_obj_tag(x_27) == 0)
{
x_8 = x_29;
goto block_18;
}
else
{
lean_dec(x_29);
x_8 = x_27;
goto block_18;
}
}
else
{
lean_dec(x_29);
if (lean_obj_tag(x_27) == 0)
{
x_8 = x_28;
goto block_18;
}
else
{
lean_dec(x_28);
x_8 = x_27;
goto block_18;
}
}
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_22);
x_31 = lean_box(0);
x_8 = x_31;
goto block_18;
}
}
block_18:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lean_Json_compress(x_5);
x_10 = l_IO_FS_Stream_readMessage___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_IO_FS_Stream_readMessage___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
if (lean_is_scalar(x_7)) {
 x_15 = lean_alloc_ctor(1, 2, 0);
} else {
 x_15 = x_7;
 lean_ctor_set_tag(x_15, 1);
}
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
if (lean_is_scalar(x_7)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_7;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
return x_4;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_IO_FS_Stream_readMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_readMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_FS_Stream_readRequestAs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
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
lean_object* l_IO_FS_Stream_readRequestAs_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Stream_readRequestAs_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_FS_Stream_readRequestAs_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
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
lean_object* l_IO_FS_Stream_readRequestAs_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_readRequestAs_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_readRequestAs_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_IO_FS_Stream_readRequestAs_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_readRequestAs_match__3___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected method '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', got method '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected lack of param for method '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected param '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' for method '");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected request, got other type of message");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___closed__6;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_IO_FS_Stream_readRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readMessage(x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_string_dec_eq(x_12, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
x_15 = l_IO_FS_Stream_readRequestAs___closed__1;
x_16 = lean_string_append(x_15, x_3);
x_17 = l_IO_FS_Stream_readRequestAs___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_12);
lean_dec(x_12);
x_20 = l_Char_HasRepr___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
else
{
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
lean_dec(x_5);
x_23 = l_IO_FS_Stream_readRequestAs___closed__3;
x_24 = lean_string_append(x_23, x_3);
x_25 = l_Char_HasRepr___closed__1;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_27);
return x_7;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
lean_dec(x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_inc(x_30);
x_31 = lean_apply_1(x_5, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_11);
x_32 = l_Lean_Json_compress(x_30);
x_33 = l_IO_FS_Stream_readRequestAs___closed__4;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_IO_FS_Stream_readRequestAs___closed__5;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_36, x_3);
x_38 = l_Char_HasRepr___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_40);
return x_7;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_30);
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_11);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_7, 0, x_42);
return x_7;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_28, 0);
lean_inc(x_43);
lean_dec(x_28);
x_44 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_44);
x_45 = lean_apply_1(x_5, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_11);
x_46 = l_Lean_Json_compress(x_44);
x_47 = l_IO_FS_Stream_readRequestAs___closed__4;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_IO_FS_Stream_readRequestAs___closed__5;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_string_append(x_50, x_3);
x_52 = l_Char_HasRepr___closed__1;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_54);
return x_7;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_44);
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
lean_dec(x_45);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_11);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_7, 0, x_56);
return x_7;
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_7, 1);
lean_inc(x_57);
lean_dec(x_7);
x_58 = lean_ctor_get(x_8, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_8, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_8, 2);
lean_inc(x_60);
lean_dec(x_8);
x_61 = lean_string_dec_eq(x_59, x_3);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_5);
x_62 = l_IO_FS_Stream_readRequestAs___closed__1;
x_63 = lean_string_append(x_62, x_3);
x_64 = l_IO_FS_Stream_readRequestAs___closed__2;
x_65 = lean_string_append(x_63, x_64);
x_66 = lean_string_append(x_65, x_59);
lean_dec(x_59);
x_67 = l_Char_HasRepr___closed__1;
x_68 = lean_string_append(x_66, x_67);
x_69 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_57);
return x_70;
}
else
{
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_58);
lean_dec(x_5);
x_71 = l_IO_FS_Stream_readRequestAs___closed__3;
x_72 = lean_string_append(x_71, x_3);
x_73 = l_Char_HasRepr___closed__1;
x_74 = lean_string_append(x_72, x_73);
x_75 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_57);
return x_76;
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_60, 0);
lean_inc(x_77);
lean_dec(x_60);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_79, 0, x_78);
lean_inc(x_79);
x_80 = lean_apply_1(x_5, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_58);
x_81 = l_Lean_Json_compress(x_79);
x_82 = l_IO_FS_Stream_readRequestAs___closed__4;
x_83 = lean_string_append(x_82, x_81);
lean_dec(x_81);
x_84 = l_IO_FS_Stream_readRequestAs___closed__5;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_string_append(x_85, x_3);
x_87 = l_Char_HasRepr___closed__1;
x_88 = lean_string_append(x_86, x_87);
x_89 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_57);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_79);
x_91 = lean_ctor_get(x_80, 0);
lean_inc(x_91);
lean_dec(x_80);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_58);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_57);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_77, 0);
lean_inc(x_94);
lean_dec(x_77);
x_95 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_inc(x_95);
x_96 = lean_apply_1(x_5, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_58);
x_97 = l_Lean_Json_compress(x_95);
x_98 = l_IO_FS_Stream_readRequestAs___closed__4;
x_99 = lean_string_append(x_98, x_97);
lean_dec(x_97);
x_100 = l_IO_FS_Stream_readRequestAs___closed__5;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_string_append(x_101, x_3);
x_103 = l_Char_HasRepr___closed__1;
x_104 = lean_string_append(x_102, x_103);
x_105 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_57);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_95);
x_107 = lean_ctor_get(x_96, 0);
lean_inc(x_107);
lean_dec(x_96);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_58);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_57);
return x_109;
}
}
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_8);
lean_dec(x_5);
x_110 = !lean_is_exclusive(x_7);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_7, 0);
lean_dec(x_111);
x_112 = l_IO_FS_Stream_readRequestAs___closed__7;
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_112);
return x_7;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_7, 1);
lean_inc(x_113);
lean_dec(x_7);
x_114 = l_IO_FS_Stream_readRequestAs___closed__7;
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_5);
x_116 = !lean_is_exclusive(x_7);
if (x_116 == 0)
{
return x_7;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_7, 0);
x_118 = lean_ctor_get(x_7, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_7);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
lean_object* l_IO_FS_Stream_readRequestAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readRequestAs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_IO_FS_Stream_readNotificationAs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
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
lean_object* l_IO_FS_Stream_readNotificationAs_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Stream_readNotificationAs_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_FS_Stream_readNotificationAs_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
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
lean_object* l_IO_FS_Stream_readNotificationAs_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_readNotificationAs_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_readNotificationAs_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_IO_FS_Stream_readNotificationAs_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_readNotificationAs_match__3___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected notification, got other type of message");
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_IO_FS_Stream_readNotificationAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readMessage(x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_string_dec_eq(x_11, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_5);
x_14 = l_IO_FS_Stream_readRequestAs___closed__1;
x_15 = lean_string_append(x_14, x_3);
x_16 = l_IO_FS_Stream_readRequestAs___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_11);
lean_dec(x_11);
x_19 = l_Char_HasRepr___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_22 = l_IO_FS_Stream_readRequestAs___closed__3;
x_23 = lean_string_append(x_22, x_3);
x_24 = l_Char_HasRepr___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
lean_dec(x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_inc(x_29);
x_30 = lean_apply_1(x_5, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = l_Lean_Json_compress(x_29);
x_32 = l_IO_FS_Stream_readRequestAs___closed__4;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_IO_FS_Stream_readRequestAs___closed__5;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_3);
x_37 = l_Char_HasRepr___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_39);
return x_7;
}
else
{
lean_object* x_40; 
lean_dec(x_29);
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
lean_ctor_set(x_7, 0, x_40);
return x_7;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_inc(x_42);
x_43 = lean_apply_1(x_5, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = l_Lean_Json_compress(x_42);
x_45 = l_IO_FS_Stream_readRequestAs___closed__4;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_IO_FS_Stream_readRequestAs___closed__5;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_3);
x_50 = l_Char_HasRepr___closed__1;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_52);
return x_7;
}
else
{
lean_object* x_53; 
lean_dec(x_42);
x_53 = lean_ctor_get(x_43, 0);
lean_inc(x_53);
lean_dec(x_43);
lean_ctor_set(x_7, 0, x_53);
return x_7;
}
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_7, 1);
lean_inc(x_54);
lean_dec(x_7);
x_55 = lean_ctor_get(x_8, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_8, 1);
lean_inc(x_56);
lean_dec(x_8);
x_57 = lean_string_dec_eq(x_55, x_3);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_56);
lean_dec(x_5);
x_58 = l_IO_FS_Stream_readRequestAs___closed__1;
x_59 = lean_string_append(x_58, x_3);
x_60 = l_IO_FS_Stream_readRequestAs___closed__2;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_string_append(x_61, x_55);
lean_dec(x_55);
x_63 = l_Char_HasRepr___closed__1;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_54);
return x_66;
}
else
{
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_5);
x_67 = l_IO_FS_Stream_readRequestAs___closed__3;
x_68 = lean_string_append(x_67, x_3);
x_69 = l_Char_HasRepr___closed__1;
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_54);
return x_72;
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_56, 0);
lean_inc(x_73);
lean_dec(x_56);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_inc(x_75);
x_76 = lean_apply_1(x_5, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = l_Lean_Json_compress(x_75);
x_78 = l_IO_FS_Stream_readRequestAs___closed__4;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_IO_FS_Stream_readRequestAs___closed__5;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_string_append(x_81, x_3);
x_83 = l_Char_HasRepr___closed__1;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_54);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_75);
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
lean_dec(x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_54);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_73, 0);
lean_inc(x_89);
lean_dec(x_73);
x_90 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_90, 0, x_89);
lean_inc(x_90);
x_91 = lean_apply_1(x_5, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_92 = l_Lean_Json_compress(x_90);
x_93 = l_IO_FS_Stream_readRequestAs___closed__4;
x_94 = lean_string_append(x_93, x_92);
lean_dec(x_92);
x_95 = l_IO_FS_Stream_readRequestAs___closed__5;
x_96 = lean_string_append(x_94, x_95);
x_97 = lean_string_append(x_96, x_3);
x_98 = l_Char_HasRepr___closed__1;
x_99 = lean_string_append(x_97, x_98);
x_100 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_54);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_90);
x_102 = lean_ctor_get(x_91, 0);
lean_inc(x_102);
lean_dec(x_91);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_54);
return x_103;
}
}
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_8);
lean_dec(x_5);
x_104 = !lean_is_exclusive(x_7);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_7, 0);
lean_dec(x_105);
x_106 = l_IO_FS_Stream_readNotificationAs___closed__2;
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_106);
return x_7;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_7, 1);
lean_inc(x_107);
lean_dec(x_7);
x_108 = l_IO_FS_Stream_readNotificationAs___closed__2;
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_5);
x_110 = !lean_is_exclusive(x_7);
if (x_110 == 0)
{
return x_7;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_7, 0);
x_112 = lean_ctor_get(x_7, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_7);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
lean_object* l_IO_FS_Stream_readNotificationAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_FS_Stream_readNotificationAs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_IO_FS_Stream_writeMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__5;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6;
x_13 = l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__1(x_12, x_6);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
x_19 = l_List_append___rarg(x_18, x_13);
x_20 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Json_mkObj(x_21);
x_23 = l_IO_FS_Stream_writeJson(x_1, x_22, x_3);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_11);
x_29 = l_List_append___rarg(x_28, x_13);
x_30 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Json_mkObj(x_31);
x_33 = l_IO_FS_Stream_writeJson(x_1, x_32, x_3);
return x_33;
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__8;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_11);
x_36 = l_List_append___rarg(x_35, x_13);
x_37 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Json_mkObj(x_38);
x_40 = l_IO_FS_Stream_writeJson(x_1, x_39, x_3);
return x_40;
}
}
}
case 1:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__5;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6;
x_47 = l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__1(x_46, x_42);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_Json_mkObj(x_50);
x_52 = l_IO_FS_Stream_writeJson(x_1, x_51, x_3);
return x_52;
}
case 2:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
x_55 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__9;
lean_inc(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
switch (lean_obj_tag(x_53)) {
case 0:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
x_64 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Json_mkObj(x_65);
x_67 = l_IO_FS_Stream_writeJson(x_1, x_66, x_3);
return x_67;
}
case 1:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_53, 0);
lean_inc(x_68);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_58);
x_73 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_Json_mkObj(x_74);
x_76 = l_IO_FS_Stream_writeJson(x_1, x_75, x_3);
return x_76;
}
default: 
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__8;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_58);
x_79 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Json_mkObj(x_80);
x_82 = l_IO_FS_Stream_writeJson(x_1, x_81, x_3);
return x_82;
}
}
}
default: 
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_83 = lean_ctor_get(x_2, 0);
x_84 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_85 = lean_ctor_get(x_2, 1);
x_86 = lean_ctor_get(x_2, 2);
lean_inc(x_85);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_85);
x_88 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__10;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__11;
x_93 = l_Lean_Json_opt___at_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___spec__2(x_92, x_86);
switch (lean_obj_tag(x_83)) {
case 0:
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_83, 0);
lean_inc(x_124);
x_125 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_94 = x_125;
goto block_123;
}
case 1:
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_83, 0);
lean_inc(x_126);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_94 = x_127;
goto block_123;
}
default: 
{
lean_object* x_128; 
x_128 = lean_box(0);
x_94 = x_128;
goto block_123;
}
}
block_123:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7;
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
switch (x_84) {
case 0:
{
lean_object* x_112; 
x_112 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__1;
x_97 = x_112;
goto block_111;
}
case 1:
{
lean_object* x_113; 
x_113 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__2;
x_97 = x_113;
goto block_111;
}
case 2:
{
lean_object* x_114; 
x_114 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__3;
x_97 = x_114;
goto block_111;
}
case 3:
{
lean_object* x_115; 
x_115 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__4;
x_97 = x_115;
goto block_111;
}
case 4:
{
lean_object* x_116; 
x_116 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__5;
x_97 = x_116;
goto block_111;
}
case 5:
{
lean_object* x_117; 
x_117 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__6;
x_97 = x_117;
goto block_111;
}
case 6:
{
lean_object* x_118; 
x_118 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__7;
x_97 = x_118;
goto block_111;
}
case 7:
{
lean_object* x_119; 
x_119 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__8;
x_97 = x_119;
goto block_111;
}
case 8:
{
lean_object* x_120; 
x_120 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__9;
x_97 = x_120;
goto block_111;
}
case 9:
{
lean_object* x_121; 
x_121 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__10;
x_97 = x_121;
goto block_111;
}
default: 
{
lean_object* x_122; 
x_122 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__11;
x_97 = x_122;
goto block_111;
}
}
block_111:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_98 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__12;
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_91);
x_101 = l_List_append___rarg(x_100, x_93);
x_102 = l_Lean_Json_mkObj(x_101);
x_103 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__13;
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_90);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Json_mkObj(x_108);
x_110 = l_IO_FS_Stream_writeJson(x_1, x_109, x_3);
return x_110;
}
}
}
}
}
}
lean_object* l_IO_FS_Stream_writeMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_FS_Stream_writeResponse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_IO_FS_Stream_writeMessage(x_2, x_7, x_5);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_IO_FS_Stream_writeResponse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeResponse___rarg), 5, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_Control(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Std_Data_RBTree(lean_object*);
lean_object* initialize_Lean_Data_Json(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_JsonRpc(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_RBTree(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__1 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__1);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__2 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__2);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__3 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__3);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__4 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__4();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__4);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__5 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__5();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__5);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__6 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__6();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__6);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__7 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__7();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__7);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__8 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__8();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__8);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__9 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__9();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__9);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__10 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__10();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__10);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__11 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__11();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__11);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__12 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__12();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__12);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__13 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__13();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__13);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__14 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__14();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__14);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__15 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__15();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__15);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__16 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__16();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__16);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__17 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__17();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__17);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__18 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__18();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__18);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__19 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__19();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__19);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__20 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__20();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__20);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__21 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__21();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__21);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__22 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__22();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__22);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__23 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__23();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__23);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__24 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__24();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__24);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__25 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__25();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__25);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__26 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__26();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__26);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__27 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__27();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__27);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__28 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__28();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__28);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__29 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__29();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__29);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__30 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__30();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__30);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__31 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__31();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__31);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__32 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__32();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__32);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__33 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__33();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__33);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__34 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__34();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__34);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__35 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__35();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__35);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__36 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__36();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__36);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__37 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__37();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__37);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__38 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__38();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__38);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__39 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__39();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__39);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__40 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__40();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__40);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__41 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__41();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__41);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__42 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__42();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__42);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__43 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__43();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__43);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__44 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__44();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__1___closed__44);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__1 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__1);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__2 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__2);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__3 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__3);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__4 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__4();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__4);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__5 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__5();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__5);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__6 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__6();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__6);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__7 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__7();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__7);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__8 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__8();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__8);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__9 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__9();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__9);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__10 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__10();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__10);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__11 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__11();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__2___closed__11);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__1 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__1();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__1);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__2 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__2();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__2);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__3 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__3();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__3);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__4);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__5 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__5();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__5);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__6);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__7);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__8 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__8();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__8);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__9 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__9();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__9);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__10 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__10();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__10);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__11 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__11();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__11);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__12 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__12();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__12);
l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__13 = _init_l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__13();
lean_mark_persistent(l_Lean_JsonRpc_Lean_Data_JsonRpc___instance__7___closed__13);
l_IO_FS_Stream_readMessage___closed__1 = _init_l_IO_FS_Stream_readMessage___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readMessage___closed__1);
l_IO_FS_Stream_readMessage___closed__2 = _init_l_IO_FS_Stream_readMessage___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readMessage___closed__2);
l_IO_FS_Stream_readRequestAs___closed__1 = _init_l_IO_FS_Stream_readRequestAs___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__1);
l_IO_FS_Stream_readRequestAs___closed__2 = _init_l_IO_FS_Stream_readRequestAs___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__2);
l_IO_FS_Stream_readRequestAs___closed__3 = _init_l_IO_FS_Stream_readRequestAs___closed__3();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__3);
l_IO_FS_Stream_readRequestAs___closed__4 = _init_l_IO_FS_Stream_readRequestAs___closed__4();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__4);
l_IO_FS_Stream_readRequestAs___closed__5 = _init_l_IO_FS_Stream_readRequestAs___closed__5();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__5);
l_IO_FS_Stream_readRequestAs___closed__6 = _init_l_IO_FS_Stream_readRequestAs___closed__6();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__6);
l_IO_FS_Stream_readRequestAs___closed__7 = _init_l_IO_FS_Stream_readRequestAs___closed__7();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___closed__7);
l_IO_FS_Stream_readNotificationAs___closed__1 = _init_l_IO_FS_Stream_readNotificationAs___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readNotificationAs___closed__1);
l_IO_FS_Stream_readNotificationAs___closed__2 = _init_l_IO_FS_Stream_readNotificationAs___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readNotificationAs___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
