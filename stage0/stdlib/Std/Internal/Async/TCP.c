// Lean compiler output
// Module: Std.Internal.Async.TCP
// Imports: Std.Time Std.Internal.UV Std.Internal.Async.Basic Std.Net.Addr
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName(lean_object*, lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__22;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__3;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__26;
lean_object* lean_uv_tcp_bind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_mk(lean_object*);
lean_object* lean_uv_tcp_getsockname(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lambda__1(lean_object*);
lean_object* lean_uv_tcp_connect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f(lean_object*, uint64_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_getpeername(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__1;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__16;
lean_object* lean_uv_tcp_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen(lean_object*, uint32_t, lean_object*);
lean_object* lean_uv_tcp_nodelay(lean_object*, lean_object*);
lean_object* lean_uv_tcp_new(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__27;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__5;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_mk(lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__14;
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t, lean_object*);
uint8_t lean_bool_to_int8(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__18;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__21;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName(lean_object*, lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__17;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__15;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__23;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__24;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__8;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__9;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_uv_tcp_accept(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134_;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__25;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__12;
lean_object* lean_uv_tcp_keepalive(lean_object*, uint8_t, uint32_t, lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__7;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_recv(lean_object*, uint64_t, lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__19;
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay(lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___rarg(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown___boxed(lean_object*, lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__10;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName___boxed(lean_object*, lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__6;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay(lean_object*, lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__11;
LEAN_EXPORT lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_269_;
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__13;
lean_object* lean_uv_tcp_shutdown(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__20;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_mk(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_tcp_new(x_1);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_bind(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_bind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Server_bind(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_listen(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_listen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_TCP_Socket_Server_listen(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lambda__1(lean_object* x_1) {
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
static lean_object* _init_l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_TCP_Socket_Server_accept___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_accept(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_IO_Promise_result_x21___rarg(x_5);
lean_dec(x_5);
x_7 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__1;
x_8 = l_Task_Priority_default;
x_9 = 0;
x_10 = lean_task_map(x_7, x_6, x_8, x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = l_IO_Promise_result_x21___rarg(x_11);
lean_dec(x_11);
x_14 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__1;
x_15 = l_Task_Priority_default;
x_16 = 0;
x_17 = lean_task_map(x_14, x_13, x_15, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_accept___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_accept(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_getsockname(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_getSockName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_nodelay(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Server_noDelay(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__1;
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__2;
x_3 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__3;
x_4 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__1;
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__2;
x_3 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__3;
x_4 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decide", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__1;
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__2;
x_3 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__3;
x_4 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__11;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__11;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__6;
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__1;
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__2;
x_3 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__3;
x_4 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__15;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__10;
x_3 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__6;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__6;
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__17;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__16;
x_3 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__18;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__14;
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__19;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__12;
x_3 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__20;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__6;
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__21;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__10;
x_3 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__22;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__6;
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__23;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__8;
x_3 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__24;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__6;
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__25;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__5;
x_3 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__26;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__27;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; 
x_6 = lean_bool_to_int8(x_2);
x_7 = l_Int_toNat(x_3);
x_8 = lean_uint32_of_nat(x_7);
lean_dec(x_7);
x_9 = lean_uv_tcp_keepalive(x_1, x_6, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Std_Internal_IO_Async_TCP_Socket_Server_keepAlive(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_mk(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_tcp_new(x_1);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_bind(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_bind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_bind(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_connect(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_IO_Promise_result_x21___rarg(x_6);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_IO_Promise_result_x21___rarg(x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_connect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_connect(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_send(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_IO_Promise_result_x21___rarg(x_6);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_IO_Promise_result_x21___rarg(x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_send___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_TCP_Socket_Client_send(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_tcp_recv(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_IO_Promise_result_x21___rarg(x_6);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_IO_Promise_result_x21___rarg(x_8);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Async_TCP_Socket_Client_recv_x3f(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_shutdown(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_IO_Promise_result_x21___rarg(x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_IO_Promise_result_x21___rarg(x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_shutdown(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_getpeername(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_getPeerName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_getsockname(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_getSockName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_tcp_nodelay(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_TCP_Socket_Client_noDelay(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Std_Internal_Async_TCP___hyg_269_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__27;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; 
x_6 = lean_bool_to_int8(x_2);
x_7 = l_Int_toNat(x_3);
x_8 = lean_uint32_of_nat(x_7);
lean_dec(x_7);
x_9 = lean_uv_tcp_keepalive(x_1, x_6, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Std_Internal_IO_Async_TCP_Socket_Client_keepAlive(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Std_Time(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_UV(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_Async_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Net_Addr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_TCP(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Net_Addr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__1 = _init_l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_TCP_Socket_Server_accept___closed__1);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__1 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__1();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__1);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__2 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__2();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__2);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__3 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__3();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__3);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__4 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__4();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__4);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__5 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__5();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__5);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__6 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__6();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__6);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__7 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__7();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__7);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__8 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__8();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__8);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__9 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__9();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__9);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__10 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__10();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__10);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__11 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__11();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__11);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__12 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__12();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__12);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__13 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__13();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__13);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__14 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__14();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__14);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__15 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__15();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__15);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__16 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__16();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__16);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__17 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__17();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__17);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__18 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__18();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__18);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__19 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__19();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__19);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__20 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__20();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__20);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__21 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__21();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__21);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__22 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__22();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__22);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__23 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__23();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__23);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__24 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__24();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__24);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__25 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__25();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__25);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__26 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__26();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__26);
l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__27 = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__27();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134____closed__27);
l___auto____x40_Std_Internal_Async_TCP___hyg_134_ = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_134_();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_134_);
l___auto____x40_Std_Internal_Async_TCP___hyg_269_ = _init_l___auto____x40_Std_Internal_Async_TCP___hyg_269_();
lean_mark_persistent(l___auto____x40_Std_Internal_Async_TCP___hyg_269_);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
