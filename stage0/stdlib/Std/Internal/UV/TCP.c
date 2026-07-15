// Lean compiler output
// Module: Std.Internal.UV.TCP
// Imports: public import Init.System.Promise public import Init.Data.SInt public import Std.Net
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
LEAN_EXPORT lean_object* l___private_Std_Internal_UV_TCP_0__Std_Internal_UV_TCP_SocketImpl;
lean_object* lean_uv_tcp_new();
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_new___boxed(lean_object*);
lean_object* lean_uv_tcp_connect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_connect___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_send(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_send___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_recv(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_recv_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_wait_readable(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_waitReadable___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_cancel_recv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_cancelRecv___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_bind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_bind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_listen(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_listen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_tcp_accept(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_accept___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_try_accept(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_tryAccept___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_cancel_accept(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_cancelAccept___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_shutdown(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_shutdown___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_getpeername(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_getPeerName___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_getsockname(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_getSockName___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_nodelay(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_noDelay___boxed(lean_object*, lean_object*);
lean_object* lean_uv_tcp_keepalive(lean_object*, uint8_t, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_keepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Internal_UV_TCP_0__Std_Internal_UV_TCP_SocketImpl(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_new___boxed(lean_object* v_a_00___x40___internal___hyg_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_uv_tcp_new();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_connect___boxed(lean_object* v_socket_8_, lean_object* v_addr_9_, lean_object* v_a_00___x40___internal___hyg_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lean_uv_tcp_connect(v_socket_8_, v_addr_9_);
lean_dec_ref(v_addr_9_);
lean_dec(v_socket_8_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_send___boxed(lean_object* v_socket_15_, lean_object* v_data_16_, lean_object* v_a_00___x40___internal___hyg_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lean_uv_tcp_send(v_socket_15_, v_data_16_);
lean_dec(v_socket_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_recv_x3f___boxed(lean_object* v_socket_22_, lean_object* v_size_23_, lean_object* v_a_00___x40___internal___hyg_24_){
_start:
{
uint64_t v_size_boxed_25_; lean_object* v_res_26_; 
v_size_boxed_25_ = lean_unbox_uint64(v_size_23_);
lean_dec_ref(v_size_23_);
v_res_26_ = lean_uv_tcp_recv(v_socket_22_, v_size_boxed_25_);
lean_dec(v_socket_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_waitReadable___boxed(lean_object* v_socket_29_, lean_object* v_a_00___x40___internal___hyg_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lean_uv_tcp_wait_readable(v_socket_29_);
lean_dec(v_socket_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_cancelRecv___boxed(lean_object* v_socket_34_, lean_object* v_a_00___x40___internal___hyg_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lean_uv_tcp_cancel_recv(v_socket_34_);
lean_dec(v_socket_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_bind___boxed(lean_object* v_socket_40_, lean_object* v_addr_41_, lean_object* v_a_00___x40___internal___hyg_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = lean_uv_tcp_bind(v_socket_40_, v_addr_41_);
lean_dec_ref(v_addr_41_);
lean_dec(v_socket_40_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_listen___boxed(lean_object* v_socket_47_, lean_object* v_backlog_48_, lean_object* v_a_00___x40___internal___hyg_49_){
_start:
{
uint32_t v_backlog_boxed_50_; lean_object* v_res_51_; 
v_backlog_boxed_50_ = lean_unbox_uint32(v_backlog_48_);
lean_dec(v_backlog_48_);
v_res_51_ = lean_uv_tcp_listen(v_socket_47_, v_backlog_boxed_50_);
lean_dec(v_socket_47_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_accept___boxed(lean_object* v_socket_54_, lean_object* v_a_00___x40___internal___hyg_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = lean_uv_tcp_accept(v_socket_54_);
lean_dec(v_socket_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_tryAccept___boxed(lean_object* v_socket_59_, lean_object* v_a_00___x40___internal___hyg_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = lean_uv_tcp_try_accept(v_socket_59_);
lean_dec(v_socket_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_cancelAccept___boxed(lean_object* v_socket_64_, lean_object* v_a_00___x40___internal___hyg_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = lean_uv_tcp_cancel_accept(v_socket_64_);
lean_dec(v_socket_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_shutdown___boxed(lean_object* v_socket_69_, lean_object* v_a_00___x40___internal___hyg_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lean_uv_tcp_shutdown(v_socket_69_);
lean_dec(v_socket_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_getPeerName___boxed(lean_object* v_socket_74_, lean_object* v_a_00___x40___internal___hyg_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = lean_uv_tcp_getpeername(v_socket_74_);
lean_dec(v_socket_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_getSockName___boxed(lean_object* v_socket_79_, lean_object* v_a_00___x40___internal___hyg_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lean_uv_tcp_getsockname(v_socket_79_);
lean_dec(v_socket_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_noDelay___boxed(lean_object* v_socket_84_, lean_object* v_a_00___x40___internal___hyg_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lean_uv_tcp_nodelay(v_socket_84_);
lean_dec(v_socket_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_keepAlive___boxed(lean_object* v_socket_91_, lean_object* v_enable_92_, lean_object* v_delay_93_, lean_object* v_a_00___x40___internal___hyg_94_){
_start:
{
uint8_t v_enable_boxed_95_; uint32_t v_delay_boxed_96_; lean_object* v_res_97_; 
v_enable_boxed_95_ = lean_unbox(v_enable_92_);
v_delay_boxed_96_ = lean_unbox_uint32(v_delay_93_);
lean_dec(v_delay_93_);
v_res_97_ = lean_uv_tcp_keepalive(v_socket_91_, v_enable_boxed_95_, v_delay_boxed_96_);
lean_dec(v_socket_91_);
return v_res_97_;
}
}
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt(uint8_t builtin);
lean_object* runtime_initialize_Std_Net(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_UV_TCP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Net(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Internal_UV_TCP_0__Std_Internal_UV_TCP_SocketImpl = _init_l___private_Std_Internal_UV_TCP_0__Std_Internal_UV_TCP_SocketImpl();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_UV_TCP(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_Promise(uint8_t builtin);
lean_object* initialize_Init_Data_SInt(uint8_t builtin);
lean_object* initialize_Std_Net(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_UV_TCP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Net(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_UV_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_UV_TCP(builtin);
}
#ifdef __cplusplus
}
#endif
