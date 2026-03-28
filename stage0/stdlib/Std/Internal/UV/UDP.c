// Lean compiler output
// Module: Std.Internal.UV.UDP
// Imports: public import Init.System.Promise public import Std.Net
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
LEAN_EXPORT lean_object* l___private_Std_Internal_UV_UDP_0__Std_Internal_UV_UDP_SocketImpl;
lean_object* lean_uv_udp_new();
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_new___boxed(lean_object*);
lean_object* lean_uv_udp_bind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_bind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_connect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_connect___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_send(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_recv(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_recv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_wait_readable(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_waitReadable___boxed(lean_object*, lean_object*);
lean_object* lean_uv_udp_cancel_recv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_cancelRecv___boxed(lean_object*, lean_object*);
lean_object* lean_uv_udp_getpeername(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_getPeerName___boxed(lean_object*, lean_object*);
lean_object* lean_uv_udp_getsockname(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_getSockName___boxed(lean_object*, lean_object*);
lean_object* lean_uv_udp_set_broadcast(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setBroadcast___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_set_multicast_loop(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastLoop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_set_multicast_ttl(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastTTL___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_set_membership(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMembership___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_set_multicast_interface(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastInterface___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_udp_set_ttl(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setTTL___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Internal_UV_UDP_0__Std_Internal_UV_UDP_SocketImpl(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_new___boxed(lean_object* v_a_00___x40___internal___hyg_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = lean_uv_udp_new();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_bind___boxed(lean_object* v_socket_8_, lean_object* v_addr_9_, lean_object* v_a_00___x40___internal___hyg_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = lean_uv_udp_bind(v_socket_8_, v_addr_9_);
lean_dec_ref(v_addr_9_);
lean_dec(v_socket_8_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_connect___boxed(lean_object* v_socket_15_, lean_object* v_addr_16_, lean_object* v_a_00___x40___internal___hyg_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lean_uv_udp_connect(v_socket_15_, v_addr_16_);
lean_dec_ref(v_addr_16_);
lean_dec(v_socket_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_send___boxed(lean_object* v_socket_23_, lean_object* v_data_24_, lean_object* v_addr_25_, lean_object* v_a_00___x40___internal___hyg_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lean_uv_udp_send(v_socket_23_, v_data_24_, v_addr_25_);
lean_dec(v_addr_25_);
lean_dec(v_socket_23_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_recv___boxed(lean_object* v_socket_31_, lean_object* v_size_32_, lean_object* v_a_00___x40___internal___hyg_33_){
_start:
{
uint64_t v_size_boxed_34_; lean_object* v_res_35_; 
v_size_boxed_34_ = lean_unbox_uint64(v_size_32_);
lean_dec_ref(v_size_32_);
v_res_35_ = lean_uv_udp_recv(v_socket_31_, v_size_boxed_34_);
lean_dec(v_socket_31_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_waitReadable___boxed(lean_object* v_socket_38_, lean_object* v_a_00___x40___internal___hyg_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lean_uv_udp_wait_readable(v_socket_38_);
lean_dec(v_socket_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_cancelRecv___boxed(lean_object* v_socket_43_, lean_object* v_a_00___x40___internal___hyg_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lean_uv_udp_cancel_recv(v_socket_43_);
lean_dec(v_socket_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_getPeerName___boxed(lean_object* v_socket_48_, lean_object* v_a_00___x40___internal___hyg_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lean_uv_udp_getpeername(v_socket_48_);
lean_dec(v_socket_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_getSockName___boxed(lean_object* v_socket_53_, lean_object* v_a_00___x40___internal___hyg_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lean_uv_udp_getsockname(v_socket_53_);
lean_dec(v_socket_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setBroadcast___boxed(lean_object* v_socket_59_, lean_object* v_on_60_, lean_object* v_a_00___x40___internal___hyg_61_){
_start:
{
uint8_t v_on_boxed_62_; lean_object* v_res_63_; 
v_on_boxed_62_ = lean_unbox(v_on_60_);
v_res_63_ = lean_uv_udp_set_broadcast(v_socket_59_, v_on_boxed_62_);
lean_dec(v_socket_59_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastLoop___boxed(lean_object* v_socket_67_, lean_object* v_on_68_, lean_object* v_a_00___x40___internal___hyg_69_){
_start:
{
uint8_t v_on_boxed_70_; lean_object* v_res_71_; 
v_on_boxed_70_ = lean_unbox(v_on_68_);
v_res_71_ = lean_uv_udp_set_multicast_loop(v_socket_67_, v_on_boxed_70_);
lean_dec(v_socket_67_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastTTL___boxed(lean_object* v_socket_75_, lean_object* v_ttl_76_, lean_object* v_a_00___x40___internal___hyg_77_){
_start:
{
uint32_t v_ttl_boxed_78_; lean_object* v_res_79_; 
v_ttl_boxed_78_ = lean_unbox_uint32(v_ttl_76_);
lean_dec(v_ttl_76_);
v_res_79_ = lean_uv_udp_set_multicast_ttl(v_socket_75_, v_ttl_boxed_78_);
lean_dec(v_socket_75_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMembership___boxed(lean_object* v_socket_85_, lean_object* v_multicastAddr_86_, lean_object* v_interfaceAddr_87_, lean_object* v_membership_88_, lean_object* v_a_00___x40___internal___hyg_89_){
_start:
{
uint8_t v_membership_boxed_90_; lean_object* v_res_91_; 
v_membership_boxed_90_ = lean_unbox(v_membership_88_);
v_res_91_ = lean_uv_udp_set_membership(v_socket_85_, v_multicastAddr_86_, v_interfaceAddr_87_, v_membership_boxed_90_);
lean_dec(v_interfaceAddr_87_);
lean_dec_ref(v_multicastAddr_86_);
lean_dec(v_socket_85_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastInterface___boxed(lean_object* v_socket_95_, lean_object* v_interfaceAddr_96_, lean_object* v_a_00___x40___internal___hyg_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = lean_uv_udp_set_multicast_interface(v_socket_95_, v_interfaceAddr_96_);
lean_dec_ref(v_interfaceAddr_96_);
lean_dec(v_socket_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setTTL___boxed(lean_object* v_socket_102_, lean_object* v_ttl_103_, lean_object* v_a_00___x40___internal___hyg_104_){
_start:
{
uint32_t v_ttl_boxed_105_; lean_object* v_res_106_; 
v_ttl_boxed_105_ = lean_unbox_uint32(v_ttl_103_);
lean_dec(v_ttl_103_);
v_res_106_ = lean_uv_udp_set_ttl(v_socket_102_, v_ttl_boxed_105_);
lean_dec(v_socket_102_);
return v_res_106_;
}
}
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
lean_object* runtime_initialize_Std_Net(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_UV_UDP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Net(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Internal_UV_UDP_0__Std_Internal_UV_UDP_SocketImpl = _init_l___private_Std_Internal_UV_UDP_0__Std_Internal_UV_UDP_SocketImpl();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_UV_UDP(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_Promise(uint8_t builtin);
lean_object* initialize_Std_Net(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_UV_UDP(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Net(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_UDP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_UV_UDP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_UV_UDP(builtin);
}
#ifdef __cplusplus
}
#endif
