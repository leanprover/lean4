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
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = lean_uv_udp_new();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_new___boxed(lean_object* v_a_00___x40___internal___hyg_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lean_uv_udp_new();
return v_res_5_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_bind_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_6_ = stack[0].m_obj;
lean_object* v_addr_7_ = stack[1].m_obj;
lean_object* v_res_9_;
v_res_9_ = lean_uv_udp_bind(v_socket_6_, v_addr_7_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_bind___boxed(lean_object* v_socket_10_, lean_object* v_addr_11_, lean_object* v_a_00___x40___internal___hyg_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lean_uv_udp_bind(v_socket_10_, v_addr_11_);
lean_dec_ref(v_addr_11_);
lean_dec(v_socket_10_);
return v_res_13_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_connect_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_14_ = stack[0].m_obj;
lean_object* v_addr_15_ = stack[1].m_obj;
lean_object* v_res_17_;
v_res_17_ = lean_uv_udp_connect(v_socket_14_, v_addr_15_);
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_connect___boxed(lean_object* v_socket_18_, lean_object* v_addr_19_, lean_object* v_a_00___x40___internal___hyg_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lean_uv_udp_connect(v_socket_18_, v_addr_19_);
lean_dec_ref(v_addr_19_);
lean_dec(v_socket_18_);
return v_res_21_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_22_ = stack[0].m_obj;
lean_object* v_data_23_ = stack[1].m_obj;
lean_object* v_addr_24_ = stack[2].m_obj;
lean_object* v_res_26_;
v_res_26_ = lean_uv_udp_send(v_socket_22_, v_data_23_, v_addr_24_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_send___boxed(lean_object* v_socket_27_, lean_object* v_data_28_, lean_object* v_addr_29_, lean_object* v_a_00___x40___internal___hyg_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lean_uv_udp_send(v_socket_27_, v_data_28_, v_addr_29_);
lean_dec(v_addr_29_);
lean_dec(v_socket_27_);
return v_res_31_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_32_ = stack[0].m_obj;
uint64_t v_size_33_ = stack[1].m_num;
lean_object* v_res_35_;
v_res_35_ = lean_uv_udp_recv(v_socket_32_, v_size_33_);
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_recv___boxed(lean_object* v_socket_36_, lean_object* v_size_37_, lean_object* v_a_00___x40___internal___hyg_38_){
_start:
{
uint64_t v_size_boxed_39_; lean_object* v_res_40_; 
v_size_boxed_39_ = lean_unbox_uint64(v_size_37_);
lean_dec_ref(v_size_37_);
v_res_40_ = lean_uv_udp_recv(v_socket_36_, v_size_boxed_39_);
lean_dec(v_socket_36_);
return v_res_40_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_waitReadable_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_41_ = stack[0].m_obj;
lean_object* v_res_43_;
v_res_43_ = lean_uv_udp_wait_readable(v_socket_41_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_waitReadable___boxed(lean_object* v_socket_44_, lean_object* v_a_00___x40___internal___hyg_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lean_uv_udp_wait_readable(v_socket_44_);
lean_dec(v_socket_44_);
return v_res_46_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_cancelRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_47_ = stack[0].m_obj;
lean_object* v_res_49_;
v_res_49_ = lean_uv_udp_cancel_recv(v_socket_47_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_cancelRecv___boxed(lean_object* v_socket_50_, lean_object* v_a_00___x40___internal___hyg_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lean_uv_udp_cancel_recv(v_socket_50_);
lean_dec(v_socket_50_);
return v_res_52_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_getPeerName_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_53_ = stack[0].m_obj;
lean_object* v_res_55_;
v_res_55_ = lean_uv_udp_getpeername(v_socket_53_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_getPeerName___boxed(lean_object* v_socket_56_, lean_object* v_a_00___x40___internal___hyg_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = lean_uv_udp_getpeername(v_socket_56_);
lean_dec(v_socket_56_);
return v_res_58_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_getSockName_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_59_ = stack[0].m_obj;
lean_object* v_res_61_;
v_res_61_ = lean_uv_udp_getsockname(v_socket_59_);
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_getSockName___boxed(lean_object* v_socket_62_, lean_object* v_a_00___x40___internal___hyg_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = lean_uv_udp_getsockname(v_socket_62_);
lean_dec(v_socket_62_);
return v_res_64_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_setBroadcast_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_65_ = stack[0].m_obj;
uint8_t v_on_66_ = stack[1].m_num;
lean_object* v_res_68_;
v_res_68_ = lean_uv_udp_set_broadcast(v_socket_65_, v_on_66_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setBroadcast___boxed(lean_object* v_socket_69_, lean_object* v_on_70_, lean_object* v_a_00___x40___internal___hyg_71_){
_start:
{
uint8_t v_on_boxed_72_; lean_object* v_res_73_; 
v_on_boxed_72_ = lean_unbox(v_on_70_);
v_res_73_ = lean_uv_udp_set_broadcast(v_socket_69_, v_on_boxed_72_);
lean_dec(v_socket_69_);
return v_res_73_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_setMulticastLoop_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_74_ = stack[0].m_obj;
uint8_t v_on_75_ = stack[1].m_num;
lean_object* v_res_77_;
v_res_77_ = lean_uv_udp_set_multicast_loop(v_socket_74_, v_on_75_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastLoop___boxed(lean_object* v_socket_78_, lean_object* v_on_79_, lean_object* v_a_00___x40___internal___hyg_80_){
_start:
{
uint8_t v_on_boxed_81_; lean_object* v_res_82_; 
v_on_boxed_81_ = lean_unbox(v_on_79_);
v_res_82_ = lean_uv_udp_set_multicast_loop(v_socket_78_, v_on_boxed_81_);
lean_dec(v_socket_78_);
return v_res_82_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_setMulticastTTL_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_83_ = stack[0].m_obj;
uint32_t v_ttl_84_ = stack[1].m_num;
lean_object* v_res_86_;
v_res_86_ = lean_uv_udp_set_multicast_ttl(v_socket_83_, v_ttl_84_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastTTL___boxed(lean_object* v_socket_87_, lean_object* v_ttl_88_, lean_object* v_a_00___x40___internal___hyg_89_){
_start:
{
uint32_t v_ttl_boxed_90_; lean_object* v_res_91_; 
v_ttl_boxed_90_ = lean_unbox_uint32(v_ttl_88_);
lean_dec(v_ttl_88_);
v_res_91_ = lean_uv_udp_set_multicast_ttl(v_socket_87_, v_ttl_boxed_90_);
lean_dec(v_socket_87_);
return v_res_91_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_setMembership_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_92_ = stack[0].m_obj;
lean_object* v_multicastAddr_93_ = stack[1].m_obj;
lean_object* v_interfaceAddr_94_ = stack[2].m_obj;
uint8_t v_membership_95_ = stack[3].m_num;
lean_object* v_res_97_;
v_res_97_ = lean_uv_udp_set_membership(v_socket_92_, v_multicastAddr_93_, v_interfaceAddr_94_, v_membership_95_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMembership___boxed(lean_object* v_socket_98_, lean_object* v_multicastAddr_99_, lean_object* v_interfaceAddr_100_, lean_object* v_membership_101_, lean_object* v_a_00___x40___internal___hyg_102_){
_start:
{
uint8_t v_membership_boxed_103_; lean_object* v_res_104_; 
v_membership_boxed_103_ = lean_unbox(v_membership_101_);
v_res_104_ = lean_uv_udp_set_membership(v_socket_98_, v_multicastAddr_99_, v_interfaceAddr_100_, v_membership_boxed_103_);
lean_dec(v_interfaceAddr_100_);
lean_dec_ref(v_multicastAddr_99_);
lean_dec(v_socket_98_);
return v_res_104_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_setMulticastInterface_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_105_ = stack[0].m_obj;
lean_object* v_interfaceAddr_106_ = stack[1].m_obj;
lean_object* v_res_108_;
v_res_108_ = lean_uv_udp_set_multicast_interface(v_socket_105_, v_interfaceAddr_106_);
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setMulticastInterface___boxed(lean_object* v_socket_109_, lean_object* v_interfaceAddr_110_, lean_object* v_a_00___x40___internal___hyg_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = lean_uv_udp_set_multicast_interface(v_socket_109_, v_interfaceAddr_110_);
lean_dec_ref(v_interfaceAddr_110_);
lean_dec(v_socket_109_);
return v_res_112_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_UDP_Socket_setTTL_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_113_ = stack[0].m_obj;
uint32_t v_ttl_114_ = stack[1].m_num;
lean_object* v_res_116_;
v_res_116_ = lean_uv_udp_set_ttl(v_socket_113_, v_ttl_114_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_UDP_Socket_setTTL___boxed(lean_object* v_socket_117_, lean_object* v_ttl_118_, lean_object* v_a_00___x40___internal___hyg_119_){
_start:
{
uint32_t v_ttl_boxed_120_; lean_object* v_res_121_; 
v_ttl_boxed_120_ = lean_unbox_uint32(v_ttl_118_);
lean_dec(v_ttl_118_);
v_res_121_ = lean_uv_udp_set_ttl(v_socket_117_, v_ttl_boxed_120_);
lean_dec(v_socket_117_);
return v_res_121_;
}
}
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
lean_object* runtime_initialize_Std_Net(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_UV_UDP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
