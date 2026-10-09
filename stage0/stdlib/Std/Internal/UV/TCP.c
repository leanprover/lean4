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
lean_object* lean_uv_tcp_wait_acceptable(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_waitAcceptable___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = lean_uv_tcp_new();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_new___boxed(lean_object* v_a_00___x40___internal___hyg_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lean_uv_tcp_new();
return v_res_5_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_connect_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_6_ = stack[0].m_obj;
lean_object* v_addr_7_ = stack[1].m_obj;
lean_object* v_res_9_;
v_res_9_ = lean_uv_tcp_connect(v_socket_6_, v_addr_7_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_connect___boxed(lean_object* v_socket_10_, lean_object* v_addr_11_, lean_object* v_a_00___x40___internal___hyg_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lean_uv_tcp_connect(v_socket_10_, v_addr_11_);
lean_dec_ref(v_addr_11_);
lean_dec(v_socket_10_);
return v_res_13_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_14_ = stack[0].m_obj;
lean_object* v_data_15_ = stack[1].m_obj;
lean_object* v_res_17_;
v_res_17_ = lean_uv_tcp_send(v_socket_14_, v_data_15_);
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_send___boxed(lean_object* v_socket_18_, lean_object* v_data_19_, lean_object* v_a_00___x40___internal___hyg_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = lean_uv_tcp_send(v_socket_18_, v_data_19_);
lean_dec(v_socket_18_);
return v_res_21_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_recv_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_22_ = stack[0].m_obj;
uint64_t v_size_23_ = stack[1].m_num;
lean_object* v_res_25_;
v_res_25_ = lean_uv_tcp_recv(v_socket_22_, v_size_23_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_recv_x3f___boxed(lean_object* v_socket_26_, lean_object* v_size_27_, lean_object* v_a_00___x40___internal___hyg_28_){
_start:
{
uint64_t v_size_boxed_29_; lean_object* v_res_30_; 
v_size_boxed_29_ = lean_unbox_uint64(v_size_27_);
lean_dec_ref(v_size_27_);
v_res_30_ = lean_uv_tcp_recv(v_socket_26_, v_size_boxed_29_);
lean_dec(v_socket_26_);
return v_res_30_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_waitReadable_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_31_ = stack[0].m_obj;
lean_object* v_res_33_;
v_res_33_ = lean_uv_tcp_wait_readable(v_socket_31_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_waitReadable___boxed(lean_object* v_socket_34_, lean_object* v_a_00___x40___internal___hyg_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = lean_uv_tcp_wait_readable(v_socket_34_);
lean_dec(v_socket_34_);
return v_res_36_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_cancelRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_37_ = stack[0].m_obj;
lean_object* v_res_39_;
v_res_39_ = lean_uv_tcp_cancel_recv(v_socket_37_);
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_cancelRecv___boxed(lean_object* v_socket_40_, lean_object* v_a_00___x40___internal___hyg_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = lean_uv_tcp_cancel_recv(v_socket_40_);
lean_dec(v_socket_40_);
return v_res_42_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_bind_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_43_ = stack[0].m_obj;
lean_object* v_addr_44_ = stack[1].m_obj;
lean_object* v_res_46_;
v_res_46_ = lean_uv_tcp_bind(v_socket_43_, v_addr_44_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_bind___boxed(lean_object* v_socket_47_, lean_object* v_addr_48_, lean_object* v_a_00___x40___internal___hyg_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lean_uv_tcp_bind(v_socket_47_, v_addr_48_);
lean_dec_ref(v_addr_48_);
lean_dec(v_socket_47_);
return v_res_50_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_listen_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_51_ = stack[0].m_obj;
uint32_t v_backlog_52_ = stack[1].m_num;
lean_object* v_res_54_;
v_res_54_ = lean_uv_tcp_listen(v_socket_51_, v_backlog_52_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_listen___boxed(lean_object* v_socket_55_, lean_object* v_backlog_56_, lean_object* v_a_00___x40___internal___hyg_57_){
_start:
{
uint32_t v_backlog_boxed_58_; lean_object* v_res_59_; 
v_backlog_boxed_58_ = lean_unbox_uint32(v_backlog_56_);
lean_dec(v_backlog_56_);
v_res_59_ = lean_uv_tcp_listen(v_socket_55_, v_backlog_boxed_58_);
lean_dec(v_socket_55_);
return v_res_59_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_accept_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_60_ = stack[0].m_obj;
lean_object* v_res_62_;
v_res_62_ = lean_uv_tcp_accept(v_socket_60_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_accept___boxed(lean_object* v_socket_63_, lean_object* v_a_00___x40___internal___hyg_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = lean_uv_tcp_accept(v_socket_63_);
lean_dec(v_socket_63_);
return v_res_65_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_tryAccept_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_66_ = stack[0].m_obj;
lean_object* v_res_68_;
v_res_68_ = lean_uv_tcp_try_accept(v_socket_66_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_tryAccept___boxed(lean_object* v_socket_69_, lean_object* v_a_00___x40___internal___hyg_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = lean_uv_tcp_try_accept(v_socket_69_);
lean_dec(v_socket_69_);
return v_res_71_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_waitAcceptable_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_72_ = stack[0].m_obj;
lean_object* v_res_74_;
v_res_74_ = lean_uv_tcp_wait_acceptable(v_socket_72_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_waitAcceptable___boxed(lean_object* v_socket_75_, lean_object* v_a_00___x40___internal___hyg_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = lean_uv_tcp_wait_acceptable(v_socket_75_);
lean_dec(v_socket_75_);
return v_res_77_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_cancelAccept_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_78_ = stack[0].m_obj;
lean_object* v_res_80_;
v_res_80_ = lean_uv_tcp_cancel_accept(v_socket_78_);
stack->m_obj
 = v_res_80_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_cancelAccept___boxed(lean_object* v_socket_81_, lean_object* v_a_00___x40___internal___hyg_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = lean_uv_tcp_cancel_accept(v_socket_81_);
lean_dec(v_socket_81_);
return v_res_83_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_shutdown_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_84_ = stack[0].m_obj;
lean_object* v_res_86_;
v_res_86_ = lean_uv_tcp_shutdown(v_socket_84_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_shutdown___boxed(lean_object* v_socket_87_, lean_object* v_a_00___x40___internal___hyg_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = lean_uv_tcp_shutdown(v_socket_87_);
lean_dec(v_socket_87_);
return v_res_89_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_getPeerName_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_90_ = stack[0].m_obj;
lean_object* v_res_92_;
v_res_92_ = lean_uv_tcp_getpeername(v_socket_90_);
stack->m_obj
 = v_res_92_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_getPeerName___boxed(lean_object* v_socket_93_, lean_object* v_a_00___x40___internal___hyg_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = lean_uv_tcp_getpeername(v_socket_93_);
lean_dec(v_socket_93_);
return v_res_95_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_getSockName_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_96_ = stack[0].m_obj;
lean_object* v_res_98_;
v_res_98_ = lean_uv_tcp_getsockname(v_socket_96_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_getSockName___boxed(lean_object* v_socket_99_, lean_object* v_a_00___x40___internal___hyg_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = lean_uv_tcp_getsockname(v_socket_99_);
lean_dec(v_socket_99_);
return v_res_101_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_noDelay_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_102_ = stack[0].m_obj;
lean_object* v_res_104_;
v_res_104_ = lean_uv_tcp_nodelay(v_socket_102_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_noDelay___boxed(lean_object* v_socket_105_, lean_object* v_a_00___x40___internal___hyg_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = lean_uv_tcp_nodelay(v_socket_105_);
lean_dec(v_socket_105_);
return v_res_107_;
}
}
LEAN_EXPORT void l_Std_Internal_UV_TCP_Socket_keepAlive_0interp(lean_interpreter_value* stack)
{
lean_object* v_socket_108_ = stack[0].m_obj;
uint8_t v_enable_109_ = stack[1].m_num;
uint32_t v_delay_110_ = stack[2].m_num;
lean_object* v_res_112_;
v_res_112_ = lean_uv_tcp_keepalive(v_socket_108_, v_enable_109_, v_delay_110_);
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l_Std_Internal_UV_TCP_Socket_keepAlive___boxed(lean_object* v_socket_113_, lean_object* v_enable_114_, lean_object* v_delay_115_, lean_object* v_a_00___x40___internal___hyg_116_){
_start:
{
uint8_t v_enable_boxed_117_; uint32_t v_delay_boxed_118_; lean_object* v_res_119_; 
v_enable_boxed_117_ = lean_unbox(v_enable_114_);
v_delay_boxed_118_ = lean_unbox_uint32(v_delay_115_);
lean_dec(v_delay_115_);
v_res_119_ = lean_uv_tcp_keepalive(v_socket_113_, v_enable_boxed_117_, v_delay_boxed_118_);
lean_dec(v_socket_113_);
return v_res_119_;
}
}
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt(uint8_t builtin);
lean_object* runtime_initialize_Std_Net(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_UV_TCP(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
