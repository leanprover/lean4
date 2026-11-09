// Lean compiler output
// Module: Std.Http.Server.Connection
// Imports: public import Std.Async.TCP public import Std.Async.ContextAsync public import Std.Http.Transport public import Std.Http.Protocol.H1 public import Std.Http.Server.Config public import Std.Http.Server.Handler
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ByteArray_mkIterator(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_get_current_time();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(uint8_t, lean_object*);
lean_object* l_Std_Http_Body_Stream_close(lean_object*);
lean_object* l_Std_Async_EAsync_instMonad___redArg();
lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Stream_send(lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Http_Protocol_H1_Machine_closeWithError(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentLength;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object*, lean_object*);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(uint8_t, lean_object*, lean_object*);
uint8_t l_Std_Http_instBEqMethod_beq(uint8_t, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_rejectOutgoingFraming(uint8_t, lean_object*);
uint16_t l_Std_Http_Status_toCode(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t, lean_object*, uint8_t);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
uint8_t l_Std_Http_Protocol_H1_Message_Head_version(uint8_t, lean_object*);
uint8_t l_Std_Http_instBEqVersion_beq(uint8_t, uint8_t);
lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
extern lean_object* l_Std_Http_Header_Name_date;
lean_object* l_Std_Time_DateTime_toHTTPDateString(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_CloseableChannel_new___redArg(lean_object*);
lean_object* l_Std_Http_Body_mkStream();
lean_object* l_Std_Http_Protocol_H1_Machine_canContinue(uint8_t, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
lean_object* l_Std_Channel_recvSelector___redArg(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
lean_object* l_Std_Async_Selector_sleep(lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Machine_step(uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Http_Config_toH1Config(lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object*);
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_Functor_discard(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Channel_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Server_instImpl___closed__0_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Http_Server_instImpl___closed__0_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_ = (const lean_object*)&l_Std_Http_Server_instImpl___closed__0_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
static const lean_string_object l_Std_Http_Server_instImpl___closed__1_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Http"};
static const lean_object* l_Std_Http_Server_instImpl___closed__1_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_ = (const lean_object*)&l_Std_Http_Server_instImpl___closed__1_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
static const lean_string_object l_Std_Http_Server_instImpl___closed__2_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l_Std_Http_Server_instImpl___closed__2_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_ = (const lean_object*)&l_Std_Http_Server_instImpl___closed__2_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
static const lean_string_object l_Std_Http_Server_instImpl___closed__3_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "RemoteAddr"};
static const lean_object* l_Std_Http_Server_instImpl___closed__3_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_ = (const lean_object*)&l_Std_Http_Server_instImpl___closed__3_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
static const lean_ctor_object l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Server_instImpl___closed__0_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value_aux_0),((lean_object*)&l_Std_Http_Server_instImpl___closed__1_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(62, 74, 245, 198, 196, 207, 141, 173)}};
static const lean_ctor_object l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value_aux_1),((lean_object*)&l_Std_Http_Server_instImpl___closed__2_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(3, 137, 82, 156, 27, 230, 60, 168)}};
static const lean_ctor_object l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value_aux_2),((lean_object*)&l_Std_Http_Server_instImpl___closed__3_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(136, 13, 149, 223, 202, 48, 50, 45)}};
static const lean_object* l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_ = (const lean_object*)&l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_ = (const lean_object*)&l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
LEAN_EXPORT const lean_object* l_Std_Http_Server_instTypeNameRemoteAddr = (const lean_object*)&l_Std_Http_Server_instImpl___closed__4_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8__value;
static const lean_string_object l_Std_Http_Server_instToStringRemoteAddr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Http_Server_instToStringRemoteAddr___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Server_instToStringRemoteAddr___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_Server_instToStringRemoteAddr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_Server_instToStringRemoteAddr___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Server_instToStringRemoteAddr___lam__0___closed__1_value;
static const lean_string_object l_Std_Http_Server_instToStringRemoteAddr___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]:"};
static const lean_object* l_Std_Http_Server_instToStringRemoteAddr___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Server_instToStringRemoteAddr___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_instToStringRemoteAddr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_instToStringRemoteAddr___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Server_instToStringRemoteAddr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_instToStringRemoteAddr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_instToStringRemoteAddr___closed__0 = (const lean_object*)&l_Std_Http_Server_instToStringRemoteAddr___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Server_instToStringRemoteAddr = (const lean_object*)&l_Std_Http_Server_instToStringRemoteAddr___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bytes_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bytes_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_responseBody_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_responseBody_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bodyInterest_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bodyInterest_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_response_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_response_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__2_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "UTC"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__1_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__2_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__4_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__0_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__4_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__8 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__8_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__8_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11;
static const lean_array_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_lift___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__2_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__2_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__7 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__7_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__7_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__8_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__2_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Invalid status line"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Invalid header"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Timeout"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Entity too large"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "URI too long"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unsupported version"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Invalid chunk"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Connection closed"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Bad message"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Too many headers"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Headers too large"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Other error: "};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 7}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "request header timeout"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1;
static lean_once_cell_t l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2;
static lean_once_cell_t l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3;
static const lean_array_object l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4 = (const lean_object*)&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4_value;
static const lean_array_object l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5 = (const lean_object*)&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5_value;
static const lean_ctor_object l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6 = (const lean_object*)&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6_value;
static lean_once_cell_t l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7;
static lean_once_cell_t l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_instToStringRemoteAddr___lam__0(lean_object* v_addr_15_){
_start:
{
if (lean_obj_tag(v_addr_15_) == 0)
{
lean_object* v_addr_16_; lean_object* v_addr_17_; uint16_t v_port_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_addr_16_ = lean_ctor_get(v_addr_15_, 0);
v_addr_17_ = lean_ctor_get(v_addr_16_, 0);
v_port_18_ = lean_ctor_get_uint16(v_addr_16_, sizeof(void*)*1);
v___x_19_ = lean_uv_ntop_v4(v_addr_17_);
v___x_20_ = ((lean_object*)(l_Std_Http_Server_instToStringRemoteAddr___lam__0___closed__0));
v___x_21_ = lean_string_append(v___x_19_, v___x_20_);
v___x_22_ = lean_uint16_to_nat(v_port_18_);
v___x_23_ = l_Nat_reprFast(v___x_22_);
v___x_24_ = lean_string_append(v___x_21_, v___x_23_);
lean_dec_ref(v___x_23_);
return v___x_24_;
}
else
{
lean_object* v_addr_25_; lean_object* v_addr_26_; uint16_t v_port_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_addr_25_ = lean_ctor_get(v_addr_15_, 0);
v_addr_26_ = lean_ctor_get(v_addr_25_, 0);
v_port_27_ = lean_ctor_get_uint16(v_addr_25_, sizeof(void*)*1);
v___x_28_ = ((lean_object*)(l_Std_Http_Server_instToStringRemoteAddr___lam__0___closed__1));
v___x_29_ = lean_uv_ntop_v6(v_addr_26_);
v___x_30_ = lean_string_append(v___x_28_, v___x_29_);
lean_dec_ref(v___x_29_);
v___x_31_ = ((lean_object*)(l_Std_Http_Server_instToStringRemoteAddr___lam__0___closed__2));
v___x_32_ = lean_string_append(v___x_30_, v___x_31_);
v___x_33_ = lean_uint16_to_nat(v_port_27_);
v___x_34_ = l_Nat_reprFast(v___x_33_);
v___x_35_ = lean_string_append(v___x_32_, v___x_34_);
lean_dec_ref(v___x_34_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_instToStringRemoteAddr___lam__0___boxed(lean_object* v_addr_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Http_Server_instToStringRemoteAddr___lam__0(v_addr_36_);
lean_dec_ref(v_addr_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___redArg(lean_object* v_x_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_obj_tag_nat(v_x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___redArg___boxed(lean_object* v_x_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___redArg(v_x_42_);
lean_dec(v_x_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl(lean_object* v_00_u03b2_44_, lean_object* v_x_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_tag_nat(v_x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl___boxed(lean_object* v_00_u03b2_47_, lean_object* v_x_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorIdx___impl(v_00_u03b2_47_, v_x_48_);
lean_dec(v_x_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(lean_object* v_t_50_, lean_object* v_k_51_){
_start:
{
switch(lean_obj_tag(v_t_50_))
{
case 0:
{
lean_object* v_x_52_; lean_object* v___x_53_; 
v_x_52_ = lean_ctor_get(v_t_50_, 0);
lean_inc(v_x_52_);
lean_dec_ref_known(v_t_50_, 1);
v___x_53_ = lean_apply_1(v_k_51_, v_x_52_);
return v___x_53_;
}
case 1:
{
lean_object* v_x_54_; lean_object* v___x_55_; 
v_x_54_ = lean_ctor_get(v_t_50_, 0);
lean_inc(v_x_54_);
lean_dec_ref_known(v_t_50_, 1);
v___x_55_ = lean_apply_1(v_k_51_, v_x_54_);
return v___x_55_;
}
case 2:
{
uint8_t v_x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_x_56_ = lean_ctor_get_uint8(v_t_50_, 0);
lean_dec_ref_known(v_t_50_, 0);
v___x_57_ = lean_box(v_x_56_);
v___x_58_ = lean_apply_1(v_k_51_, v___x_57_);
return v___x_58_;
}
case 3:
{
lean_object* v_x_59_; lean_object* v___x_60_; 
v_x_59_ = lean_ctor_get(v_t_50_, 0);
lean_inc_ref(v_x_59_);
lean_dec_ref_known(v_t_50_, 1);
v___x_60_ = lean_apply_1(v_k_51_, v_x_59_);
return v___x_60_;
}
default: 
{
lean_dec(v_t_50_);
return v_k_51_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim(lean_object* v_00_u03b2_61_, lean_object* v_motive_62_, lean_object* v_ctorIdx_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_k_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_64_, v_k_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___boxed(lean_object* v_00_u03b2_68_, lean_object* v_motive_69_, lean_object* v_ctorIdx_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_k_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim(v_00_u03b2_68_, v_motive_69_, v_ctorIdx_70_, v_t_71_, v_h_72_, v_k_73_);
lean_dec(v_ctorIdx_70_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bytes_elim___redArg(lean_object* v_t_75_, lean_object* v_bytes_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_75_, v_bytes_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bytes_elim(lean_object* v_00_u03b2_78_, lean_object* v_motive_79_, lean_object* v_t_80_, lean_object* v_h_81_, lean_object* v_bytes_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_80_, v_bytes_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_responseBody_elim___redArg(lean_object* v_t_84_, lean_object* v_responseBody_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_84_, v_responseBody_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_responseBody_elim(lean_object* v_00_u03b2_87_, lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_responseBody_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_89_, v_responseBody_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bodyInterest_elim___redArg(lean_object* v_t_93_, lean_object* v_bodyInterest_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_93_, v_bodyInterest_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_bodyInterest_elim(lean_object* v_00_u03b2_96_, lean_object* v_motive_97_, lean_object* v_t_98_, lean_object* v_h_99_, lean_object* v_bodyInterest_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_98_, v_bodyInterest_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_response_elim___redArg(lean_object* v_t_102_, lean_object* v_response_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_102_, v_response_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_response_elim(lean_object* v_00_u03b2_105_, lean_object* v_motive_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_response_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_107_, v_response_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim___redArg(lean_object* v_t_111_, lean_object* v_timeout_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_111_, v_timeout_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim(lean_object* v_00_u03b2_114_, lean_object* v_motive_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_timeout_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_116_, v_timeout_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim___redArg(lean_object* v_t_120_, lean_object* v_shutdown_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_120_, v_shutdown_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim(lean_object* v_00_u03b2_123_, lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_shutdown_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_125_, v_shutdown_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim___redArg(lean_object* v_t_129_, lean_object* v_close_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_129_, v_close_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim(lean_object* v_00_u03b2_132_, lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_close_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_134_, v_close_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_158_; 
v_a_150_ = lean_ctor_get(v_x_146_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_146_);
if (v_isSharedCheck_158_ == 0)
{
v___x_152_ = v_x_146_;
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v_x_146_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_158_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_157_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
}
else
{
lean_object* v_a_159_; 
v_a_159_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v_x_146_, 1);
if (lean_obj_tag(v_a_159_) == 1)
{
lean_object* v_val_160_; 
v_val_160_ = lean_ctor_get(v_a_159_, 0);
lean_inc(v_val_160_);
lean_dec_ref_known(v_a_159_, 1);
if (lean_obj_tag(v_val_160_) == 0)
{
lean_object* v___x_161_; 
v___x_161_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3));
return v___x_161_;
}
else
{
lean_dec(v_val_160_);
goto v___jp_148_;
}
}
else
{
lean_dec(v_a_159_);
goto v___jp_148_;
}
}
v___jp_148_:
{
lean_object* v___x_149_; 
v___x_149_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__1));
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed(lean_object* v_x_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(v_x_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(lean_object* v_x_169_){
_start:
{
if (lean_obj_tag(v_x_169_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_179_; 
v_a_171_ = lean_ctor_get(v_x_169_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_169_);
if (v_isSharedCheck_179_ == 0)
{
v___x_173_ = v_x_169_;
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v_x_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_178_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; 
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
}
else
{
lean_object* v___x_180_; 
lean_dec_ref_known(v_x_169_, 1);
v___x_180_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1));
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed(lean_object* v_x_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(v_x_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(lean_object* v_inst_184_, lean_object* v_handler_185_, lean_object* v___f_186_, lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v_a_189_; lean_object* v_onFailure_190_; lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_a_189_ = lean_ctor_get(v_x_187_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v_x_187_, 1);
v_onFailure_190_ = lean_ctor_get(v_inst_184_, 2);
lean_inc_ref(v_onFailure_190_);
lean_dec_ref(v_inst_184_);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = 0;
v___x_193_ = lean_apply_3(v_onFailure_190_, v_handler_185_, v_a_189_, lean_box(0));
v___x_194_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_191_, v___x_192_, v___x_193_, v___f_186_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; 
lean_dec_ref(v___f_186_);
lean_dec(v_handler_185_);
lean_dec_ref(v_inst_184_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v_x_187_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed(lean_object* v_inst_196_, lean_object* v_handler_197_, lean_object* v___f_198_, lean_object* v_x_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(v_inst_196_, v_handler_197_, v___f_198_, v_x_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(lean_object* v_x_202_){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_204_, 0, v_x_202_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed(lean_object* v_x_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(v_x_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(uint8_t v_x_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_212_, 0, v_x_210_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed(lean_object* v_x_215_, lean_object* v___y_216_){
_start:
{
uint8_t v_x_3730__boxed_217_; lean_object* v_res_218_; 
v_x_3730__boxed_217_ = lean_unbox(v_x_215_);
v_res_218_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(v_x_3730__boxed_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(lean_object* v_x_219_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v_x_219_);
v___x_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed(lean_object* v_x_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(v_x_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object* v_x_227_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v_x_227_);
v___x_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object* v_x_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(v_x_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object* v_x_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___closed__3));
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object* v_x_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(v_x_238_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object* v_x_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1));
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object* v_x_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v_x_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object* v___f_247_, lean_object* v_response_248_, lean_object* v___x_249_, lean_object* v___f_250_, lean_object* v_requestBody_251_, lean_object* v___f_252_, lean_object* v_responseBody_253_, lean_object* v_inst_254_, lean_object* v___f_255_, lean_object* v_____r_256_, lean_object* v_selectables_257_){
_start:
{
lean_object* v_selectables_260_; lean_object* v_selectables_266_; lean_object* v_selectables_272_; 
if (lean_obj_tag(v_responseBody_253_) == 1)
{
lean_object* v_val_277_; lean_object* v_recvSelector_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_selectables_281_; 
v_val_277_ = lean_ctor_get(v_responseBody_253_, 0);
lean_inc(v_val_277_);
lean_dec_ref_known(v_responseBody_253_, 1);
v_recvSelector_278_ = lean_ctor_get(v_inst_254_, 3);
lean_inc_ref(v_recvSelector_278_);
lean_dec_ref(v_inst_254_);
v___x_279_ = lean_apply_1(v_recvSelector_278_, v_val_277_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___f_255_);
v_selectables_281_ = lean_array_push(v_selectables_257_, v___x_280_);
v_selectables_272_ = v_selectables_281_;
goto v___jp_271_;
}
else
{
lean_dec_ref(v___f_255_);
lean_dec_ref(v_inst_254_);
lean_dec(v_responseBody_253_);
v_selectables_272_ = v_selectables_257_;
goto v___jp_271_;
}
v___jp_259_:
{
lean_object* v___x_261_; uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = 0;
v___x_263_ = l_Std_Async_Selectable_one___redArg(v_selectables_260_);
v___x_264_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_261_, v___x_262_, v___x_263_, v___f_247_);
return v___x_264_;
}
v___jp_265_:
{
if (lean_obj_tag(v_response_248_) == 1)
{
lean_object* v_val_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v_selectables_270_; 
v_val_267_ = lean_ctor_get(v_response_248_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v_response_248_, 1);
v___x_268_ = l_Std_Channel_recvSelector___redArg(v___x_249_, v_val_267_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___f_250_);
v_selectables_270_ = lean_array_push(v_selectables_266_, v___x_269_);
v_selectables_260_ = v_selectables_270_;
goto v___jp_259_;
}
else
{
lean_dec_ref(v___f_250_);
lean_dec_ref(v___x_249_);
lean_dec(v_response_248_);
v_selectables_260_ = v_selectables_266_;
goto v___jp_259_;
}
}
v___jp_271_:
{
if (lean_obj_tag(v_requestBody_251_) == 1)
{
lean_object* v_val_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_selectables_276_; 
v_val_273_ = lean_ctor_get(v_requestBody_251_, 0);
lean_inc(v_val_273_);
lean_dec_ref_known(v_requestBody_251_, 1);
v___x_274_ = l_Std_Http_Body_Stream_interestSelector(v_val_273_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v___f_252_);
v_selectables_276_ = lean_array_push(v_selectables_272_, v___x_275_);
v_selectables_266_ = v_selectables_276_;
goto v___jp_265_;
}
else
{
lean_dec_ref(v___f_252_);
lean_dec(v_requestBody_251_);
v_selectables_266_ = v_selectables_272_;
goto v___jp_265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object* v___f_282_, lean_object* v_response_283_, lean_object* v___x_284_, lean_object* v___f_285_, lean_object* v_requestBody_286_, lean_object* v___f_287_, lean_object* v_responseBody_288_, lean_object* v_inst_289_, lean_object* v___f_290_, lean_object* v_____r_291_, lean_object* v_selectables_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_282_, v_response_283_, v___x_284_, v___f_285_, v_requestBody_286_, v___f_287_, v_responseBody_288_, v_inst_289_, v___f_290_, v_____r_291_, v_selectables_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object* v_token_295_, lean_object* v___f_296_, lean_object* v_x_297_){
_start:
{
lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = 0;
v___x_301_ = l_Std_CancellationToken_getCancellationReason(v_token_295_);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
v___x_304_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_299_, v___x_300_, v___x_303_, v___f_296_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object* v_token_305_, lean_object* v___f_306_, lean_object* v_x_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(v_token_305_, v___f_306_, v_x_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(lean_object* v___f_310_, lean_object* v_selectables_311_, lean_object* v___f_312_, lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v___f_312_);
lean_dec_ref(v_selectables_311_);
lean_dec_ref(v___f_310_);
v_a_315_ = lean_ctor_get(v_x_313_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_323_ == 0)
{
v___x_317_ = v_x_313_;
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v_x_313_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_323_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_322_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; 
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_a_324_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v_x_313_, 1);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v_a_324_);
lean_ctor_set(v___x_325_, 1, v___f_310_);
v___x_326_ = lean_array_push(v_selectables_311_, v___x_325_);
v___x_327_ = lean_box(0);
v___x_328_ = lean_apply_3(v___f_312_, v___x_327_, v___x_326_, lean_box(0));
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed(lean_object* v___f_329_, lean_object* v_selectables_330_, lean_object* v___f_331_, lean_object* v_x_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(v___f_329_, v_selectables_330_, v___f_331_, v_x_332_);
return v_res_334_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(1000000000u);
v___x_336_ = lean_nat_to_int(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(1000u);
v___x_338_ = lean_nat_to_int(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(1000000u);
v___x_340_ = lean_nat_to_int(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(lean_object* v_val_341_, lean_object* v___f_342_, lean_object* v_x_343_){
_start:
{
if (lean_obj_tag(v_x_343_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v___f_342_);
v_a_345_ = lean_ctor_get(v_x_343_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v_x_343_);
if (v_isSharedCheck_353_ == 0)
{
v___x_347_ = v_x_343_;
v_isShared_348_ = v_isSharedCheck_353_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v_x_343_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_353_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_352_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; 
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
}
else
{
lean_object* v_a_354_; lean_object* v_second_355_; lean_object* v_nano_356_; lean_object* v_second_357_; lean_object* v_nano_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_nanos_363_; lean_object* v___x_364_; lean_object* v_nanos_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_second_368_; lean_object* v_nano_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_millis_374_; lean_object* v___x_375_; uint8_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_a_354_ = lean_ctor_get(v_x_343_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v_x_343_, 1);
v_second_355_ = lean_ctor_get(v_a_354_, 0);
lean_inc(v_second_355_);
v_nano_356_ = lean_ctor_get(v_a_354_, 1);
lean_inc(v_nano_356_);
lean_dec(v_a_354_);
v_second_357_ = lean_ctor_get(v_val_341_, 0);
v_nano_358_ = lean_ctor_get(v_val_341_, 1);
v___x_359_ = lean_int_neg(v_second_355_);
lean_dec(v_second_355_);
v___x_360_ = lean_int_neg(v_nano_356_);
lean_dec(v_nano_356_);
v___x_361_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_362_ = lean_int_mul(v_second_357_, v___x_361_);
v_nanos_363_ = lean_int_add(v___x_362_, v_nano_358_);
lean_dec(v___x_362_);
v___x_364_ = lean_int_mul(v___x_359_, v___x_361_);
lean_dec(v___x_359_);
v_nanos_365_ = lean_int_add(v___x_364_, v___x_360_);
lean_dec(v___x_360_);
lean_dec(v___x_364_);
v___x_366_ = lean_int_add(v_nanos_363_, v_nanos_365_);
lean_dec(v_nanos_365_);
lean_dec(v_nanos_363_);
v___x_367_ = l_Std_Time_Duration_ofNanoseconds(v___x_366_);
lean_dec(v___x_366_);
v_second_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_second_368_);
v_nano_369_ = lean_ctor_get(v___x_367_, 1);
lean_inc(v_nano_369_);
lean_dec_ref(v___x_367_);
v___x_370_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1);
v___x_371_ = lean_int_mul(v_second_368_, v___x_370_);
lean_dec(v_second_368_);
v___x_372_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_373_ = lean_int_ediv(v_nano_369_, v___x_372_);
lean_dec(v_nano_369_);
v_millis_374_ = lean_int_add(v___x_371_, v___x_373_);
lean_dec(v___x_373_);
lean_dec(v___x_371_);
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = 0;
v___x_377_ = l_Std_Async_Selector_sleep(v_millis_374_);
lean_dec(v_millis_374_);
v___x_378_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_375_, v___x_376_, v___x_377_, v___f_342_);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___boxed(lean_object* v_val_379_, lean_object* v___f_380_, lean_object* v_x_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(v_val_379_, v___f_380_, v_x_381_);
lean_dec_ref(v_val_379_);
return v_res_383_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = l_instInhabitedError;
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_config_397_, lean_object* v_handler_398_, lean_object* v_sources_399_){
_start:
{
lean_object* v___y_402_; lean_object* v___y_403_; uint8_t v___y_404_; lean_object* v_val_405_; lean_object* v_socket_408_; lean_object* v_expect_409_; lean_object* v_response_410_; lean_object* v_responseBody_411_; lean_object* v_requestBody_412_; lean_object* v_timeout_413_; lean_object* v_keepAliveTimeout_414_; lean_object* v_headerTimeout_415_; lean_object* v_connectionContext_416_; lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___f_419_; lean_object* v___f_420_; lean_object* v___f_421_; lean_object* v___f_422_; lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___x_426_; lean_object* v___f_427_; lean_object* v___y_429_; lean_object* v___y_479_; 
v_socket_408_ = lean_ctor_get(v_sources_399_, 0);
lean_inc(v_socket_408_);
v_expect_409_ = lean_ctor_get(v_sources_399_, 1);
lean_inc(v_expect_409_);
v_response_410_ = lean_ctor_get(v_sources_399_, 2);
lean_inc_n(v_response_410_, 2);
v_responseBody_411_ = lean_ctor_get(v_sources_399_, 3);
lean_inc_n(v_responseBody_411_, 2);
v_requestBody_412_ = lean_ctor_get(v_sources_399_, 4);
lean_inc_n(v_requestBody_412_, 2);
v_timeout_413_ = lean_ctor_get(v_sources_399_, 5);
lean_inc(v_timeout_413_);
v_keepAliveTimeout_414_ = lean_ctor_get(v_sources_399_, 6);
lean_inc(v_keepAliveTimeout_414_);
v_headerTimeout_415_ = lean_ctor_get(v_sources_399_, 7);
lean_inc(v_headerTimeout_415_);
v_connectionContext_416_ = lean_ctor_get(v_sources_399_, 8);
lean_inc_ref(v_connectionContext_416_);
lean_dec_ref(v_sources_399_);
v___f_417_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0));
v___f_418_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1));
v___f_419_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_419_, 0, v_inst_395_);
lean_closure_set(v___f_419_, 1, v_handler_398_);
lean_closure_set(v___f_419_, 2, v___f_418_);
v___f_420_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2));
v___f_421_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3));
v___f_422_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4));
v___f_423_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5));
v___f_424_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6));
v___f_425_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7));
v___x_426_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8);
lean_inc_ref(v_inst_396_);
lean_inc_ref(v___f_419_);
v___f_427_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed), 12, 9);
lean_closure_set(v___f_427_, 0, v___f_419_);
lean_closure_set(v___f_427_, 1, v_response_410_);
lean_closure_set(v___f_427_, 2, v___x_426_);
lean_closure_set(v___f_427_, 3, v___f_420_);
lean_closure_set(v___f_427_, 4, v_requestBody_412_);
lean_closure_set(v___f_427_, 5, v___f_421_);
lean_closure_set(v___f_427_, 6, v_responseBody_411_);
lean_closure_set(v___f_427_, 7, v_inst_396_);
lean_closure_set(v___f_427_, 8, v___f_422_);
if (lean_obj_tag(v_expect_409_) == 0)
{
lean_object* v_defaultPayloadBytes_482_; 
v_defaultPayloadBytes_482_ = lean_ctor_get(v_config_397_, 8);
lean_inc(v_defaultPayloadBytes_482_);
v___y_479_ = v_defaultPayloadBytes_482_;
goto v___jp_478_;
}
else
{
lean_object* v_val_483_; 
v_val_483_ = lean_ctor_get(v_expect_409_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v_expect_409_, 1);
v___y_479_ = v_val_483_;
goto v___jp_478_;
}
v___jp_401_:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_val_405_);
v___x_407_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_403_, v___y_404_, v___x_406_, v___y_402_);
return v___x_407_;
}
v___jp_428_:
{
lean_object* v_token_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v_selectables_436_; 
v_token_430_ = lean_ctor_get(v_connectionContext_416_, 1);
lean_inc_ref_n(v_token_430_, 2);
lean_dec_ref(v_connectionContext_416_);
v___f_431_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 4, 2);
lean_closure_set(v___f_431_, 0, v_token_430_);
lean_closure_set(v___f_431_, 1, v___f_417_);
v___x_432_ = l_Std_CancellationToken_selector(v_token_430_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___f_431_);
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_mk_empty_array_with_capacity(v___x_434_);
v_selectables_436_ = lean_array_push(v___x_435_, v___x_433_);
if (lean_obj_tag(v_socket_408_) == 1)
{
lean_object* v_val_437_; lean_object* v_recvSelector_438_; uint64_t v_expectedBytes_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_selectables_443_; 
lean_dec_ref(v___f_419_);
lean_dec(v_requestBody_412_);
lean_dec(v_responseBody_411_);
lean_dec(v_response_410_);
lean_dec_ref(v_inst_396_);
v_val_437_ = lean_ctor_get(v_socket_408_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v_socket_408_, 1);
v_recvSelector_438_ = lean_ctor_get(v_inst_394_, 2);
lean_inc_ref(v_recvSelector_438_);
lean_dec_ref(v_inst_394_);
v_expectedBytes_439_ = lean_uint64_of_nat(v___y_429_);
lean_dec(v___y_429_);
v___x_440_ = lean_box_uint64(v_expectedBytes_439_);
v___x_441_ = lean_apply_2(v_recvSelector_438_, v_val_437_, v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___f_423_);
v_selectables_443_ = lean_array_push(v_selectables_436_, v___x_442_);
if (lean_obj_tag(v_keepAliveTimeout_414_) == 0)
{
if (lean_obj_tag(v_headerTimeout_415_) == 1)
{
lean_object* v_val_444_; lean_object* v___f_445_; lean_object* v___f_446_; lean_object* v___x_447_; uint8_t v___x_448_; lean_object* v___x_449_; 
lean_dec(v_timeout_413_);
v_val_444_ = lean_ctor_get(v_headerTimeout_415_, 0);
lean_inc(v_val_444_);
lean_dec_ref_known(v_headerTimeout_415_, 1);
v___f_445_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_445_, 0, v___f_424_);
lean_closure_set(v___f_445_, 1, v_selectables_443_);
lean_closure_set(v___f_445_, 2, v___f_427_);
v___f_446_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___boxed), 4, 2);
lean_closure_set(v___f_446_, 0, v_val_444_);
lean_closure_set(v___f_446_, 1, v___f_445_);
v___x_447_ = lean_unsigned_to_nat(0u);
v___x_448_ = 0;
v___x_449_ = lean_get_current_time();
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set_tag(v___x_452_, 1);
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
v___y_402_ = v___f_446_;
v___y_403_ = v___x_447_;
v___y_404_ = v___x_448_;
v_val_405_ = v___x_455_;
goto v___jp_401_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_a_458_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_449_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_449_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 0);
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
v___y_402_ = v___f_446_;
v___y_403_ = v___x_447_;
v___y_404_ = v___x_448_;
v_val_405_ = v___x_463_;
goto v___jp_401_;
}
}
}
}
else
{
lean_object* v___f_466_; lean_object* v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_headerTimeout_415_);
v___f_466_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_466_, 0, v___f_424_);
lean_closure_set(v___f_466_, 1, v_selectables_443_);
lean_closure_set(v___f_466_, 2, v___f_427_);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = 0;
v___x_469_ = l_Std_Async_Selector_sleep(v_timeout_413_);
lean_dec(v_timeout_413_);
v___x_470_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_467_, v___x_468_, v___x_469_, v___f_466_);
return v___x_470_;
}
}
else
{
lean_object* v___f_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec_ref_known(v_keepAliveTimeout_414_, 1);
lean_dec(v_headerTimeout_415_);
v___f_471_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 5, 3);
lean_closure_set(v___f_471_, 0, v___f_425_);
lean_closure_set(v___f_471_, 1, v_selectables_443_);
lean_closure_set(v___f_471_, 2, v___f_427_);
v___x_472_ = 0;
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = l_Std_Async_Selector_sleep(v_timeout_413_);
lean_dec(v_timeout_413_);
v___x_475_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_473_, v___x_472_, v___x_474_, v___f_471_);
return v___x_475_;
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec(v___y_429_);
lean_dec_ref(v___f_427_);
lean_dec(v_headerTimeout_415_);
lean_dec(v_keepAliveTimeout_414_);
lean_dec(v_timeout_413_);
lean_dec(v_socket_408_);
lean_dec_ref(v_inst_394_);
v___x_476_ = lean_box(0);
v___x_477_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_419_, v_response_410_, v___x_426_, v___f_420_, v_requestBody_412_, v___f_421_, v_responseBody_411_, v_inst_396_, v___f_422_, v___x_476_, v_selectables_436_);
return v___x_477_;
}
}
v___jp_478_:
{
lean_object* v_maximumRecvSize_480_; uint8_t v___x_481_; 
v_maximumRecvSize_480_ = lean_ctor_get(v_config_397_, 7);
lean_inc(v_maximumRecvSize_480_);
lean_dec_ref(v_config_397_);
v___x_481_ = lean_nat_dec_le(v___y_479_, v_maximumRecvSize_480_);
if (v___x_481_ == 0)
{
lean_dec(v___y_479_);
v___y_429_ = v_maximumRecvSize_480_;
goto v___jp_428_;
}
else
{
lean_dec(v_maximumRecvSize_480_);
v___y_429_ = v___y_479_;
goto v___jp_428_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_config_487_, lean_object* v_handler_488_, lean_object* v_sources_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_484_, v_inst_485_, v_inst_486_, v_config_487_, v_handler_488_, v_sources_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object* v_00_u03b1_492_, lean_object* v_00_u03c3_493_, lean_object* v_00_u03b2_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_config_498_, lean_object* v_handler_499_, lean_object* v_sources_500_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_495_, v_inst_496_, v_inst_497_, v_config_498_, v_handler_499_, v_sources_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object* v_00_u03b1_503_, lean_object* v_00_u03c3_504_, lean_object* v_00_u03b2_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_config_509_, lean_object* v_handler_510_, lean_object* v_sources_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(v_00_u03b1_503_, v_00_u03c3_504_, v_00_u03b2_505_, v_inst_506_, v_inst_507_, v_inst_508_, v_config_509_, v_handler_510_, v_sources_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(lean_object* v_machine_514_, lean_object* v_x_515_){
_start:
{
lean_object* v___y_518_; uint8_t v___y_519_; 
if (lean_obj_tag(v_x_515_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_532_; 
lean_dec_ref(v_machine_514_);
v_a_524_ = lean_ctor_get(v_x_515_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v_x_515_);
if (v_isSharedCheck_532_ == 0)
{
v___x_526_ = v_x_515_;
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v_x_515_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_531_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___y_535_; uint8_t v___x_541_; 
v_a_533_ = lean_ctor_get(v_x_515_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v_x_515_, 1);
v___x_541_ = lean_unbox(v_a_533_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
v___x_542_ = lean_box(40);
v___y_535_ = v___x_542_;
goto v___jp_534_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = lean_box(0);
v___y_535_ = v___x_543_;
goto v___jp_534_;
}
v___jp_534_:
{
uint8_t v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = 0;
lean_inc(v___y_535_);
v___x_537_ = l_Std_Http_Protocol_H1_Machine_canContinue(v___x_536_, v_machine_514_, v___y_535_);
v___x_538_ = lean_unbox(v_a_533_);
lean_dec(v_a_533_);
if (v___x_538_ == 0)
{
uint8_t v___x_539_; 
v___x_539_ = 1;
v___y_518_ = v___x_537_;
v___y_519_ = v___x_539_;
goto v___jp_517_;
}
else
{
uint8_t v___x_540_; 
v___x_540_ = 0;
v___y_518_ = v___x_537_;
v___y_519_ = v___x_540_;
goto v___jp_517_;
}
}
}
v___jp_517_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_520_ = lean_box(v___y_519_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___y_518_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object* v_machine_544_, lean_object* v_x_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(v_machine_544_, v_x_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t v___y_548_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_box(v___y_548_);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v___y_1377__boxed_555_; lean_object* v_res_556_; 
v___y_1377__boxed_555_ = lean_unbox(v___y_553_);
v_res_556_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_1377__boxed_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_559_; 
v_a_558_ = lean_ctor_get(v_x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v_x_557_, 1);
v___x_559_ = lean_task_pure(v_a_558_);
return v___x_559_;
}
else
{
lean_object* v_a_560_; 
v_a_560_ = lean_ctor_get(v_x_557_, 0);
lean_inc_ref(v_a_560_);
lean_dec_ref_known(v_x_557_, 1);
return v_a_560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object* v_a_561_, lean_object* v_x_562_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref_known(v_x_562_, 1);
v___x_564_ = 0;
v___x_565_ = lean_box(0);
v___x_566_ = lean_box(v___x_564_);
v___x_567_ = l_Std_Channel_send___redArg(v_a_561_, v___x_566_);
lean_dec_ref(v___x_567_);
return v___x_565_;
}
else
{
lean_object* v_a_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_a_568_ = lean_ctor_get(v_x_562_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v_x_562_, 1);
v___x_569_ = lean_box(0);
v___x_570_ = l_Std_Channel_send___redArg(v_a_561_, v_a_568_);
lean_dec_ref(v___x_570_);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object* v_a_571_, lean_object* v_x_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(v_a_571_, v_x_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t v___x_575_, lean_object* v_x_576_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_box(v___x_575_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object* v___x_581_, lean_object* v_x_582_, lean_object* v___y_583_){
_start:
{
uint8_t v___x_1421__boxed_584_; lean_object* v_res_585_; 
v___x_1421__boxed_584_ = lean_unbox(v___x_581_);
v_res_585_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_1421__boxed_584_, v_x_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object* v_connectionContext_586_, uint8_t v___x_587_, lean_object* v_a_588_, lean_object* v___f_589_, lean_object* v___f_590_, lean_object* v___x_591_, uint8_t v___x_592_, lean_object* v___f_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v___f_593_);
lean_dec(v___x_591_);
lean_dec_ref(v___f_590_);
lean_dec_ref(v___f_589_);
lean_dec_ref(v_a_588_);
lean_dec_ref(v_connectionContext_586_);
v_a_596_ = lean_ctor_get(v_x_594_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_594_);
if (v_isSharedCheck_604_ == 0)
{
v___x_598_ = v_x_594_;
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v_x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_604_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_603_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; 
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
}
else
{
lean_object* v_a_605_; lean_object* v_token_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_a_605_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v_x_594_, 1);
v_token_606_ = lean_ctor_get(v_connectionContext_586_, 1);
lean_inc_ref(v_token_606_);
lean_dec_ref(v_connectionContext_586_);
v___x_607_ = lean_box(v___x_587_);
v___x_608_ = l_Std_Channel_recvSelector___redArg(v___x_607_, v_a_588_);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___f_589_);
v___x_610_ = l_Std_CancellationToken_selector(v_token_606_);
lean_inc_ref(v___f_590_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___f_590_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_a_605_);
lean_ctor_set(v___x_612_, 1, v___f_590_);
v___x_613_ = lean_unsigned_to_nat(3u);
v___x_614_ = lean_mk_empty_array_with_capacity(v___x_613_);
v___x_615_ = lean_array_push(v___x_614_, v___x_609_);
v___x_616_ = lean_array_push(v___x_615_, v___x_611_);
v___x_617_ = lean_array_push(v___x_616_, v___x_612_);
v___x_618_ = l_Std_Async_Selectable_one___redArg(v___x_617_);
v___x_619_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_591_, v___x_592_, v___x_618_, v___f_593_);
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object* v_connectionContext_620_, lean_object* v___x_621_, lean_object* v_a_622_, lean_object* v___f_623_, lean_object* v___f_624_, lean_object* v___x_625_, lean_object* v___x_626_, lean_object* v___f_627_, lean_object* v_x_628_, lean_object* v___y_629_){
_start:
{
uint8_t v___x_1436__boxed_630_; uint8_t v___x_1441__boxed_631_; lean_object* v_res_632_; 
v___x_1436__boxed_630_ = lean_unbox(v___x_621_);
v___x_1441__boxed_631_ = lean_unbox(v___x_626_);
v_res_632_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_620_, v___x_1436__boxed_630_, v_a_622_, v___f_623_, v___f_624_, v___x_625_, v___x_1441__boxed_631_, v___f_627_, v_x_628_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object* v_config_633_, lean_object* v___x_634_, uint8_t v___x_635_, lean_object* v___f_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v___f_636_);
lean_dec(v___x_634_);
v_a_639_ = lean_ctor_get(v_x_637_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_647_ == 0)
{
v___x_641_ = v_x_637_;
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v_x_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_646_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; 
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
}
else
{
lean_object* v_lingeringTimeout_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec_ref_known(v_x_637_, 1);
v_lingeringTimeout_648_ = lean_ctor_get(v_config_633_, 4);
v___x_649_ = l_Std_Async_Selector_sleep(v_lingeringTimeout_648_);
v___x_650_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_634_, v___x_635_, v___x_649_, v___f_636_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object* v_config_651_, lean_object* v___x_652_, lean_object* v___x_653_, lean_object* v___f_654_, lean_object* v_x_655_, lean_object* v___y_656_){
_start:
{
uint8_t v___x_1510__boxed_657_; lean_object* v_res_658_; 
v___x_1510__boxed_657_ = lean_unbox(v___x_653_);
v_res_658_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_651_, v___x_652_, v___x_1510__boxed_657_, v___f_654_, v_x_655_);
lean_dec_ref(v_config_651_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object* v_connectionContext_662_, uint8_t v___x_663_, lean_object* v_a_664_, lean_object* v___f_665_, lean_object* v___x_666_, lean_object* v___f_667_, lean_object* v_config_668_, lean_object* v___f_669_, lean_object* v_x_670_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v___f_669_);
lean_dec_ref(v_config_668_);
lean_dec_ref(v___f_667_);
lean_dec(v___x_666_);
lean_dec_ref(v___f_665_);
lean_dec_ref(v_a_664_);
lean_dec_ref(v_connectionContext_662_);
v_a_672_ = lean_ctor_get(v_x_670_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_x_670_);
if (v_isSharedCheck_680_ == 0)
{
v___x_674_ = v_x_670_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v_x_670_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_679_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; 
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
return v___x_678_;
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_698_; 
v_a_681_ = lean_ctor_get(v_x_670_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v_x_670_);
if (v_isSharedCheck_698_ == 0)
{
v___x_683_ = v_x_670_;
v_isShared_684_ = v_isSharedCheck_698_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v_x_670_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_698_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
uint8_t v___x_685_; lean_object* v___f_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___f_689_; lean_object* v___x_690_; lean_object* v___f_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_685_ = 0;
v___f_686_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0));
v___x_687_ = lean_box(v___x_663_);
v___x_688_ = lean_box(v___x_685_);
lean_inc_n(v___x_666_, 3);
v___f_689_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed), 10, 8);
lean_closure_set(v___f_689_, 0, v_connectionContext_662_);
lean_closure_set(v___f_689_, 1, v___x_687_);
lean_closure_set(v___f_689_, 2, v_a_664_);
lean_closure_set(v___f_689_, 3, v___f_665_);
lean_closure_set(v___f_689_, 4, v___f_686_);
lean_closure_set(v___f_689_, 5, v___x_666_);
lean_closure_set(v___f_689_, 6, v___x_688_);
lean_closure_set(v___f_689_, 7, v___f_667_);
v___x_690_ = lean_box(v___x_685_);
v___f_691_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_691_, 0, v_config_668_);
lean_closure_set(v___f_691_, 1, v___x_666_);
lean_closure_set(v___f_691_, 2, v___x_690_);
lean_closure_set(v___f_691_, 3, v___f_689_);
v___x_692_ = l_BaseIO_chainTask___redArg(v_a_681_, v___f_669_, v___x_666_, v___x_685_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_692_);
v___x_694_ = v___x_683_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_697_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
v___x_696_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_666_, v___x_685_, v___x_695_, v___f_691_);
return v___x_696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object* v_connectionContext_699_, lean_object* v___x_700_, lean_object* v_a_701_, lean_object* v___f_702_, lean_object* v___x_703_, lean_object* v___f_704_, lean_object* v_config_705_, lean_object* v___f_706_, lean_object* v_x_707_, lean_object* v___y_708_){
_start:
{
uint8_t v___x_1550__boxed_709_; lean_object* v_res_710_; 
v___x_1550__boxed_709_ = lean_unbox(v___x_700_);
v_res_710_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v_connectionContext_699_, v___x_1550__boxed_709_, v_a_701_, v___f_702_, v___x_703_, v___f_704_, v_config_705_, v___f_706_, v_x_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object* v_inst_711_, lean_object* v_handler_712_, lean_object* v_head_713_, lean_object* v_connectionContext_714_, uint8_t v___x_715_, lean_object* v___f_716_, lean_object* v___f_717_, lean_object* v_config_718_, lean_object* v___f_719_, lean_object* v_x_720_){
_start:
{
if (lean_obj_tag(v_x_720_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v___f_719_);
lean_dec_ref(v_config_718_);
lean_dec_ref(v___f_717_);
lean_dec_ref(v___f_716_);
lean_dec_ref(v_connectionContext_714_);
lean_dec_ref(v_head_713_);
lean_dec(v_handler_712_);
lean_dec_ref(v_inst_711_);
v_a_722_ = lean_ctor_get(v_x_720_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_730_ == 0)
{
v___x_724_ = v_x_720_;
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v_x_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_729_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_751_; 
v_a_731_ = lean_ctor_get(v_x_720_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v_x_720_);
if (v_isSharedCheck_751_ == 0)
{
v___x_733_ = v_x_720_;
v_isShared_734_ = v_isSharedCheck_751_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v_x_720_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_751_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_onContinue_735_; lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___f_740_; uint8_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v_onContinue_735_ = lean_ctor_get(v_inst_711_, 3);
lean_inc_ref(v_onContinue_735_);
lean_dec_ref(v_inst_711_);
lean_inc(v_a_731_);
v___f_736_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_736_, 0, v_a_731_);
v___x_737_ = lean_apply_2(v_onContinue_735_, v_handler_712_, v_head_713_);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_box(v___x_715_);
v___f_740_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_740_, 0, v_connectionContext_714_);
lean_closure_set(v___f_740_, 1, v___x_739_);
lean_closure_set(v___f_740_, 2, v_a_731_);
lean_closure_set(v___f_740_, 3, v___f_716_);
lean_closure_set(v___f_740_, 4, v___x_738_);
lean_closure_set(v___f_740_, 5, v___f_717_);
lean_closure_set(v___f_740_, 6, v_config_718_);
lean_closure_set(v___f_740_, 7, v___f_736_);
v___x_741_ = 0;
v___x_742_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_742_, 0, lean_box(0));
lean_closure_set(v___x_742_, 1, v___x_737_);
v___x_743_ = lean_io_as_task(v___x_742_, v___x_738_);
v___x_744_ = 1;
v___x_745_ = lean_task_bind(v___x_743_, v___f_719_, v___x_738_, v___x_744_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_745_);
v___x_747_ = v___x_733_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_750_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
v___x_749_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_738_, v___x_741_, v___x_748_, v___f_740_);
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object* v_inst_752_, lean_object* v_handler_753_, lean_object* v_head_754_, lean_object* v_connectionContext_755_, lean_object* v___x_756_, lean_object* v___f_757_, lean_object* v___f_758_, lean_object* v_config_759_, lean_object* v___f_760_, lean_object* v_x_761_, lean_object* v___y_762_){
_start:
{
uint8_t v___x_1633__boxed_763_; lean_object* v_res_764_; 
v___x_1633__boxed_763_ = lean_unbox(v___x_756_);
v_res_764_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_752_, v_handler_753_, v_head_754_, v_connectionContext_755_, v___x_1633__boxed_763_, v___f_757_, v___f_758_, v_config_759_, v___f_760_, v_x_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object* v_inst_767_, lean_object* v_handler_768_, lean_object* v_machine_769_, lean_object* v_head_770_, lean_object* v_config_771_, lean_object* v_connectionContext_772_){
_start:
{
lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___f_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___f_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___f_774_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_774_, 0, v_machine_769_);
v___f_775_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0));
v___f_776_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1));
v___x_777_ = 0;
v___x_778_ = lean_box(v___x_777_);
v___f_779_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_779_, 0, v_inst_767_);
lean_closure_set(v___f_779_, 1, v_handler_768_);
lean_closure_set(v___f_779_, 2, v_head_770_);
lean_closure_set(v___f_779_, 3, v_connectionContext_772_);
lean_closure_set(v___f_779_, 4, v___x_778_);
lean_closure_set(v___f_779_, 5, v___f_775_);
lean_closure_set(v___f_779_, 6, v___f_774_);
lean_closure_set(v___f_779_, 7, v_config_771_);
lean_closure_set(v___f_779_, 8, v___f_776_);
v___x_780_ = lean_box(0);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = l_Std_CloseableChannel_new___redArg(v___x_780_);
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
v___x_785_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_781_, v___x_777_, v___x_784_, v___f_779_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object* v_inst_786_, lean_object* v_handler_787_, lean_object* v_machine_788_, lean_object* v_head_789_, lean_object* v_config_790_, lean_object* v_connectionContext_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_786_, v_handler_787_, v_machine_788_, v_head_789_, v_config_790_, v_connectionContext_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object* v_00_u03c3_794_, lean_object* v_inst_795_, lean_object* v_handler_796_, lean_object* v_machine_797_, lean_object* v_head_798_, lean_object* v_config_799_, lean_object* v_connectionContext_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_795_, v_handler_796_, v_machine_797_, v_head_798_, v_config_799_, v_connectionContext_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object* v_00_u03c3_803_, lean_object* v_inst_804_, lean_object* v_handler_805_, lean_object* v_machine_806_, lean_object* v_head_807_, lean_object* v_config_808_, lean_object* v_connectionContext_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(v_00_u03c3_803_, v_inst_804_, v_handler_805_, v_machine_806_, v_head_807_, v_config_808_, v_connectionContext_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__1(lean_object* v_a_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = lean_nat_to_int(v_a_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__2(lean_object* v_a_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Rat_ofInt(v_a_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(lean_object* v_tz_816_, lean_object* v_a_817_, lean_object* v___x_818_, lean_object* v_x_819_){
_start:
{
lean_object* v_offset_820_; lean_object* v_second_821_; lean_object* v_nano_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v_nanos_826_; lean_object* v___x_827_; lean_object* v_nanos_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_offset_820_ = lean_ctor_get(v_tz_816_, 0);
v_second_821_ = lean_ctor_get(v_a_817_, 0);
v_nano_822_ = lean_ctor_get(v_a_817_, 1);
v___x_823_ = lean_nat_to_int(v___x_818_);
v___x_824_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_825_ = lean_int_mul(v_second_821_, v___x_824_);
v_nanos_826_ = lean_int_add(v___x_825_, v_nano_822_);
lean_dec(v___x_825_);
v___x_827_ = lean_int_mul(v_offset_820_, v___x_824_);
v_nanos_828_ = lean_int_add(v___x_827_, v___x_823_);
lean_dec(v___x_823_);
lean_dec(v___x_827_);
v___x_829_ = lean_int_add(v_nanos_826_, v_nanos_828_);
lean_dec(v_nanos_828_);
lean_dec(v_nanos_826_);
v___x_830_ = l_Std_Time_Duration_ofNanoseconds(v___x_829_);
lean_dec(v___x_829_);
v___x_831_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed(lean_object* v_tz_832_, lean_object* v_a_833_, lean_object* v___x_834_, lean_object* v_x_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0(v_tz_832_, v_a_833_, v___x_834_, v_x_835_);
lean_dec_ref(v_a_833_);
lean_dec_ref(v_tz_832_);
return v_res_836_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = lean_nat_to_int(v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__2));
v___x_843_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__0);
v___x_844_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_843_, v___x_842_, v___x_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(lean_object* v_headers_845_, lean_object* v_status_846_, uint8_t v_version_847_, lean_object* v_x_848_){
_start:
{
if (lean_obj_tag(v_x_848_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_858_; 
lean_dec(v_status_846_);
lean_dec_ref(v_headers_845_);
v_a_850_ = lean_ctor_get(v_x_848_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_x_848_);
if (v_isSharedCheck_858_ == 0)
{
v___x_852_ = v_x_848_;
v_isShared_853_ = v_isSharedCheck_858_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v_x_848_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_858_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_857_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; 
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_879_; 
v_a_859_ = lean_ctor_get(v_x_848_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v_x_848_);
if (v_isSharedCheck_879_ == 0)
{
v___x_861_ = v_x_848_;
v_isShared_862_ = v_isSharedCheck_879_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v_x_848_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_879_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_tz_865_; lean_object* v___f_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___closed__3);
v_tz_865_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_864_, v_a_859_);
lean_inc(v_a_859_);
lean_inc_ref(v_tz_865_);
v___f_866_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__0___boxed), 4, 3);
lean_closure_set(v___f_866_, 0, v_tz_865_);
lean_closure_set(v___f_866_, 1, v_a_859_);
lean_closure_set(v___f_866_, 2, v___x_863_);
v___x_867_ = lean_mk_thunk(v___f_866_);
v___x_868_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v_a_859_);
lean_ctor_set(v___x_868_, 2, v___x_864_);
lean_ctor_set(v___x_868_, 3, v_tz_865_);
v___x_869_ = l_Std_Http_Header_Name_date;
v___x_870_ = l_Std_Time_DateTime_toHTTPDateString(v___x_868_);
v___x_871_ = l_Std_Http_Header_Value_ofString_x21(v___x_870_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_869_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_array_push(v_headers_845_, v___x_872_);
v___x_874_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_874_, 0, v_status_846_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
lean_ctor_set_uint8(v___x_874_, sizeof(void*)*2, v_version_847_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_874_);
v___x_876_ = v___x_861_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_878_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; 
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed(lean_object* v_headers_880_, lean_object* v_status_881_, lean_object* v_version_882_, lean_object* v_x_883_, lean_object* v___y_884_){
_start:
{
uint8_t v_version_boxed_885_; lean_object* v_res_886_; 
v_version_boxed_885_ = lean_unbox(v_version_882_);
v_res_886_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1(v_headers_880_, v_status_881_, v_version_boxed_885_, v_x_883_);
return v_res_886_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(lean_object* v_as_887_, size_t v_i_888_, size_t v_stop_889_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = lean_usize_dec_eq(v_i_888_, v_stop_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v_fst_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_891_ = lean_array_uget_borrowed(v_as_887_, v_i_888_);
v_fst_892_ = lean_ctor_get(v___x_891_, 0);
v___x_893_ = l_Std_Http_Header_Name_date;
v___x_894_ = lean_string_dec_eq(v_fst_892_, v___x_893_);
if (v___x_894_ == 0)
{
size_t v___x_895_; size_t v___x_896_; 
v___x_895_ = ((size_t)1ULL);
v___x_896_ = lean_usize_add(v_i_888_, v___x_895_);
v_i_888_ = v___x_896_;
goto _start;
}
else
{
return v___x_894_;
}
}
else
{
uint8_t v___x_898_; 
v___x_898_ = 0;
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3___boxed(lean_object* v_as_899_, lean_object* v_i_900_, lean_object* v_stop_901_){
_start:
{
size_t v_i_boxed_902_; size_t v_stop_boxed_903_; uint8_t v_res_904_; lean_object* v_r_905_; 
v_i_boxed_902_ = lean_unbox_usize(v_i_900_);
lean_dec(v_i_900_);
v_stop_boxed_903_ = lean_unbox_usize(v_stop_901_);
lean_dec(v_stop_901_);
v_res_904_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(v_as_899_, v_i_boxed_902_, v_stop_boxed_903_);
lean_dec_ref(v_as_899_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(lean_object* v_config_906_, lean_object* v_head_907_){
_start:
{
uint8_t v_generateDate_912_; 
v_generateDate_912_ = lean_ctor_get_uint8(v_config_906_, sizeof(void*)*24 + 1);
if (v_generateDate_912_ == 0)
{
goto v___jp_909_;
}
else
{
lean_object* v_status_913_; uint8_t v_version_914_; lean_object* v_headers_915_; lean_object* v___x_916_; lean_object* v___f_917_; lean_object* v___y_919_; uint8_t v___y_920_; lean_object* v_val_921_; uint8_t v___y_925_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v_status_913_ = lean_ctor_get(v_head_907_, 0);
v_version_914_ = lean_ctor_get_uint8(v_head_907_, sizeof(void*)*2);
v_headers_915_ = lean_ctor_get(v_head_907_, 1);
v___x_916_ = lean_box(v_version_914_);
lean_inc(v_status_913_);
lean_inc_ref(v_headers_915_);
v___f_917_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___lam__1___boxed), 5, 3);
lean_closure_set(v___f_917_, 0, v_headers_915_);
lean_closure_set(v___f_917_, 1, v_status_913_);
lean_closure_set(v___f_917_, 2, v___x_916_);
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = lean_array_get_size(v_headers_915_);
v___x_946_ = lean_nat_dec_lt(v___x_944_, v___x_945_);
if (v___x_946_ == 0)
{
lean_dec_ref(v_head_907_);
v___y_925_ = v___x_946_;
goto v___jp_924_;
}
else
{
size_t v___x_947_; size_t v___x_948_; uint8_t v___x_949_; 
v___x_947_ = ((size_t)0ULL);
v___x_948_ = lean_usize_of_nat(v___x_945_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__3(v_headers_915_, v___x_947_, v___x_948_);
if (v___x_949_ == 0)
{
lean_dec_ref(v_head_907_);
v___y_925_ = v___x_949_;
goto v___jp_924_;
}
else
{
lean_dec_ref(v___f_917_);
goto v___jp_909_;
}
}
v___jp_918_:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v_val_921_);
v___x_923_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_919_, v___y_920_, v___x_922_, v___f_917_);
return v___x_923_;
}
v___jp_924_:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_get_current_time();
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set_tag(v___x_930_, 1);
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
v___y_919_ = v___x_926_;
v___y_920_ = v___y_925_;
v_val_921_ = v___x_933_;
goto v___jp_918_;
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v_a_936_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_927_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_927_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 0);
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
v___y_919_ = v___x_926_;
v___y_920_ = v___y_925_;
v_val_921_ = v___x_941_;
goto v___jp_918_;
}
}
}
}
}
v___jp_909_:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v_head_907_);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead___boxed(lean_object* v_config_950_, lean_object* v_head_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_950_, v_head_951_);
lean_dec_ref(v_config_950_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead_spec__0(lean_object* v_a_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_nat_to_int(v_a_954_);
v___x_956_ = l_Rat_ofInt(v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v_x_957_){
_start:
{
lean_object* v_fst_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v_fst_958_ = lean_ctor_get(v_x_957_, 0);
v___x_959_ = l_Std_Http_Header_Name_contentLength;
v___x_960_ = lean_string_dec_eq(v_fst_958_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = l_Std_Http_Header_Name_transferEncoding;
v___x_962_ = lean_string_dec_eq(v_fst_958_, v___x_961_);
return v___x_962_;
}
else
{
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v_x_963_){
_start:
{
uint8_t v_res_964_; lean_object* v_r_965_; 
v_res_964_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v_x_963_);
lean_dec_ref(v_x_963_);
v_r_965_ = lean_box(v_res_964_);
return v_r_965_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___y_966_, lean_object* v_____r_967_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_969_ = lean_box(0);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___y_966_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___y_973_, lean_object* v_____r_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___y_973_, v_____r_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v___f_977_, lean_object* v_x_978_){
_start:
{
if (lean_obj_tag(v_x_978_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v___f_977_);
v_a_980_ = lean_ctor_get(v_x_978_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v_x_978_);
if (v_isSharedCheck_988_ == 0)
{
v___x_982_ = v_x_978_;
v_isShared_983_ = v_isSharedCheck_988_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v_x_978_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_988_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_987_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_986_; 
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_990_; 
v_a_989_ = lean_ctor_get(v_x_978_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v_x_978_, 1);
v___x_990_ = lean_apply_2(v___f_977_, v_a_989_, lean_box(0));
return v___x_990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v___f_991_, lean_object* v_x_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v___f_991_, v_x_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_close_995_, lean_object* v_body_996_, lean_object* v___f_997_, lean_object* v___f_998_, lean_object* v_x_999_){
_start:
{
if (lean_obj_tag(v_x_999_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v___f_998_);
lean_dec_ref(v___f_997_);
lean_dec(v_body_996_);
lean_dec_ref(v_close_995_);
v_a_1001_ = lean_ctor_get(v_x_999_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_x_999_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1003_ = v_x_999_;
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v_x_999_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
}
else
{
lean_object* v_a_1010_; uint8_t v___x_1011_; 
v_a_1010_ = lean_ctor_get(v_x_999_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v_x_999_, 1);
v___x_1011_ = lean_unbox(v_a_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; lean_object* v___x_1015_; 
lean_dec_ref(v___f_998_);
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = lean_apply_2(v_close_995_, v_body_996_, lean_box(0));
v___x_1014_ = lean_unbox(v_a_1010_);
lean_dec(v_a_1010_);
v___x_1015_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1012_, v___x_1014_, v___x_1013_, v___f_997_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v_a_1010_);
lean_dec_ref(v___f_997_);
lean_dec(v_body_996_);
lean_dec_ref(v_close_995_);
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_apply_2(v___f_998_, v___x_1016_, lean_box(0));
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_close_1018_, lean_object* v_body_1019_, lean_object* v___f_1020_, lean_object* v___f_1021_, lean_object* v_x_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_close_1018_, v_body_1019_, v___f_1020_, v___f_1021_, v_x_1022_);
return v_res_1024_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_1025_, lean_object* v_x_1026_){
_start:
{
lean_object* v_fst_1027_; uint8_t v___x_1028_; 
v_fst_1027_ = lean_ctor_get(v_x_1026_, 0);
v___x_1028_ = lean_string_dec_eq(v_fst_1027_, v___x_1025_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_1029_, lean_object* v_x_1030_){
_start:
{
uint8_t v_res_1031_; lean_object* v_r_1032_; 
v_res_1031_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_1029_, v_x_1030_);
lean_dec_ref(v_x_1030_);
lean_dec_ref(v___x_1029_);
v_r_1032_ = lean_box(v_res_1031_);
return v_r_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object* v___x_1033_, lean_object* v_x1_1034_, lean_object* v_x2_1035_){
_start:
{
lean_object* v_fst_1036_; uint8_t v___x_1037_; 
v_fst_1036_ = lean_ctor_get(v_x2_1035_, 0);
v___x_1037_ = lean_string_dec_eq(v_fst_1036_, v___x_1033_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_array_push(v_x1_1034_, v_x2_1035_);
return v___x_1038_;
}
else
{
lean_dec_ref(v_x2_1035_);
return v_x1_1034_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed(lean_object* v___x_1039_, lean_object* v_x1_1040_, lean_object* v_x2_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(v___x_1039_, v_x1_1040_, v_x2_1041_);
lean_dec_ref(v___x_1039_);
return v_res_1042_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___f_1063_; 
v___x_1062_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1063_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1063_, 0, v___x_1062_);
return v___f_1063_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___f_1065_; 
v___x_1064_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1065_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_1065_, 0, v___x_1064_);
return v___f_1065_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___f_1069_; 
v___x_1068_ = l_Std_Http_Header_Name_contentLength;
v___f_1069_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1069_, 0, v___x_1068_);
return v___f_1069_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___f_1071_; 
v___x_1070_ = l_Std_Http_Header_Name_contentLength;
v___f_1071_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_1071_, 0, v___x_1070_);
return v___f_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object* v___y_1072_, lean_object* v_body_1073_, lean_object* v_close_1074_, lean_object* v_isClosed_1075_, lean_object* v___f_1076_, lean_object* v_x_1077_){
_start:
{
lean_object* v___y_1080_; uint8_t v_omitBody_1081_; 
if (lean_obj_tag(v_x_1077_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref(v___f_1076_);
lean_dec_ref(v_isClosed_1075_);
lean_dec_ref(v_close_1074_);
lean_dec(v_body_1073_);
lean_dec_ref(v___y_1072_);
v_a_1093_ = lean_ctor_get(v_x_1077_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_x_1077_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1095_ = v_x_1077_;
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v_x_1077_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
}
else
{
lean_object* v_writer_1102_; lean_object* v_a_1103_; lean_object* v_reader_1104_; lean_object* v_config_1105_; lean_object* v_events_1106_; lean_object* v_error_1107_; lean_object* v_instant_1108_; uint8_t v_keepAlive_1109_; uint8_t v_pullBodyStalled_1110_; lean_object* v_userData_1111_; lean_object* v_outputData_1112_; lean_object* v_state_1113_; lean_object* v_knownSize_1114_; lean_object* v_messageHead_1115_; uint8_t v_sentMessage_1116_; uint8_t v_userClosedBody_1117_; uint8_t v_omitBody_1118_; lean_object* v_userDataBytes_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1302_; 
v_writer_1102_ = lean_ctor_get(v___y_1072_, 1);
lean_inc_ref(v_writer_1102_);
v_a_1103_ = lean_ctor_get(v_x_1077_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v_x_1077_, 1);
v_reader_1104_ = lean_ctor_get(v___y_1072_, 0);
v_config_1105_ = lean_ctor_get(v___y_1072_, 2);
v_events_1106_ = lean_ctor_get(v___y_1072_, 3);
v_error_1107_ = lean_ctor_get(v___y_1072_, 4);
v_instant_1108_ = lean_ctor_get(v___y_1072_, 5);
v_keepAlive_1109_ = lean_ctor_get_uint8(v___y_1072_, sizeof(void*)*6);
v_pullBodyStalled_1110_ = lean_ctor_get_uint8(v___y_1072_, sizeof(void*)*6 + 1);
v_userData_1111_ = lean_ctor_get(v_writer_1102_, 0);
v_outputData_1112_ = lean_ctor_get(v_writer_1102_, 1);
v_state_1113_ = lean_ctor_get(v_writer_1102_, 2);
v_knownSize_1114_ = lean_ctor_get(v_writer_1102_, 3);
v_messageHead_1115_ = lean_ctor_get(v_writer_1102_, 4);
v_sentMessage_1116_ = lean_ctor_get_uint8(v_writer_1102_, sizeof(void*)*6);
v_userClosedBody_1117_ = lean_ctor_get_uint8(v_writer_1102_, sizeof(void*)*6 + 1);
v_omitBody_1118_ = lean_ctor_get_uint8(v_writer_1102_, sizeof(void*)*6 + 2);
v_userDataBytes_1119_ = lean_ctor_get(v_writer_1102_, 5);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_writer_1102_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1121_ = v_writer_1102_;
v_isShared_1122_ = v_isSharedCheck_1302_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_userDataBytes_1119_);
lean_inc(v_messageHead_1115_);
lean_inc(v_knownSize_1114_);
lean_inc(v_state_1113_);
lean_inc(v_outputData_1112_);
lean_inc(v_userData_1111_);
lean_dec(v_writer_1102_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1302_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___y_1124_; uint8_t v___y_1130_; lean_object* v___y_1131_; uint8_t v___y_1150_; lean_object* v___y_1151_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_box(1);
v___x_1165_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1113_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_del_object(v___x_1121_);
lean_dec(v_userDataBytes_1119_);
lean_dec(v_messageHead_1115_);
lean_dec(v_knownSize_1114_);
lean_dec(v_state_1113_);
lean_dec_ref(v_outputData_1112_);
lean_dec_ref(v_userData_1111_);
lean_dec(v_a_1103_);
lean_dec_ref(v___f_1076_);
v___y_1080_ = v___y_1072_;
v_omitBody_1081_ = v_omitBody_1118_;
goto v___jp_1079_;
}
else
{
if (v_sentMessage_1116_ == 0)
{
lean_object* v_status_1166_; uint8_t v___x_1167_; lean_object* v_reader_1169_; lean_object* v_userData_1170_; lean_object* v_outputData_1171_; lean_object* v_state_1172_; lean_object* v_knownSize_1173_; uint8_t v_userClosedBody_1174_; uint8_t v_omitBody_1175_; lean_object* v_userDataBytes_1176_; lean_object* v_config_1177_; lean_object* v_events_1178_; lean_object* v_error_1179_; lean_object* v_instant_1180_; uint8_t v_keepAlive_1181_; uint8_t v_pullBodyStalled_1182_; lean_object* v___y_1219_; lean_object* v___y_1221_; uint8_t v___y_1222_; lean_object* v___y_1223_; uint8_t v___y_1253_; lean_object* v___y_1254_; uint8_t v___y_1262_; uint8_t v___y_1265_; uint16_t v___x_1279_; uint16_t v___x_1280_; uint8_t v___x_1281_; 
v_status_1166_ = lean_ctor_get(v_a_1103_, 0);
v___x_1167_ = 0;
v___x_1279_ = 100;
v___x_1280_ = l_Std_Http_Status_toCode(v_status_1166_);
v___x_1281_ = lean_uint16_dec_le(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_del_object(v___x_1121_);
lean_dec(v_messageHead_1115_);
v___y_1265_ = v___x_1281_;
goto v___jp_1264_;
}
else
{
uint16_t v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = 200;
v___x_1283_ = lean_uint16_dec_lt(v___x_1280_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_del_object(v___x_1121_);
lean_dec(v_messageHead_1115_);
v___y_1265_ = v___x_1283_;
goto v___jp_1264_;
}
else
{
lean_object* v_messageHead_1284_; uint8_t v___x_1285_; uint8_t v___x_1286_; uint8_t v___x_1287_; 
lean_dec_ref(v___f_1076_);
v_messageHead_1284_ = lean_ctor_get(v_reader_1104_, 2);
v___x_1285_ = l_Std_Http_Protocol_H1_Message_Head_version(v___x_1167_, v_messageHead_1284_);
v___x_1286_ = 1;
v___x_1287_ = l_Std_Http_instBEqVersion_beq(v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_del_object(v___x_1121_);
lean_dec(v_userDataBytes_1119_);
lean_dec(v_messageHead_1115_);
lean_dec(v_knownSize_1114_);
lean_dec(v_state_1113_);
lean_dec_ref(v_outputData_1112_);
lean_dec_ref(v_userData_1111_);
lean_dec(v_a_1103_);
v___y_1080_ = v___y_1072_;
v_omitBody_1081_ = v_omitBody_1118_;
goto v___jp_1079_;
}
else
{
uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
lean_inc(v_instant_1108_);
lean_inc(v_error_1107_);
lean_inc_ref(v_events_1106_);
lean_inc_ref(v_config_1105_);
lean_inc_ref(v_reader_1104_);
lean_dec_ref(v___y_1072_);
v___x_1288_ = 1;
v___x_1289_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1288_, v_a_1103_);
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = lean_array_get_size(v___x_1289_);
v___x_1292_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1293_ = lean_nat_dec_lt(v___x_1290_, v___x_1291_);
if (v___x_1293_ == 0)
{
v___y_1150_ = v___x_1288_;
v___y_1151_ = v___x_1289_;
goto v___jp_1149_;
}
else
{
lean_object* v___f_1294_; size_t v___x_1295_; size_t v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___f_1294_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13);
v___x_1295_ = ((size_t)0ULL);
v___x_1296_ = lean_usize_of_nat(v___x_1291_);
lean_inc_ref(v___x_1289_);
v___x_1297_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1292_, v___f_1294_, v___x_1289_, v___x_1295_, v___x_1296_);
v___x_1298_ = lean_unbox(v___x_1297_);
lean_dec(v___x_1297_);
if (v___x_1298_ == 0)
{
v___y_1150_ = v___x_1288_;
v___y_1151_ = v___x_1289_;
goto v___jp_1149_;
}
else
{
lean_object* v___f_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___f_1299_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14);
v___x_1300_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1292_, v___f_1299_, v___x_1289_, v___x_1295_, v___x_1296_, v___x_1300_);
v___y_1150_ = v___x_1288_;
v___y_1151_ = v___x_1301_;
goto v___jp_1149_;
}
}
}
}
}
v___jp_1168_:
{
lean_object* v___x_1183_; lean_object* v_machine_1184_; lean_object* v_machine_1185_; lean_object* v_writer_1186_; lean_object* v_reader_1187_; lean_object* v_config_1188_; lean_object* v_events_1189_; lean_object* v_error_1190_; lean_object* v_instant_1191_; uint8_t v_keepAlive_1192_; uint8_t v_pullBodyStalled_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1217_; 
lean_inc(v_a_1103_);
v___x_1183_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1183_, 0, v_userData_1170_);
lean_ctor_set(v___x_1183_, 1, v_outputData_1171_);
lean_ctor_set(v___x_1183_, 2, v_state_1172_);
lean_ctor_set(v___x_1183_, 3, v_knownSize_1173_);
lean_ctor_set(v___x_1183_, 4, v_a_1103_);
lean_ctor_set(v___x_1183_, 5, v_userDataBytes_1176_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*6, v___x_1165_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*6 + 1, v_userClosedBody_1174_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*6 + 2, v_omitBody_1175_);
v_machine_1184_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_machine_1184_, 0, v_reader_1169_);
lean_ctor_set(v_machine_1184_, 1, v___x_1183_);
lean_ctor_set(v_machine_1184_, 2, v_config_1177_);
lean_ctor_set(v_machine_1184_, 3, v_events_1178_);
lean_ctor_set(v_machine_1184_, 4, v_error_1179_);
lean_ctor_set(v_machine_1184_, 5, v_instant_1180_);
lean_ctor_set_uint8(v_machine_1184_, sizeof(void*)*6, v_keepAlive_1181_);
lean_ctor_set_uint8(v_machine_1184_, sizeof(void*)*6 + 1, v_pullBodyStalled_1182_);
v_machine_1185_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1167_, v_machine_1184_, v_a_1103_);
lean_dec(v_a_1103_);
v_writer_1186_ = lean_ctor_get(v_machine_1185_, 1);
v_reader_1187_ = lean_ctor_get(v_machine_1185_, 0);
v_config_1188_ = lean_ctor_get(v_machine_1185_, 2);
v_events_1189_ = lean_ctor_get(v_machine_1185_, 3);
v_error_1190_ = lean_ctor_get(v_machine_1185_, 4);
v_instant_1191_ = lean_ctor_get(v_machine_1185_, 5);
v_keepAlive_1192_ = lean_ctor_get_uint8(v_machine_1185_, sizeof(void*)*6);
v_pullBodyStalled_1193_ = lean_ctor_get_uint8(v_machine_1185_, sizeof(void*)*6 + 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_machine_1185_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1195_ = v_machine_1185_;
v_isShared_1196_ = v_isSharedCheck_1217_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_instant_1191_);
lean_inc(v_error_1190_);
lean_inc(v_events_1189_);
lean_inc(v_config_1188_);
lean_inc(v_writer_1186_);
lean_inc(v_reader_1187_);
lean_dec(v_machine_1185_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1217_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_userData_1197_; lean_object* v_outputData_1198_; lean_object* v_knownSize_1199_; lean_object* v_messageHead_1200_; uint8_t v_sentMessage_1201_; uint8_t v_userClosedBody_1202_; uint8_t v_omitBody_1203_; lean_object* v_userDataBytes_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1215_; 
v_userData_1197_ = lean_ctor_get(v_writer_1186_, 0);
v_outputData_1198_ = lean_ctor_get(v_writer_1186_, 1);
v_knownSize_1199_ = lean_ctor_get(v_writer_1186_, 3);
v_messageHead_1200_ = lean_ctor_get(v_writer_1186_, 4);
v_sentMessage_1201_ = lean_ctor_get_uint8(v_writer_1186_, sizeof(void*)*6);
v_userClosedBody_1202_ = lean_ctor_get_uint8(v_writer_1186_, sizeof(void*)*6 + 1);
v_omitBody_1203_ = lean_ctor_get_uint8(v_writer_1186_, sizeof(void*)*6 + 2);
v_userDataBytes_1204_ = lean_ctor_get(v_writer_1186_, 5);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_writer_1186_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v_writer_1186_, 2);
lean_dec(v_unused_1216_);
v___x_1206_ = v_writer_1186_;
v_isShared_1207_ = v_isSharedCheck_1215_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_userDataBytes_1204_);
lean_inc(v_messageHead_1200_);
lean_inc(v_knownSize_1199_);
lean_inc(v_outputData_1198_);
lean_inc(v_userData_1197_);
lean_dec(v_writer_1186_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1215_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1208_ = lean_box(2);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 2, v___x_1208_);
v___x_1210_ = v___x_1206_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_userData_1197_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_outputData_1198_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v_knownSize_1199_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v_messageHead_1200_);
lean_ctor_set(v_reuseFailAlloc_1214_, 5, v_userDataBytes_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*6, v_sentMessage_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*6 + 1, v_userClosedBody_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*6 + 2, v_omitBody_1203_);
v___x_1210_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1212_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v___x_1210_);
v___x_1212_ = v___x_1195_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_reader_1187_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_config_1188_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_events_1189_);
lean_ctor_set(v_reuseFailAlloc_1213_, 4, v_error_1190_);
lean_ctor_set(v_reuseFailAlloc_1213_, 5, v_instant_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1213_, sizeof(void*)*6, v_keepAlive_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1213_, sizeof(void*)*6 + 1, v_pullBodyStalled_1193_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
v___y_1080_ = v___x_1212_;
v_omitBody_1081_ = v_omitBody_1203_;
goto v___jp_1079_;
}
}
}
}
}
v___jp_1218_:
{
if (lean_obj_tag(v___y_1219_) == 0)
{
v_reader_1169_ = v_reader_1104_;
v_userData_1170_ = v_userData_1111_;
v_outputData_1171_ = v_outputData_1112_;
v_state_1172_ = v_state_1113_;
v_knownSize_1173_ = v_knownSize_1114_;
v_userClosedBody_1174_ = v_userClosedBody_1117_;
v_omitBody_1175_ = v_omitBody_1118_;
v_userDataBytes_1176_ = v_userDataBytes_1119_;
v_config_1177_ = v_config_1105_;
v_events_1178_ = v_events_1106_;
v_error_1179_ = v_error_1107_;
v_instant_1180_ = v_instant_1108_;
v_keepAlive_1181_ = v_keepAlive_1109_;
v_pullBodyStalled_1182_ = v_pullBodyStalled_1110_;
goto v___jp_1168_;
}
else
{
lean_dec(v_knownSize_1114_);
v_reader_1169_ = v_reader_1104_;
v_userData_1170_ = v_userData_1111_;
v_outputData_1171_ = v_outputData_1112_;
v_state_1172_ = v_state_1113_;
v_knownSize_1173_ = v___y_1219_;
v_userClosedBody_1174_ = v_userClosedBody_1117_;
v_omitBody_1175_ = v_omitBody_1118_;
v_userDataBytes_1176_ = v_userDataBytes_1119_;
v_config_1177_ = v_config_1105_;
v_events_1178_ = v_events_1106_;
v_error_1179_ = v_error_1107_;
v_instant_1180_ = v_instant_1108_;
v_keepAlive_1181_ = v_keepAlive_1109_;
v_pullBodyStalled_1182_ = v_pullBodyStalled_1110_;
goto v___jp_1168_;
}
}
v___jp_1220_:
{
lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1224_ = lean_unsigned_to_nat(204u);
v___x_1225_ = lean_nat_dec_eq(v___y_1223_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1226_ = lean_unsigned_to_nat(304u);
v___x_1227_ = lean_nat_dec_eq(v___y_1223_, v___x_1226_);
lean_dec(v___y_1223_);
if (v___x_1227_ == 0)
{
lean_object* v_messageHead_1228_; uint8_t v_method_1229_; uint8_t v___x_1230_; uint8_t v___x_1231_; 
v_messageHead_1228_ = lean_ctor_get(v_reader_1104_, 2);
v_method_1229_ = lean_ctor_get_uint8(v_messageHead_1228_, sizeof(void*)*2);
v___x_1230_ = 9;
v___x_1231_ = l_Std_Http_instBEqMethod_beq(v_method_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; 
lean_dec(v_userDataBytes_1119_);
lean_dec(v_knownSize_1114_);
lean_dec(v_state_1113_);
lean_dec_ref(v_outputData_1112_);
lean_dec_ref(v_userData_1111_);
lean_inc_ref(v___y_1072_);
v___x_1232_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1167_, v___y_1072_, v___y_1221_, v___y_1222_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v___x_1233_; lean_object* v_writer_1234_; uint8_t v_omitBody_1235_; 
lean_dec(v_a_1103_);
v___x_1233_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_rejectOutgoingFraming(v___x_1167_, v___y_1072_);
v_writer_1234_ = lean_ctor_get(v___x_1233_, 1);
v_omitBody_1235_ = lean_ctor_get_uint8(v_writer_1234_, sizeof(void*)*6 + 2);
v___y_1080_ = v___x_1233_;
v_omitBody_1081_ = v_omitBody_1235_;
goto v___jp_1079_;
}
else
{
lean_object* v_val_1236_; lean_object* v_writer_1237_; lean_object* v_reader_1238_; lean_object* v_config_1239_; lean_object* v_events_1240_; lean_object* v_error_1241_; lean_object* v_instant_1242_; uint8_t v_keepAlive_1243_; uint8_t v_pullBodyStalled_1244_; lean_object* v_userData_1245_; lean_object* v_outputData_1246_; lean_object* v_state_1247_; lean_object* v_knownSize_1248_; uint8_t v_userClosedBody_1249_; uint8_t v_omitBody_1250_; lean_object* v_userDataBytes_1251_; 
lean_dec_ref(v___y_1072_);
v_val_1236_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_val_1236_);
lean_dec_ref_known(v___x_1232_, 1);
v_writer_1237_ = lean_ctor_get(v_val_1236_, 1);
lean_inc_ref(v_writer_1237_);
v_reader_1238_ = lean_ctor_get(v_val_1236_, 0);
lean_inc_ref(v_reader_1238_);
v_config_1239_ = lean_ctor_get(v_val_1236_, 2);
lean_inc_ref(v_config_1239_);
v_events_1240_ = lean_ctor_get(v_val_1236_, 3);
lean_inc_ref(v_events_1240_);
v_error_1241_ = lean_ctor_get(v_val_1236_, 4);
lean_inc(v_error_1241_);
v_instant_1242_ = lean_ctor_get(v_val_1236_, 5);
lean_inc(v_instant_1242_);
v_keepAlive_1243_ = lean_ctor_get_uint8(v_val_1236_, sizeof(void*)*6);
v_pullBodyStalled_1244_ = lean_ctor_get_uint8(v_val_1236_, sizeof(void*)*6 + 1);
lean_dec(v_val_1236_);
v_userData_1245_ = lean_ctor_get(v_writer_1237_, 0);
lean_inc_ref(v_userData_1245_);
v_outputData_1246_ = lean_ctor_get(v_writer_1237_, 1);
lean_inc_ref(v_outputData_1246_);
v_state_1247_ = lean_ctor_get(v_writer_1237_, 2);
lean_inc(v_state_1247_);
v_knownSize_1248_ = lean_ctor_get(v_writer_1237_, 3);
lean_inc(v_knownSize_1248_);
v_userClosedBody_1249_ = lean_ctor_get_uint8(v_writer_1237_, sizeof(void*)*6 + 1);
v_omitBody_1250_ = lean_ctor_get_uint8(v_writer_1237_, sizeof(void*)*6 + 2);
v_userDataBytes_1251_ = lean_ctor_get(v_writer_1237_, 5);
lean_inc(v_userDataBytes_1251_);
lean_dec_ref(v_writer_1237_);
v_reader_1169_ = v_reader_1238_;
v_userData_1170_ = v_userData_1245_;
v_outputData_1171_ = v_outputData_1246_;
v_state_1172_ = v_state_1247_;
v_knownSize_1173_ = v_knownSize_1248_;
v_userClosedBody_1174_ = v_userClosedBody_1249_;
v_omitBody_1175_ = v_omitBody_1250_;
v_userDataBytes_1176_ = v_userDataBytes_1251_;
v_config_1177_ = v_config_1239_;
v_events_1178_ = v_events_1240_;
v_error_1179_ = v_error_1241_;
v_instant_1180_ = v_instant_1242_;
v_keepAlive_1181_ = v_keepAlive_1243_;
v_pullBodyStalled_1182_ = v_pullBodyStalled_1244_;
goto v___jp_1168_;
}
}
else
{
lean_inc(v_instant_1108_);
lean_inc(v_error_1107_);
lean_inc_ref(v_events_1106_);
lean_inc_ref(v_config_1105_);
lean_inc_ref(v_reader_1104_);
lean_dec_ref(v___y_1072_);
v___y_1219_ = v___y_1221_;
goto v___jp_1218_;
}
}
else
{
lean_inc(v_instant_1108_);
lean_inc(v_error_1107_);
lean_inc_ref(v_events_1106_);
lean_inc_ref(v_config_1105_);
lean_inc_ref(v_reader_1104_);
lean_dec_ref(v___y_1072_);
v___y_1219_ = v___y_1221_;
goto v___jp_1218_;
}
}
else
{
lean_inc(v_instant_1108_);
lean_inc(v_error_1107_);
lean_inc_ref(v_events_1106_);
lean_inc_ref(v_config_1105_);
lean_inc_ref(v_reader_1104_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1072_);
v___y_1219_ = v___y_1221_;
goto v___jp_1218_;
}
}
v___jp_1252_:
{
uint16_t v___x_1255_; lean_object* v_code_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1255_ = l_Std_Http_Status_toCode(v_status_1166_);
v_code_1256_ = lean_uint16_to_nat(v___x_1255_);
v___x_1257_ = lean_unsigned_to_nat(100u);
v___x_1258_ = lean_nat_dec_le(v___x_1257_, v_code_1256_);
if (v___x_1258_ == 0)
{
v___y_1221_ = v___y_1254_;
v___y_1222_ = v___y_1253_;
v___y_1223_ = v_code_1256_;
goto v___jp_1220_;
}
else
{
lean_object* v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = lean_unsigned_to_nat(200u);
v___x_1260_ = lean_nat_dec_lt(v_code_1256_, v___x_1259_);
if (v___x_1260_ == 0)
{
v___y_1221_ = v___y_1254_;
v___y_1222_ = v___y_1253_;
v___y_1223_ = v_code_1256_;
goto v___jp_1220_;
}
else
{
lean_inc(v_instant_1108_);
lean_inc(v_error_1107_);
lean_inc_ref(v_events_1106_);
lean_inc_ref(v_config_1105_);
lean_inc_ref(v_reader_1104_);
lean_dec_ref(v___y_1072_);
v___y_1219_ = v___y_1254_;
goto v___jp_1218_;
}
}
}
v___jp_1261_:
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_box(0);
v___y_1253_ = v___y_1262_;
v___y_1254_ = v___x_1263_;
goto v___jp_1252_;
}
v___jp_1264_:
{
uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1266_ = 1;
v___x_1267_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1266_, v_a_1103_);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_array_get_size(v___x_1267_);
v___x_1270_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1271_ = lean_nat_dec_lt(v___x_1268_, v___x_1269_);
if (v___x_1271_ == 0)
{
lean_dec_ref(v___x_1267_);
lean_dec_ref(v___f_1076_);
v___y_1262_ = v___x_1271_;
goto v___jp_1261_;
}
else
{
size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1272_ = ((size_t)0ULL);
v___x_1273_ = lean_usize_of_nat(v___x_1269_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1270_, v___f_1076_, v___x_1267_, v___x_1272_, v___x_1273_);
v___x_1275_ = lean_unbox(v___x_1274_);
if (v___x_1275_ == 0)
{
uint8_t v___x_1276_; 
v___x_1276_ = lean_unbox(v___x_1274_);
lean_dec(v___x_1274_);
v___y_1262_ = v___x_1276_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_1266_, v_a_1103_, v___y_1265_);
v___x_1278_ = lean_unbox(v___x_1274_);
lean_dec(v___x_1274_);
v___y_1253_ = v___x_1278_;
v___y_1254_ = v___x_1277_;
goto v___jp_1252_;
}
}
}
}
else
{
lean_del_object(v___x_1121_);
lean_dec(v_userDataBytes_1119_);
lean_dec(v_messageHead_1115_);
lean_dec(v_knownSize_1114_);
lean_dec(v_state_1113_);
lean_dec_ref(v_outputData_1112_);
lean_dec_ref(v_userData_1111_);
lean_dec(v_a_1103_);
lean_dec_ref(v___f_1076_);
v___y_1080_ = v___y_1072_;
v_omitBody_1081_ = v_omitBody_1118_;
goto v___jp_1079_;
}
}
v___jp_1123_:
{
lean_object* v___x_1126_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v___y_1124_);
v___x_1126_ = v___x_1121_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_userData_1111_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___y_1124_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v_state_1113_);
lean_ctor_set(v_reuseFailAlloc_1128_, 3, v_knownSize_1114_);
lean_ctor_set(v_reuseFailAlloc_1128_, 4, v_messageHead_1115_);
lean_ctor_set(v_reuseFailAlloc_1128_, 5, v_userDataBytes_1119_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, sizeof(void*)*6, v_sentMessage_1116_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, sizeof(void*)*6 + 1, v_userClosedBody_1117_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, sizeof(void*)*6 + 2, v_omitBody_1118_);
v___x_1126_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1127_, 0, v_reader_1104_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
lean_ctor_set(v___x_1127_, 2, v_config_1105_);
lean_ctor_set(v___x_1127_, 3, v_events_1106_);
lean_ctor_set(v___x_1127_, 4, v_error_1107_);
lean_ctor_set(v___x_1127_, 5, v_instant_1108_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*6, v_keepAlive_1109_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*6 + 1, v_pullBodyStalled_1110_);
v___y_1080_ = v___x_1127_;
v_omitBody_1081_ = v_omitBody_1118_;
goto v___jp_1079_;
}
}
v___jp_1129_:
{
lean_object* v_message_1132_; lean_object* v___x_1133_; lean_object* v___x_2618__overap_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v_message_1132_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1130_, v_a_1103_, v___y_1131_);
v___x_1133_ = l_ByteArray_empty;
v___x_2618__overap_1134_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1130_);
v___x_1135_ = lean_apply_2(v___x_2618__overap_1134_, v___x_1133_, v_message_1132_);
v___x_1136_ = l_ByteArray_isEmpty(v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v_data_1137_; lean_object* v_size_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1148_; 
v_data_1137_ = lean_ctor_get(v_outputData_1112_, 0);
v_size_1138_ = lean_ctor_get(v_outputData_1112_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_outputData_1112_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1140_ = v_outputData_1112_;
v_isShared_1141_ = v_isSharedCheck_1148_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_size_1138_);
lean_inc(v_data_1137_);
lean_dec(v_outputData_1112_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1148_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
lean_inc_ref(v___x_1135_);
v___x_1142_ = lean_array_push(v_data_1137_, v___x_1135_);
v___x_1143_ = lean_byte_array_size(v___x_1135_);
lean_dec_ref(v___x_1135_);
v___x_1144_ = lean_nat_add(v_size_1138_, v___x_1143_);
lean_dec(v_size_1138_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 1, v___x_1144_);
lean_ctor_set(v___x_1140_, 0, v___x_1142_);
v___x_1146_ = v___x_1140_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
v___y_1124_ = v___x_1146_;
goto v___jp_1123_;
}
}
}
else
{
lean_dec_ref(v___x_1135_);
v___y_1124_ = v_outputData_1112_;
goto v___jp_1123_;
}
}
v___jp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = lean_array_get_size(v___y_1151_);
v___x_1154_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1155_ = lean_nat_dec_lt(v___x_1152_, v___x_1153_);
if (v___x_1155_ == 0)
{
v___y_1130_ = v___y_1150_;
v___y_1131_ = v___y_1151_;
goto v___jp_1129_;
}
else
{
lean_object* v___f_1156_; size_t v___x_1157_; size_t v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___f_1156_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10);
v___x_1157_ = ((size_t)0ULL);
v___x_1158_ = lean_usize_of_nat(v___x_1153_);
lean_inc_ref(v___y_1151_);
v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1154_, v___f_1156_, v___y_1151_, v___x_1157_, v___x_1158_);
v___x_1160_ = lean_unbox(v___x_1159_);
lean_dec(v___x_1159_);
if (v___x_1160_ == 0)
{
v___y_1130_ = v___y_1150_;
v___y_1131_ = v___y_1151_;
goto v___jp_1129_;
}
else
{
lean_object* v___f_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___f_1161_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11);
v___x_1162_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___x_1163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1154_, v___f_1161_, v___y_1151_, v___x_1157_, v___x_1158_, v___x_1162_);
v___y_1130_ = v___y_1150_;
v___y_1131_ = v___x_1163_;
goto v___jp_1129_;
}
}
}
}
}
v___jp_1079_:
{
if (v_omitBody_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec_ref(v_isClosed_1075_);
lean_dec_ref(v_close_1074_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v_body_1073_);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___y_1080_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
else
{
lean_object* v___f_1086_; lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___f_1086_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1086_, 0, v___y_1080_);
lean_inc_ref(v___f_1086_);
v___f_1087_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1087_, 0, v___f_1086_);
lean_inc(v_body_1073_);
v___f_1088_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_1088_, 0, v_close_1074_);
lean_closure_set(v___f_1088_, 1, v_body_1073_);
lean_closure_set(v___f_1088_, 2, v___f_1087_);
lean_closure_set(v___f_1088_, 3, v___f_1086_);
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = 0;
v___x_1091_ = lean_apply_2(v_isClosed_1075_, v_body_1073_, lean_box(0));
v___x_1092_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1089_, v___x_1090_, v___x_1091_, v___f_1088_);
return v___x_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object* v___y_1303_, lean_object* v_body_1304_, lean_object* v_close_1305_, lean_object* v_isClosed_1306_, lean_object* v___f_1307_, lean_object* v_x_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(v___y_1303_, v_body_1304_, v_close_1305_, v_isClosed_1306_, v___f_1307_, v_x_1308_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object* v_body_1311_, lean_object* v_close_1312_, lean_object* v_isClosed_1313_, lean_object* v___f_1314_, lean_object* v_config_1315_, lean_object* v_line_1316_, lean_object* v_machine_1317_, lean_object* v_x_1318_){
_start:
{
lean_object* v___y_1321_; 
if (lean_obj_tag(v_x_1318_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_machine_1317_);
lean_dec_ref(v_line_1316_);
lean_dec_ref(v___f_1314_);
lean_dec_ref(v_isClosed_1313_);
lean_dec_ref(v_close_1312_);
lean_dec(v_body_1311_);
v_a_1327_ = lean_ctor_get(v_x_1318_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_x_1318_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1329_ = v_x_1318_;
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v_x_1318_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
}
else
{
lean_object* v_a_1336_; 
v_a_1336_ = lean_ctor_get(v_x_1318_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v_x_1318_, 1);
if (lean_obj_tag(v_a_1336_) == 1)
{
lean_object* v_writer_1337_; lean_object* v_reader_1338_; lean_object* v_config_1339_; lean_object* v_events_1340_; lean_object* v_error_1341_; lean_object* v_instant_1342_; uint8_t v_keepAlive_1343_; uint8_t v_pullBodyStalled_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1367_; 
v_writer_1337_ = lean_ctor_get(v_machine_1317_, 1);
v_reader_1338_ = lean_ctor_get(v_machine_1317_, 0);
v_config_1339_ = lean_ctor_get(v_machine_1317_, 2);
v_events_1340_ = lean_ctor_get(v_machine_1317_, 3);
v_error_1341_ = lean_ctor_get(v_machine_1317_, 4);
v_instant_1342_ = lean_ctor_get(v_machine_1317_, 5);
v_keepAlive_1343_ = lean_ctor_get_uint8(v_machine_1317_, sizeof(void*)*6);
v_pullBodyStalled_1344_ = lean_ctor_get_uint8(v_machine_1317_, sizeof(void*)*6 + 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_machine_1317_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1346_ = v_machine_1317_;
v_isShared_1347_ = v_isSharedCheck_1367_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_instant_1342_);
lean_inc(v_error_1341_);
lean_inc(v_events_1340_);
lean_inc(v_config_1339_);
lean_inc(v_writer_1337_);
lean_inc(v_reader_1338_);
lean_dec(v_machine_1317_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1367_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_userData_1348_; lean_object* v_outputData_1349_; lean_object* v_state_1350_; lean_object* v_messageHead_1351_; uint8_t v_sentMessage_1352_; uint8_t v_userClosedBody_1353_; uint8_t v_omitBody_1354_; lean_object* v_userDataBytes_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1365_; 
v_userData_1348_ = lean_ctor_get(v_writer_1337_, 0);
v_outputData_1349_ = lean_ctor_get(v_writer_1337_, 1);
v_state_1350_ = lean_ctor_get(v_writer_1337_, 2);
v_messageHead_1351_ = lean_ctor_get(v_writer_1337_, 4);
v_sentMessage_1352_ = lean_ctor_get_uint8(v_writer_1337_, sizeof(void*)*6);
v_userClosedBody_1353_ = lean_ctor_get_uint8(v_writer_1337_, sizeof(void*)*6 + 1);
v_omitBody_1354_ = lean_ctor_get_uint8(v_writer_1337_, sizeof(void*)*6 + 2);
v_userDataBytes_1355_ = lean_ctor_get(v_writer_1337_, 5);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_writer_1337_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v_writer_1337_, 3);
lean_dec(v_unused_1366_);
v___x_1357_ = v_writer_1337_;
v_isShared_1358_ = v_isSharedCheck_1365_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_userDataBytes_1355_);
lean_inc(v_messageHead_1351_);
lean_inc(v_state_1350_);
lean_inc(v_outputData_1349_);
lean_inc(v_userData_1348_);
lean_dec(v_writer_1337_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1365_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 3, v_a_1336_);
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_userData_1348_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_outputData_1349_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_state_1350_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v_a_1336_);
lean_ctor_set(v_reuseFailAlloc_1364_, 4, v_messageHead_1351_);
lean_ctor_set(v_reuseFailAlloc_1364_, 5, v_userDataBytes_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1364_, sizeof(void*)*6, v_sentMessage_1352_);
lean_ctor_set_uint8(v_reuseFailAlloc_1364_, sizeof(void*)*6 + 1, v_userClosedBody_1353_);
lean_ctor_set_uint8(v_reuseFailAlloc_1364_, sizeof(void*)*6 + 2, v_omitBody_1354_);
v___x_1360_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1362_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1360_);
v___x_1362_ = v___x_1346_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_reader_1338_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v_config_1339_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v_events_1340_);
lean_ctor_set(v_reuseFailAlloc_1363_, 4, v_error_1341_);
lean_ctor_set(v_reuseFailAlloc_1363_, 5, v_instant_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1363_, sizeof(void*)*6, v_keepAlive_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1363_, sizeof(void*)*6 + 1, v_pullBodyStalled_1344_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
v___y_1321_ = v___x_1362_;
goto v___jp_1320_;
}
}
}
}
}
else
{
lean_dec(v_a_1336_);
v___y_1321_ = v_machine_1317_;
goto v___jp_1320_;
}
}
v___jp_1320_:
{
lean_object* v___f_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___f_1322_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_1322_, 0, v___y_1321_);
lean_closure_set(v___f_1322_, 1, v_body_1311_);
lean_closure_set(v___f_1322_, 2, v_close_1312_);
lean_closure_set(v___f_1322_, 3, v_isClosed_1313_);
lean_closure_set(v___f_1322_, 4, v___f_1314_);
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = 0;
v___x_1325_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1315_, v_line_1316_);
v___x_1326_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1323_, v___x_1324_, v___x_1325_, v___f_1322_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object* v_body_1368_, lean_object* v_close_1369_, lean_object* v_isClosed_1370_, lean_object* v___f_1371_, lean_object* v_config_1372_, lean_object* v_line_1373_, lean_object* v_machine_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(v_body_1368_, v_close_1369_, v_isClosed_1370_, v___f_1371_, v_config_1372_, v_line_1373_, v_machine_1374_, v_x_1375_);
lean_dec_ref(v_config_1372_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1379_, lean_object* v_config_1380_, lean_object* v_machine_1381_, lean_object* v_res_1382_){
_start:
{
lean_object* v_close_1384_; lean_object* v_isClosed_1385_; lean_object* v_getKnownSize_1386_; lean_object* v_line_1387_; lean_object* v_body_1388_; lean_object* v___f_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_close_1384_ = lean_ctor_get(v_inst_1379_, 1);
lean_inc_ref(v_close_1384_);
v_isClosed_1385_ = lean_ctor_get(v_inst_1379_, 2);
lean_inc_ref(v_isClosed_1385_);
v_getKnownSize_1386_ = lean_ctor_get(v_inst_1379_, 5);
lean_inc_ref(v_getKnownSize_1386_);
lean_dec_ref(v_inst_1379_);
v_line_1387_ = lean_ctor_get(v_res_1382_, 0);
lean_inc_ref(v_line_1387_);
v_body_1388_ = lean_ctor_get(v_res_1382_, 1);
lean_inc_n(v_body_1388_, 2);
lean_dec_ref(v_res_1382_);
v___f_1389_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___closed__0));
v___f_1390_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed), 9, 7);
lean_closure_set(v___f_1390_, 0, v_body_1388_);
lean_closure_set(v___f_1390_, 1, v_close_1384_);
lean_closure_set(v___f_1390_, 2, v_isClosed_1385_);
lean_closure_set(v___f_1390_, 3, v___f_1389_);
lean_closure_set(v___f_1390_, 4, v_config_1380_);
lean_closure_set(v___f_1390_, 5, v_line_1387_);
lean_closure_set(v___f_1390_, 6, v_machine_1381_);
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = 0;
v___x_1393_ = lean_apply_2(v_getKnownSize_1386_, v_body_1388_, lean_box(0));
v___x_1394_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1391_, v___x_1392_, v___x_1393_, v___f_1390_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1395_, lean_object* v_config_1396_, lean_object* v_machine_1397_, lean_object* v_res_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1395_, v_config_1396_, v_machine_1397_, v_res_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1401_, lean_object* v_inst_1402_, lean_object* v_config_1403_, lean_object* v_machine_1404_, lean_object* v_res_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1402_, v_config_1403_, v_machine_1404_, v_res_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1408_, lean_object* v_inst_1409_, lean_object* v_config_1410_, lean_object* v_machine_1411_, lean_object* v_res_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1408_, v_inst_1409_, v_config_1410_, v_machine_1411_, v_res_1412_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v_closed_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_closed_1418_ = lean_ctor_get_uint8(v_____do__lift_1415_, sizeof(void*)*6);
v___x_1419_ = lean_box(v_closed_1418_);
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v_____do__lift_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1426_, lean_object* v_x_1427_){
_start:
{
if (lean_obj_tag(v_x_1427_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v___x_1426_);
v_a_1429_ = lean_ctor_get(v_x_1427_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_x_1427_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1431_ = v_x_1427_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v_x_1427_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
return v___x_1435_;
}
}
}
else
{
lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1446_; 
v_isSharedCheck_1446_ = !lean_is_exclusive(v_x_1427_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v_x_1427_, 0);
lean_dec(v_unused_1447_);
v___x_1439_ = v_x_1427_;
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
else
{
lean_dec(v_x_1427_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1426_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1441_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1448_, lean_object* v_x_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1448_, v_x_1449_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; lean_object* v_pendingProducer_1460_; lean_object* v_pendingConsumer_1461_; lean_object* v_interestWaiter_1462_; uint8_t v_closed_1463_; lean_object* v_pendingIncompleteChunk_1464_; lean_object* v_closeError_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1474_; 
v___x_1459_ = lean_st_ref_take(v___y_1457_);
v_pendingProducer_1460_ = lean_ctor_get(v___x_1459_, 0);
v_pendingConsumer_1461_ = lean_ctor_get(v___x_1459_, 1);
v_interestWaiter_1462_ = lean_ctor_get(v___x_1459_, 2);
v_closed_1463_ = lean_ctor_get_uint8(v___x_1459_, sizeof(void*)*6);
v_pendingIncompleteChunk_1464_ = lean_ctor_get(v___x_1459_, 4);
v_closeError_1465_ = lean_ctor_get(v___x_1459_, 5);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v___x_1459_, 3);
lean_dec(v_unused_1475_);
v___x_1467_ = v___x_1459_;
v_isShared_1468_ = v_isSharedCheck_1474_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_closeError_1465_);
lean_inc(v_pendingIncompleteChunk_1464_);
lean_inc(v_interestWaiter_1462_);
lean_inc(v_pendingConsumer_1461_);
lean_inc(v_pendingProducer_1460_);
lean_dec(v___x_1459_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1474_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 3, v___x_1456_);
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_pendingProducer_1460_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_pendingConsumer_1461_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v_interestWaiter_1462_);
lean_ctor_set(v_reuseFailAlloc_1473_, 3, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1473_, 4, v_pendingIncompleteChunk_1464_);
lean_ctor_set(v_reuseFailAlloc_1473_, 5, v_closeError_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1473_, sizeof(void*)*6, v_closed_1463_);
v___x_1470_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_st_ref_put(v___y_1457_, v___x_1470_);
v___x_1472_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1));
return v___x_1472_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1476_, v___y_1477_);
lean_dec(v___y_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1480_, lean_object* v_requestStream_1481_, lean_object* v_keepAliveTimeout_1482_, lean_object* v_currentTimeout_1483_, lean_object* v_headerTimeout_1484_, lean_object* v_response_1485_, lean_object* v_respStream_1486_, lean_object* v_expectData_1487_, uint8_t v_handlerDispatched_1488_, lean_object* v_____r_1489_){
_start:
{
uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1491_ = 0;
v___x_1492_ = lean_box(0);
v___x_1493_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1493_, 0, v_machine_1480_);
lean_ctor_set(v___x_1493_, 1, v_requestStream_1481_);
lean_ctor_set(v___x_1493_, 2, v_keepAliveTimeout_1482_);
lean_ctor_set(v___x_1493_, 3, v_currentTimeout_1483_);
lean_ctor_set(v___x_1493_, 4, v_headerTimeout_1484_);
lean_ctor_set(v___x_1493_, 5, v_response_1485_);
lean_ctor_set(v___x_1493_, 6, v_respStream_1486_);
lean_ctor_set(v___x_1493_, 7, v_expectData_1487_);
lean_ctor_set(v___x_1493_, 8, v___x_1492_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*9, v___x_1491_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*9 + 1, v_handlerDispatched_1488_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1497_, lean_object* v_requestStream_1498_, lean_object* v_keepAliveTimeout_1499_, lean_object* v_currentTimeout_1500_, lean_object* v_headerTimeout_1501_, lean_object* v_response_1502_, lean_object* v_respStream_1503_, lean_object* v_expectData_1504_, lean_object* v_handlerDispatched_1505_, lean_object* v_____r_1506_, lean_object* v___y_1507_){
_start:
{
uint8_t v_handlerDispatched_boxed_1508_; lean_object* v_res_1509_; 
v_handlerDispatched_boxed_1508_ = lean_unbox(v_handlerDispatched_1505_);
v_res_1509_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1497_, v_requestStream_1498_, v_keepAliveTimeout_1499_, v_currentTimeout_1500_, v_headerTimeout_1501_, v_response_1502_, v_respStream_1503_, v_expectData_1504_, v_handlerDispatched_boxed_1508_, v_____r_1506_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1510_, lean_object* v_x_1511_){
_start:
{
if (lean_obj_tag(v_x_1511_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref(v___f_1510_);
v_a_1513_ = lean_ctor_get(v_x_1511_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_x_1511_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1515_ = v_x_1511_;
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v_x_1511_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1523_; 
v_a_1522_ = lean_ctor_get(v_x_1511_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v_x_1511_, 1);
v___x_1523_ = lean_apply_2(v___f_1510_, v_a_1522_, lean_box(0));
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1524_, lean_object* v_x_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1524_, v_x_1525_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1528_, lean_object* v___f_1529_, lean_object* v___f_1530_, lean_object* v_x_1531_){
_start:
{
if (lean_obj_tag(v_x_1531_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1541_; 
lean_dec_ref(v___f_1530_);
lean_dec_ref(v___f_1529_);
lean_dec_ref(v_requestStream_1528_);
v_a_1533_ = lean_ctor_get(v_x_1531_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_x_1531_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1535_ = v_x_1531_;
v_isShared_1536_ = v_isSharedCheck_1541_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v_x_1531_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1541_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
return v___x_1539_;
}
}
}
else
{
lean_object* v_a_1542_; uint8_t v___x_1543_; 
v_a_1542_ = lean_ctor_get(v_x_1531_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v_x_1531_, 1);
v___x_1543_ = lean_unbox(v_a_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; 
lean_dec_ref(v___f_1530_);
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = l_Std_Http_Body_Stream_close(v_requestStream_1528_);
v___x_1546_ = lean_unbox(v_a_1542_);
lean_dec(v_a_1542_);
v___x_1547_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1544_, v___x_1546_, v___x_1545_, v___f_1529_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec(v_a_1542_);
lean_dec_ref(v___f_1529_);
lean_dec_ref(v_requestStream_1528_);
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_apply_2(v___f_1530_, v___x_1548_, lean_box(0));
return v___x_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1550_, lean_object* v___f_1551_, lean_object* v___f_1552_, lean_object* v_x_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1550_, v___f_1551_, v___f_1552_, v_x_1553_);
return v_res_1555_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_1556_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_1557_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___f_1564_; lean_object* v___f_1565_; 
v___x_1563_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1564_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1565_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1565_, 0, v___f_1564_);
lean_closure_set(v___f_1565_, 1, v___x_1563_);
return v___f_1565_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___f_1575_; lean_object* v___f_1576_; 
v___x_1574_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1575_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1576_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1576_, 0, v___f_1575_);
lean_closure_set(v___f_1576_, 1, v___x_1574_);
return v___f_1576_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1577_; lean_object* v___x_1578_; 
v___f_1577_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1578_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1578_, 0, lean_box(0));
lean_closure_set(v___x_1578_, 1, lean_box(0));
lean_closure_set(v___x_1578_, 2, lean_box(0));
lean_closure_set(v___x_1578_, 3, v___f_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1579_, lean_object* v___f_1580_, lean_object* v_x_1581_){
_start:
{
if (lean_obj_tag(v_x_1581_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v___f_1580_);
lean_dec_ref(v___y_1579_);
v_a_1583_ = lean_ctor_get(v_x_1581_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_x_1581_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1585_ = v_x_1581_;
v_isShared_1586_ = v_isSharedCheck_1591_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v_x_1581_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1591_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
return v___x_1589_;
}
}
}
else
{
lean_object* v_machine_1592_; lean_object* v_requestStream_1593_; lean_object* v_keepAliveTimeout_1594_; lean_object* v_currentTimeout_1595_; lean_object* v_headerTimeout_1596_; lean_object* v_response_1597_; lean_object* v_respStream_1598_; lean_object* v_expectData_1599_; uint8_t v_handlerDispatched_1600_; lean_object* v___x_1601_; lean_object* v___f_1602_; lean_object* v___f_1603_; lean_object* v___f_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___f_1608_; lean_object* v___f_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_4870__overap_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec_ref_known(v_x_1581_, 1);
v_machine_1592_ = lean_ctor_get(v___y_1579_, 0);
lean_inc_ref(v_machine_1592_);
v_requestStream_1593_ = lean_ctor_get(v___y_1579_, 1);
lean_inc_ref_n(v_requestStream_1593_, 3);
v_keepAliveTimeout_1594_ = lean_ctor_get(v___y_1579_, 2);
lean_inc(v_keepAliveTimeout_1594_);
v_currentTimeout_1595_ = lean_ctor_get(v___y_1579_, 3);
lean_inc(v_currentTimeout_1595_);
v_headerTimeout_1596_ = lean_ctor_get(v___y_1579_, 4);
lean_inc(v_headerTimeout_1596_);
v_response_1597_ = lean_ctor_get(v___y_1579_, 5);
lean_inc_ref(v_response_1597_);
v_respStream_1598_ = lean_ctor_get(v___y_1579_, 6);
lean_inc(v_respStream_1598_);
v_expectData_1599_ = lean_ctor_get(v___y_1579_, 7);
lean_inc(v_expectData_1599_);
v_handlerDispatched_1600_ = lean_ctor_get_uint8(v___y_1579_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1579_);
v___x_1601_ = lean_box(v_handlerDispatched_1600_);
v___f_1602_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1602_, 0, v_machine_1592_);
lean_closure_set(v___f_1602_, 1, v_requestStream_1593_);
lean_closure_set(v___f_1602_, 2, v_keepAliveTimeout_1594_);
lean_closure_set(v___f_1602_, 3, v_currentTimeout_1595_);
lean_closure_set(v___f_1602_, 4, v_headerTimeout_1596_);
lean_closure_set(v___f_1602_, 5, v_response_1597_);
lean_closure_set(v___f_1602_, 6, v_respStream_1598_);
lean_closure_set(v___f_1602_, 7, v_expectData_1599_);
lean_closure_set(v___f_1602_, 8, v___x_1601_);
lean_inc_ref(v___f_1602_);
v___f_1603_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1603_, 0, v___f_1602_);
v___f_1604_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1604_, 0, v_requestStream_1593_);
lean_closure_set(v___f_1604_, 1, v___f_1603_);
lean_closure_set(v___f_1604_, 2, v___f_1602_);
v___x_1605_ = lean_unsigned_to_nat(0u);
v___x_1606_ = 0;
v___x_1607_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1608_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1609_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1610_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1611_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1611_, 0, lean_box(0));
lean_closure_set(v___x_1611_, 1, lean_box(0));
lean_closure_set(v___x_1611_, 2, v___x_1607_);
lean_closure_set(v___x_1611_, 3, lean_box(0));
lean_closure_set(v___x_1611_, 4, lean_box(0));
lean_closure_set(v___x_1611_, 5, v___x_1610_);
lean_closure_set(v___x_1611_, 6, v___f_1580_);
v___x_4870__overap_1612_ = l_Std_Mutex_atomically___redArg(v___x_1607_, v___f_1608_, v___f_1609_, v_requestStream_1593_, v___x_1611_);
v___x_1613_ = lean_apply_1(v___x_4870__overap_1612_, lean_box(0));
v___x_1614_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1605_, v___x_1606_, v___x_1613_, v___f_1604_);
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1615_, lean_object* v___f_1616_, lean_object* v_x_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1615_, v___f_1616_, v_x_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1620_, lean_object* v_x_1621_){
_start:
{
if (lean_obj_tag(v_x_1621_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v___y_1620_);
v_a_1623_ = lean_ctor_get(v_x_1621_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1625_ = v_x_1621_;
v_isShared_1626_ = v_isSharedCheck_1631_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v_x_1621_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1631_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
}
}
else
{
lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1640_; 
v_isSharedCheck_1640_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; 
v_unused_1641_ = lean_ctor_get(v_x_1621_, 0);
lean_dec(v_unused_1641_);
v___x_1633_ = v_x_1621_;
v_isShared_1634_ = v_isSharedCheck_1640_;
goto v_resetjp_1632_;
}
else
{
lean_dec(v_x_1621_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1640_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___y_1620_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1635_);
v___x_1637_ = v___x_1633_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
return v___x_1638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1642_, lean_object* v_x_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1642_, v_x_1643_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1646_, lean_object* v___f_1647_, lean_object* v___y_1648_, lean_object* v_x_1649_){
_start:
{
if (lean_obj_tag(v_x_1649_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v___y_1648_);
lean_dec_ref(v___f_1647_);
lean_dec_ref(v_requestStream_1646_);
v_a_1651_ = lean_ctor_get(v_x_1649_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_x_1649_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1653_ = v_x_1649_;
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v_x_1649_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
return v___x_1657_;
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1674_; 
v_a_1660_ = lean_ctor_get(v_x_1649_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_x_1649_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1662_ = v_x_1649_;
v_isShared_1663_ = v_isSharedCheck_1674_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v_x_1649_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1674_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
uint8_t v___x_1664_; 
v___x_1664_ = lean_unbox(v_a_1660_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; 
lean_del_object(v___x_1662_);
lean_dec_ref(v___y_1648_);
v___x_1665_ = lean_unsigned_to_nat(0u);
v___x_1666_ = l_Std_Http_Body_Stream_close(v_requestStream_1646_);
v___x_1667_ = lean_unbox(v_a_1660_);
lean_dec(v_a_1660_);
v___x_1668_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1665_, v___x_1667_, v___x_1666_, v___f_1647_);
return v___x_1668_;
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
lean_dec(v_a_1660_);
lean_dec_ref(v___f_1647_);
lean_dec_ref(v_requestStream_1646_);
v___x_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___y_1648_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1669_);
v___x_1671_ = v___x_1662_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
return v___x_1672_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1675_, lean_object* v___f_1676_, lean_object* v___y_1677_, lean_object* v_x_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1675_, v___f_1676_, v___y_1677_, v_x_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1681_, lean_object* v_machine_1682_, lean_object* v_a_1683_, uint8_t v_requiresData_1684_, lean_object* v_expectData_1685_, lean_object* v_pendingHead_1686_, lean_object* v_x_1687_){
_start:
{
if (lean_obj_tag(v_x_1687_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v_pendingHead_1686_);
lean_dec(v_expectData_1685_);
lean_dec_ref(v_a_1683_);
lean_dec_ref(v_machine_1682_);
v_a_1689_ = lean_ctor_get(v_x_1687_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1691_ = v_x_1687_;
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v_x_1687_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1712_; 
v_a_1698_ = lean_ctor_get(v_x_1687_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_x_1687_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1700_ = v_x_1687_;
v_isShared_1701_ = v_isSharedCheck_1712_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v_x_1687_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1712_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_keepAliveTimeout_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v_keepAliveTimeout_1702_ = lean_ctor_get(v_config_1681_, 5);
lean_inc_n(v_keepAliveTimeout_1702_, 2);
v___x_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_keepAliveTimeout_1702_);
v___x_1704_ = lean_box(0);
v___x_1705_ = 0;
v___x_1706_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1706_, 0, v_machine_1682_);
lean_ctor_set(v___x_1706_, 1, v_a_1683_);
lean_ctor_set(v___x_1706_, 2, v___x_1703_);
lean_ctor_set(v___x_1706_, 3, v_keepAliveTimeout_1702_);
lean_ctor_set(v___x_1706_, 4, v___x_1704_);
lean_ctor_set(v___x_1706_, 5, v_a_1698_);
lean_ctor_set(v___x_1706_, 6, v___x_1704_);
lean_ctor_set(v___x_1706_, 7, v_expectData_1685_);
lean_ctor_set(v___x_1706_, 8, v_pendingHead_1686_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*9, v_requiresData_1684_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*9 + 1, v___x_1705_);
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1707_);
v___x_1709_ = v___x_1700_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1713_, lean_object* v_machine_1714_, lean_object* v_a_1715_, lean_object* v_requiresData_1716_, lean_object* v_expectData_1717_, lean_object* v_pendingHead_1718_, lean_object* v_x_1719_, lean_object* v___y_1720_){
_start:
{
uint8_t v_requiresData_boxed_1721_; lean_object* v_res_1722_; 
v_requiresData_boxed_1721_ = lean_unbox(v_requiresData_1716_);
v_res_1722_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1713_, v_machine_1714_, v_a_1715_, v_requiresData_boxed_1721_, v_expectData_1717_, v_pendingHead_1718_, v_x_1719_);
lean_dec_ref(v_config_1713_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1723_, lean_object* v_machine_1724_, uint8_t v_requiresData_1725_, lean_object* v_expectData_1726_, lean_object* v_pendingHead_1727_, lean_object* v_x_1728_){
_start:
{
if (lean_obj_tag(v_x_1728_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v_pendingHead_1727_);
lean_dec(v_expectData_1726_);
lean_dec_ref(v_machine_1724_);
lean_dec_ref(v_config_1723_);
v_a_1730_ = lean_ctor_get(v_x_1728_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_x_1728_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1732_ = v_x_1728_;
v_isShared_1733_ = v_isSharedCheck_1738_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v_x_1728_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1738_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; 
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1754_; 
v_a_1739_ = lean_ctor_get(v_x_1728_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_x_1728_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1741_ = v_x_1728_;
v_isShared_1742_ = v_isSharedCheck_1754_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v_x_1728_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1754_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v___f_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1743_ = lean_box(v_requiresData_1725_);
v___f_1744_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1744_, 0, v_config_1723_);
lean_closure_set(v___f_1744_, 1, v_machine_1724_);
lean_closure_set(v___f_1744_, 2, v_a_1739_);
lean_closure_set(v___f_1744_, 3, v___x_1743_);
lean_closure_set(v___f_1744_, 4, v_expectData_1726_);
lean_closure_set(v___f_1744_, 5, v_pendingHead_1727_);
v___x_1745_ = lean_box(0);
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = 0;
v___x_1748_ = l_Std_CloseableChannel_new___redArg(v___x_1745_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1748_);
v___x_1750_ = v___x_1741_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
v___x_1752_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1746_, v___x_1747_, v___x_1751_, v___f_1744_);
return v___x_1752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1755_, lean_object* v_machine_1756_, lean_object* v_requiresData_1757_, lean_object* v_expectData_1758_, lean_object* v_pendingHead_1759_, lean_object* v_x_1760_, lean_object* v___y_1761_){
_start:
{
uint8_t v_requiresData_boxed_1762_; lean_object* v_res_1763_; 
v_requiresData_boxed_1762_ = lean_unbox(v_requiresData_1757_);
v_res_1763_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1755_, v_machine_1756_, v_requiresData_boxed_1762_, v_expectData_1758_, v_pendingHead_1759_, v_x_1760_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1764_, lean_object* v_____r_1765_){
_start:
{
lean_object* v___x_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = 0;
v___x_1769_ = l_Std_Http_Body_mkStream();
v___x_1770_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1767_, v___x_1768_, v___x_1769_, v___f_1764_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1771_, lean_object* v_____r_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1771_, v_____r_1772_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1775_, lean_object* v_val_1776_, lean_object* v___f_1777_, lean_object* v___f_1778_, lean_object* v_x_1779_){
_start:
{
if (lean_obj_tag(v_x_1779_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v___f_1778_);
lean_dec_ref(v___f_1777_);
lean_dec(v_val_1776_);
lean_dec_ref(v_close_1775_);
v_a_1781_ = lean_ctor_get(v_x_1779_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_x_1779_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1783_ = v_x_1779_;
v_isShared_1784_ = v_isSharedCheck_1789_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v_x_1779_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1789_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
}
else
{
lean_object* v_a_1790_; uint8_t v___x_1791_; 
v_a_1790_ = lean_ctor_get(v_x_1779_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v_x_1779_, 1);
v___x_1791_ = lean_unbox(v_a_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; 
lean_dec_ref(v___f_1778_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = lean_apply_2(v_close_1775_, v_val_1776_, lean_box(0));
v___x_1794_ = lean_unbox(v_a_1790_);
lean_dec(v_a_1790_);
v___x_1795_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1792_, v___x_1794_, v___x_1793_, v___f_1777_);
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec(v_a_1790_);
lean_dec_ref(v___f_1777_);
lean_dec(v_val_1776_);
lean_dec_ref(v_close_1775_);
v___x_1796_ = lean_box(0);
v___x_1797_ = lean_apply_2(v___f_1778_, v___x_1796_, lean_box(0));
return v___x_1797_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1798_, lean_object* v_val_1799_, lean_object* v___f_1800_, lean_object* v___f_1801_, lean_object* v_x_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1798_, v_val_1799_, v___f_1800_, v___f_1801_, v_x_1802_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1805_, lean_object* v_inst_1806_, lean_object* v___f_1807_, lean_object* v___f_1808_, lean_object* v_____r_1809_){
_start:
{
if (lean_obj_tag(v_respStream_1805_) == 1)
{
lean_object* v_val_1811_; lean_object* v_close_1812_; lean_object* v_isClosed_1813_; lean_object* v___f_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v_val_1811_ = lean_ctor_get(v_respStream_1805_, 0);
lean_inc_n(v_val_1811_, 2);
lean_dec_ref_known(v_respStream_1805_, 1);
v_close_1812_ = lean_ctor_get(v_inst_1806_, 1);
lean_inc_ref(v_close_1812_);
v_isClosed_1813_ = lean_ctor_get(v_inst_1806_, 2);
lean_inc_ref(v_isClosed_1813_);
lean_dec_ref(v_inst_1806_);
v___f_1814_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1814_, 0, v_close_1812_);
lean_closure_set(v___f_1814_, 1, v_val_1811_);
lean_closure_set(v___f_1814_, 2, v___f_1807_);
lean_closure_set(v___f_1814_, 3, v___f_1808_);
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = 0;
v___x_1817_ = lean_apply_2(v_isClosed_1813_, v_val_1811_, lean_box(0));
v___x_1818_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1815_, v___x_1816_, v___x_1817_, v___f_1814_);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec_ref(v___f_1807_);
lean_dec_ref(v_inst_1806_);
lean_dec(v_respStream_1805_);
v___x_1819_ = lean_box(0);
v___x_1820_ = lean_apply_2(v___f_1808_, v___x_1819_, lean_box(0));
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_1821_, lean_object* v_inst_1822_, lean_object* v___f_1823_, lean_object* v___f_1824_, lean_object* v_____r_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_1821_, v_inst_1822_, v___f_1823_, v___f_1824_, v_____r_1825_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_1828_, lean_object* v_keepAliveTimeout_1829_, lean_object* v_currentTimeout_1830_, lean_object* v_headerTimeout_1831_, lean_object* v_response_1832_, lean_object* v_respStream_1833_, uint8_t v_requiresData_1834_, lean_object* v_expectData_1835_, uint8_t v_handlerDispatched_1836_, lean_object* v_pendingHead_1837_, lean_object* v_x_1838_){
_start:
{
if (lean_obj_tag(v_x_1838_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_pendingHead_1837_);
lean_dec(v_expectData_1835_);
lean_dec(v_respStream_1833_);
lean_dec_ref(v_response_1832_);
lean_dec(v_headerTimeout_1831_);
lean_dec(v_currentTimeout_1830_);
lean_dec(v_keepAliveTimeout_1829_);
lean_dec_ref(v_requestStream_1828_);
v_a_1840_ = lean_ctor_get(v_x_1838_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_x_1838_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1842_ = v_x_1838_;
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v_x_1838_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1848_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1870_; 
v_a_1849_ = lean_ctor_get(v_x_1838_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_x_1838_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1851_ = v_x_1838_;
v_isShared_1852_ = v_isSharedCheck_1870_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v_x_1838_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1870_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v_snd_1853_; uint8_t v___x_1854_; 
v_snd_1853_ = lean_ctor_get(v_a_1849_, 1);
v___x_1854_ = lean_unbox(v_snd_1853_);
if (v___x_1854_ == 0)
{
lean_object* v_fst_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v_fst_1855_ = lean_ctor_get(v_a_1849_, 0);
lean_inc(v_fst_1855_);
lean_dec(v_a_1849_);
v___x_1856_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1856_, 0, v_fst_1855_);
lean_ctor_set(v___x_1856_, 1, v_requestStream_1828_);
lean_ctor_set(v___x_1856_, 2, v_keepAliveTimeout_1829_);
lean_ctor_set(v___x_1856_, 3, v_currentTimeout_1830_);
lean_ctor_set(v___x_1856_, 4, v_headerTimeout_1831_);
lean_ctor_set(v___x_1856_, 5, v_response_1832_);
lean_ctor_set(v___x_1856_, 6, v_respStream_1833_);
lean_ctor_set(v___x_1856_, 7, v_expectData_1835_);
lean_ctor_set(v___x_1856_, 8, v_pendingHead_1837_);
lean_ctor_set_uint8(v___x_1856_, sizeof(void*)*9, v_requiresData_1834_);
lean_ctor_set_uint8(v___x_1856_, sizeof(void*)*9 + 1, v_handlerDispatched_1836_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1857_);
v___x_1859_ = v___x_1851_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
}
else
{
lean_object* v_fst_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
lean_dec(v_pendingHead_1837_);
v_fst_1862_ = lean_ctor_get(v_a_1849_, 0);
lean_inc(v_fst_1862_);
lean_dec(v_a_1849_);
v___x_1863_ = lean_box(0);
v___x_1864_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1864_, 0, v_fst_1862_);
lean_ctor_set(v___x_1864_, 1, v_requestStream_1828_);
lean_ctor_set(v___x_1864_, 2, v_keepAliveTimeout_1829_);
lean_ctor_set(v___x_1864_, 3, v_currentTimeout_1830_);
lean_ctor_set(v___x_1864_, 4, v_headerTimeout_1831_);
lean_ctor_set(v___x_1864_, 5, v_response_1832_);
lean_ctor_set(v___x_1864_, 6, v_respStream_1833_);
lean_ctor_set(v___x_1864_, 7, v_expectData_1835_);
lean_ctor_set(v___x_1864_, 8, v___x_1863_);
lean_ctor_set_uint8(v___x_1864_, sizeof(void*)*9, v_requiresData_1834_);
lean_ctor_set_uint8(v___x_1864_, sizeof(void*)*9 + 1, v_handlerDispatched_1836_);
v___x_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1865_);
v___x_1867_ = v___x_1851_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
return v___x_1868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_1871_, lean_object* v_keepAliveTimeout_1872_, lean_object* v_currentTimeout_1873_, lean_object* v_headerTimeout_1874_, lean_object* v_response_1875_, lean_object* v_respStream_1876_, lean_object* v_requiresData_1877_, lean_object* v_expectData_1878_, lean_object* v_handlerDispatched_1879_, lean_object* v_pendingHead_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_){
_start:
{
uint8_t v_requiresData_boxed_1883_; uint8_t v_handlerDispatched_boxed_1884_; lean_object* v_res_1885_; 
v_requiresData_boxed_1883_ = lean_unbox(v_requiresData_1877_);
v_handlerDispatched_boxed_1884_ = lean_unbox(v_handlerDispatched_1879_);
v_res_1885_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_1871_, v_keepAliveTimeout_1872_, v_currentTimeout_1873_, v_headerTimeout_1874_, v_response_1875_, v_respStream_1876_, v_requiresData_boxed_1883_, v_expectData_1878_, v_handlerDispatched_boxed_1884_, v_pendingHead_1880_, v_x_1881_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_1898_, lean_object* v_inst_1899_, lean_object* v___f_1900_, lean_object* v_handler_1901_, lean_object* v___f_1902_, lean_object* v_inst_1903_, lean_object* v___f_1904_, lean_object* v_connectionContext_1905_, lean_object* v_a_1906_, lean_object* v_x_1907_, lean_object* v___y_1908_){
_start:
{
switch(lean_obj_tag(v_a_1906_))
{
case 0:
{
lean_object* v_head_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v_connectionContext_1905_);
lean_dec_ref(v___f_1904_);
lean_dec_ref(v_inst_1903_);
lean_dec_ref(v___f_1902_);
lean_dec(v_handler_1901_);
lean_dec_ref(v___f_1900_);
lean_dec_ref(v_inst_1899_);
v_head_1910_ = lean_ctor_get(v_a_1906_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_a_1906_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1912_ = v_a_1906_;
v_isShared_1913_ = v_isSharedCheck_1953_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_head_1910_);
lean_dec(v_a_1906_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1953_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v_machine_1914_; lean_object* v_requestStream_1915_; lean_object* v_response_1916_; lean_object* v_respStream_1917_; uint8_t v_requiresData_1918_; lean_object* v_expectData_1919_; uint8_t v_handlerDispatched_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1948_; 
v_machine_1914_ = lean_ctor_get(v___y_1908_, 0);
v_requestStream_1915_ = lean_ctor_get(v___y_1908_, 1);
v_response_1916_ = lean_ctor_get(v___y_1908_, 5);
v_respStream_1917_ = lean_ctor_get(v___y_1908_, 6);
v_requiresData_1918_ = lean_ctor_get_uint8(v___y_1908_, sizeof(void*)*9);
v_expectData_1919_ = lean_ctor_get(v___y_1908_, 7);
v_handlerDispatched_1920_ = lean_ctor_get_uint8(v___y_1908_, sizeof(void*)*9 + 1);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___y_1908_);
if (v_isSharedCheck_1948_ == 0)
{
lean_object* v_unused_1949_; lean_object* v_unused_1950_; lean_object* v_unused_1951_; lean_object* v_unused_1952_; 
v_unused_1949_ = lean_ctor_get(v___y_1908_, 8);
lean_dec(v_unused_1949_);
v_unused_1950_ = lean_ctor_get(v___y_1908_, 4);
lean_dec(v_unused_1950_);
v_unused_1951_ = lean_ctor_get(v___y_1908_, 3);
lean_dec(v_unused_1951_);
v_unused_1952_ = lean_ctor_get(v___y_1908_, 2);
lean_dec(v_unused_1952_);
v___x_1922_ = v___y_1908_;
v_isShared_1923_ = v_isSharedCheck_1948_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_expectData_1919_);
lean_inc(v_respStream_1917_);
lean_inc(v_response_1916_);
lean_inc(v_requestStream_1915_);
lean_inc(v_machine_1914_);
lean_dec(v___y_1908_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1948_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_lingeringTimeout_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v_lingeringTimeout_1924_ = lean_ctor_get(v_config_1898_, 4);
lean_inc(v_lingeringTimeout_1924_);
lean_dec_ref(v_config_1898_);
v___x_1925_ = lean_box(0);
lean_inc(v_head_1910_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set_tag(v___x_1912_, 1);
v___x_1927_ = v___x_1912_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_head_1910_);
v___x_1927_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1929_; 
lean_inc_ref(v_requestStream_1915_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 8, v___x_1927_);
lean_ctor_set(v___x_1922_, 4, v___x_1925_);
lean_ctor_set(v___x_1922_, 3, v_lingeringTimeout_1924_);
lean_ctor_set(v___x_1922_, 2, v___x_1925_);
v___x_1929_ = v___x_1922_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_machine_1914_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_requestStream_1915_);
lean_ctor_set(v_reuseFailAlloc_1946_, 2, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1946_, 3, v_lingeringTimeout_1924_);
lean_ctor_set(v_reuseFailAlloc_1946_, 4, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1946_, 5, v_response_1916_);
lean_ctor_set(v_reuseFailAlloc_1946_, 6, v_respStream_1917_);
lean_ctor_set(v_reuseFailAlloc_1946_, 7, v_expectData_1919_);
lean_ctor_set(v_reuseFailAlloc_1946_, 8, v___x_1927_);
lean_ctor_set_uint8(v_reuseFailAlloc_1946_, sizeof(void*)*9, v_requiresData_1918_);
lean_ctor_set_uint8(v_reuseFailAlloc_1946_, sizeof(void*)*9 + 1, v_handlerDispatched_1920_);
v___x_1929_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
uint8_t v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = 0;
v___x_1931_ = 1;
v___x_1932_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_1930_, v_head_1910_, v___x_1931_);
lean_dec(v_head_1910_);
if (lean_obj_tag(v___x_1932_) == 1)
{
lean_object* v___f_1933_; lean_object* v___f_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; lean_object* v___x_1937_; lean_object* v___f_1938_; lean_object* v___f_1939_; lean_object* v___x_5061__overap_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___f_1933_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1933_, 0, v___x_1929_);
v___f_1934_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1934_, 0, v___x_1932_);
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = 0;
v___x_1937_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1938_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1939_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5061__overap_1940_ = l_Std_Mutex_atomically___redArg(v___x_1937_, v___f_1938_, v___f_1939_, v_requestStream_1915_, v___f_1934_);
v___x_1941_ = lean_apply_1(v___x_5061__overap_1940_, lean_box(0));
v___x_1942_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1935_, v___x_1936_, v___x_1941_, v___f_1933_);
return v___x_1942_;
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
lean_dec(v___x_1932_);
lean_dec_ref(v_requestStream_1915_);
v___x_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1929_);
v___x_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
return v___x_1945_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v_connectionContext_1905_);
lean_dec_ref(v___f_1904_);
lean_dec_ref(v_inst_1903_);
lean_dec_ref(v___f_1902_);
lean_dec(v_handler_1901_);
lean_dec_ref(v___f_1900_);
lean_dec_ref(v_inst_1899_);
lean_dec_ref(v_config_1898_);
v_size_1954_ = lean_ctor_get(v_a_1906_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_a_1906_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1956_ = v_a_1906_;
v_isShared_1957_ = v_isSharedCheck_1981_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_size_1954_);
lean_dec(v_a_1906_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1981_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v_machine_1958_; lean_object* v_requestStream_1959_; lean_object* v_keepAliveTimeout_1960_; lean_object* v_currentTimeout_1961_; lean_object* v_headerTimeout_1962_; lean_object* v_response_1963_; lean_object* v_respStream_1964_; uint8_t v_handlerDispatched_1965_; lean_object* v_pendingHead_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1979_; 
v_machine_1958_ = lean_ctor_get(v___y_1908_, 0);
v_requestStream_1959_ = lean_ctor_get(v___y_1908_, 1);
v_keepAliveTimeout_1960_ = lean_ctor_get(v___y_1908_, 2);
v_currentTimeout_1961_ = lean_ctor_get(v___y_1908_, 3);
v_headerTimeout_1962_ = lean_ctor_get(v___y_1908_, 4);
v_response_1963_ = lean_ctor_get(v___y_1908_, 5);
v_respStream_1964_ = lean_ctor_get(v___y_1908_, 6);
v_handlerDispatched_1965_ = lean_ctor_get_uint8(v___y_1908_, sizeof(void*)*9 + 1);
v_pendingHead_1966_ = lean_ctor_get(v___y_1908_, 8);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___y_1908_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v___y_1908_, 7);
lean_dec(v_unused_1980_);
v___x_1968_ = v___y_1908_;
v_isShared_1969_ = v_isSharedCheck_1979_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_pendingHead_1966_);
lean_inc(v_respStream_1964_);
lean_inc(v_response_1963_);
lean_inc(v_headerTimeout_1962_);
lean_inc(v_currentTimeout_1961_);
lean_inc(v_keepAliveTimeout_1960_);
lean_inc(v_requestStream_1959_);
lean_inc(v_machine_1958_);
lean_dec(v___y_1908_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1979_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
uint8_t v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = 1;
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 7, v_size_1954_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_machine_1958_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_requestStream_1959_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v_keepAliveTimeout_1960_);
lean_ctor_set(v_reuseFailAlloc_1978_, 3, v_currentTimeout_1961_);
lean_ctor_set(v_reuseFailAlloc_1978_, 4, v_headerTimeout_1962_);
lean_ctor_set(v_reuseFailAlloc_1978_, 5, v_response_1963_);
lean_ctor_set(v_reuseFailAlloc_1978_, 6, v_respStream_1964_);
lean_ctor_set(v_reuseFailAlloc_1978_, 7, v_size_1954_);
lean_ctor_set(v_reuseFailAlloc_1978_, 8, v_pendingHead_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*9 + 1, v_handlerDispatched_1965_);
v___x_1972_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1974_; 
lean_ctor_set_uint8(v___x_1972_, sizeof(void*)*9, v___x_1970_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1972_);
v___x_1974_ = v___x_1956_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
return v___x_1976_;
}
}
}
}
}
case 2:
{
lean_object* v_err_1982_; lean_object* v_onFailure_1983_; lean_object* v___f_1984_; lean_object* v___y_1986_; 
lean_dec_ref(v_connectionContext_1905_);
lean_dec_ref(v___f_1904_);
lean_dec_ref(v_inst_1903_);
lean_dec_ref(v___f_1902_);
lean_dec_ref(v_config_1898_);
v_err_1982_ = lean_ctor_get(v_a_1906_, 0);
lean_inc(v_err_1982_);
lean_dec_ref_known(v_a_1906_, 1);
v_onFailure_1983_ = lean_ctor_get(v_inst_1899_, 2);
lean_inc_ref(v_onFailure_1983_);
lean_dec_ref(v_inst_1899_);
v___f_1984_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_1984_, 0, v___y_1908_);
lean_closure_set(v___f_1984_, 1, v___f_1900_);
switch(lean_obj_tag(v_err_1982_))
{
case 0:
{
lean_object* v___x_1992_; 
v___x_1992_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_1986_ = v___x_1992_;
goto v___jp_1985_;
}
case 1:
{
lean_object* v___x_1993_; 
v___x_1993_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_1986_ = v___x_1993_;
goto v___jp_1985_;
}
case 2:
{
lean_object* v___x_1994_; 
v___x_1994_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_1986_ = v___x_1994_;
goto v___jp_1985_;
}
case 3:
{
lean_object* v___x_1995_; 
v___x_1995_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_1986_ = v___x_1995_;
goto v___jp_1985_;
}
case 4:
{
lean_object* v___x_1996_; 
v___x_1996_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_1986_ = v___x_1996_;
goto v___jp_1985_;
}
case 5:
{
lean_object* v___x_1997_; 
v___x_1997_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_1986_ = v___x_1997_;
goto v___jp_1985_;
}
case 6:
{
lean_object* v___x_1998_; 
v___x_1998_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_1986_ = v___x_1998_;
goto v___jp_1985_;
}
case 7:
{
lean_object* v___x_1999_; 
v___x_1999_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_1986_ = v___x_1999_;
goto v___jp_1985_;
}
case 8:
{
lean_object* v___x_2000_; 
v___x_2000_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_1986_ = v___x_2000_;
goto v___jp_1985_;
}
case 9:
{
lean_object* v___x_2001_; 
v___x_2001_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_1986_ = v___x_2001_;
goto v___jp_1985_;
}
case 10:
{
lean_object* v___x_2002_; 
v___x_2002_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_1986_ = v___x_2002_;
goto v___jp_1985_;
}
default: 
{
lean_object* v_message_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v_message_2003_ = lean_ctor_get(v_err_1982_, 0);
lean_inc_ref(v_message_2003_);
lean_dec_ref_known(v_err_1982_, 1);
v___x_2004_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_2005_ = lean_string_append(v___x_2004_, v_message_2003_);
lean_dec_ref(v_message_2003_);
v___y_1986_ = v___x_2005_;
goto v___jp_1985_;
}
}
v___jp_1985_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1987_ = lean_mk_io_user_error(v___y_1986_);
v___x_1988_ = lean_unsigned_to_nat(0u);
v___x_1989_ = 0;
v___x_1990_ = lean_apply_3(v_onFailure_1983_, v_handler_1901_, v___x_1987_, lean_box(0));
v___x_1991_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1988_, v___x_1989_, v___x_1990_, v___f_1984_);
return v___x_1991_;
}
}
case 4:
{
lean_object* v_requestStream_2006_; lean_object* v___f_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; lean_object* v___f_2012_; lean_object* v___f_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_5118__overap_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec_ref(v_connectionContext_1905_);
lean_dec_ref(v___f_1904_);
lean_dec_ref(v_inst_1903_);
lean_dec(v_handler_1901_);
lean_dec_ref(v___f_1900_);
lean_dec_ref(v_inst_1899_);
lean_dec_ref(v_config_1898_);
v_requestStream_2006_ = lean_ctor_get(v___y_1908_, 1);
lean_inc_ref_n(v_requestStream_2006_, 2);
lean_inc_ref(v___y_1908_);
v___f_2007_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2007_, 0, v___y_1908_);
v___f_2008_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_2008_, 0, v_requestStream_2006_);
lean_closure_set(v___f_2008_, 1, v___f_2007_);
lean_closure_set(v___f_2008_, 2, v___y_1908_);
v___x_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = 0;
v___x_2011_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2012_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2013_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2014_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2015_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2015_, 0, lean_box(0));
lean_closure_set(v___x_2015_, 1, lean_box(0));
lean_closure_set(v___x_2015_, 2, v___x_2011_);
lean_closure_set(v___x_2015_, 3, lean_box(0));
lean_closure_set(v___x_2015_, 4, lean_box(0));
lean_closure_set(v___x_2015_, 5, v___x_2014_);
lean_closure_set(v___x_2015_, 6, v___f_1902_);
v___x_5118__overap_2016_ = l_Std_Mutex_atomically___redArg(v___x_2011_, v___f_2012_, v___f_2013_, v_requestStream_2006_, v___x_2015_);
v___x_2017_ = lean_apply_1(v___x_5118__overap_2016_, lean_box(0));
v___x_2018_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2009_, v___x_2010_, v___x_2017_, v___f_2008_);
return v___x_2018_;
}
case 6:
{
lean_object* v_machine_2019_; lean_object* v_requestStream_2020_; lean_object* v_respStream_2021_; uint8_t v_requiresData_2022_; lean_object* v_expectData_2023_; lean_object* v_pendingHead_2024_; lean_object* v___x_2025_; lean_object* v___f_2026_; lean_object* v___f_2027_; lean_object* v___f_2028_; lean_object* v___f_2029_; lean_object* v___f_2030_; lean_object* v___f_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___f_2035_; lean_object* v___f_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_5143__overap_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_dec_ref(v_connectionContext_1905_);
lean_dec_ref(v___f_1902_);
lean_dec(v_handler_1901_);
lean_dec_ref(v___f_1900_);
lean_dec_ref(v_inst_1899_);
v_machine_2019_ = lean_ctor_get(v___y_1908_, 0);
lean_inc_ref(v_machine_2019_);
v_requestStream_2020_ = lean_ctor_get(v___y_1908_, 1);
lean_inc_ref_n(v_requestStream_2020_, 2);
v_respStream_2021_ = lean_ctor_get(v___y_1908_, 6);
lean_inc(v_respStream_2021_);
v_requiresData_2022_ = lean_ctor_get_uint8(v___y_1908_, sizeof(void*)*9);
v_expectData_2023_ = lean_ctor_get(v___y_1908_, 7);
lean_inc(v_expectData_2023_);
v_pendingHead_2024_ = lean_ctor_get(v___y_1908_, 8);
lean_inc(v_pendingHead_2024_);
lean_dec_ref(v___y_1908_);
v___x_2025_ = lean_box(v_requiresData_2022_);
v___f_2026_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2026_, 0, v_config_1898_);
lean_closure_set(v___f_2026_, 1, v_machine_2019_);
lean_closure_set(v___f_2026_, 2, v___x_2025_);
lean_closure_set(v___f_2026_, 3, v_expectData_2023_);
lean_closure_set(v___f_2026_, 4, v_pendingHead_2024_);
v___f_2027_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2027_, 0, v___f_2026_);
lean_inc_ref(v___f_2027_);
v___f_2028_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2028_, 0, v___f_2027_);
v___f_2029_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2029_, 0, v_respStream_2021_);
lean_closure_set(v___f_2029_, 1, v_inst_1903_);
lean_closure_set(v___f_2029_, 2, v___f_2028_);
lean_closure_set(v___f_2029_, 3, v___f_2027_);
lean_inc_ref(v___f_2029_);
v___f_2030_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2030_, 0, v___f_2029_);
v___f_2031_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2031_, 0, v_requestStream_2020_);
lean_closure_set(v___f_2031_, 1, v___f_2030_);
lean_closure_set(v___f_2031_, 2, v___f_2029_);
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = 0;
v___x_2034_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2035_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2036_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2037_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2038_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2038_, 0, lean_box(0));
lean_closure_set(v___x_2038_, 1, lean_box(0));
lean_closure_set(v___x_2038_, 2, v___x_2034_);
lean_closure_set(v___x_2038_, 3, lean_box(0));
lean_closure_set(v___x_2038_, 4, lean_box(0));
lean_closure_set(v___x_2038_, 5, v___x_2037_);
lean_closure_set(v___x_2038_, 6, v___f_1904_);
v___x_5143__overap_2039_ = l_Std_Mutex_atomically___redArg(v___x_2034_, v___f_2035_, v___f_2036_, v_requestStream_2020_, v___x_2038_);
v___x_2040_ = lean_apply_1(v___x_5143__overap_2039_, lean_box(0));
v___x_2041_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2032_, v___x_2033_, v___x_2040_, v___f_2031_);
return v___x_2041_;
}
case 7:
{
lean_object* v_pendingHead_2042_; 
lean_dec_ref(v___f_1904_);
lean_dec_ref(v_inst_1903_);
lean_dec_ref(v___f_1902_);
lean_dec_ref(v___f_1900_);
v_pendingHead_2042_ = lean_ctor_get(v___y_1908_, 8);
if (lean_obj_tag(v_pendingHead_2042_) == 1)
{
lean_object* v_machine_2043_; lean_object* v_requestStream_2044_; lean_object* v_keepAliveTimeout_2045_; lean_object* v_currentTimeout_2046_; lean_object* v_headerTimeout_2047_; lean_object* v_response_2048_; lean_object* v_respStream_2049_; uint8_t v_requiresData_2050_; lean_object* v_expectData_2051_; uint8_t v_handlerDispatched_2052_; lean_object* v_val_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___f_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_inc_ref(v_pendingHead_2042_);
v_machine_2043_ = lean_ctor_get(v___y_1908_, 0);
lean_inc_ref(v_machine_2043_);
v_requestStream_2044_ = lean_ctor_get(v___y_1908_, 1);
lean_inc_ref(v_requestStream_2044_);
v_keepAliveTimeout_2045_ = lean_ctor_get(v___y_1908_, 2);
lean_inc(v_keepAliveTimeout_2045_);
v_currentTimeout_2046_ = lean_ctor_get(v___y_1908_, 3);
lean_inc(v_currentTimeout_2046_);
v_headerTimeout_2047_ = lean_ctor_get(v___y_1908_, 4);
lean_inc(v_headerTimeout_2047_);
v_response_2048_ = lean_ctor_get(v___y_1908_, 5);
lean_inc_ref(v_response_2048_);
v_respStream_2049_ = lean_ctor_get(v___y_1908_, 6);
lean_inc(v_respStream_2049_);
v_requiresData_2050_ = lean_ctor_get_uint8(v___y_1908_, sizeof(void*)*9);
v_expectData_2051_ = lean_ctor_get(v___y_1908_, 7);
lean_inc(v_expectData_2051_);
v_handlerDispatched_2052_ = lean_ctor_get_uint8(v___y_1908_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1908_);
v_val_2053_ = lean_ctor_get(v_pendingHead_2042_, 0);
lean_inc(v_val_2053_);
v___x_2054_ = lean_box(v_requiresData_2050_);
v___x_2055_ = lean_box(v_handlerDispatched_2052_);
v___f_2056_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2056_, 0, v_requestStream_2044_);
lean_closure_set(v___f_2056_, 1, v_keepAliveTimeout_2045_);
lean_closure_set(v___f_2056_, 2, v_currentTimeout_2046_);
lean_closure_set(v___f_2056_, 3, v_headerTimeout_2047_);
lean_closure_set(v___f_2056_, 4, v_response_2048_);
lean_closure_set(v___f_2056_, 5, v_respStream_2049_);
lean_closure_set(v___f_2056_, 6, v___x_2054_);
lean_closure_set(v___f_2056_, 7, v_expectData_2051_);
lean_closure_set(v___f_2056_, 8, v___x_2055_);
lean_closure_set(v___f_2056_, 9, v_pendingHead_2042_);
v___x_2057_ = lean_unsigned_to_nat(0u);
v___x_2058_ = 0;
v___x_2059_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_1899_, v_handler_1901_, v_machine_2043_, v_val_2053_, v_config_1898_, v_connectionContext_1905_);
v___x_2060_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2057_, v___x_2058_, v___x_2059_, v___f_2056_);
return v___x_2060_;
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec_ref(v_connectionContext_1905_);
lean_dec(v_handler_1901_);
lean_dec_ref(v_inst_1899_);
lean_dec_ref(v_config_1898_);
v___x_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___y_1908_);
v___x_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
return v___x_2063_;
}
}
default: 
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec(v_a_1906_);
lean_dec_ref(v_connectionContext_1905_);
lean_dec_ref(v___f_1904_);
lean_dec_ref(v_inst_1903_);
lean_dec_ref(v___f_1902_);
lean_dec(v_handler_1901_);
lean_dec_ref(v___f_1900_);
lean_dec_ref(v_inst_1899_);
lean_dec_ref(v_config_1898_);
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___y_1908_);
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
return v___x_2066_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2067_, lean_object* v_inst_2068_, lean_object* v___f_2069_, lean_object* v_handler_2070_, lean_object* v___f_2071_, lean_object* v_inst_2072_, lean_object* v___f_2073_, lean_object* v_connectionContext_2074_, lean_object* v_a_2075_, lean_object* v_x_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2067_, v_inst_2068_, v___f_2069_, v_handler_2070_, v___f_2071_, v_inst_2072_, v___f_2073_, v_connectionContext_2074_, v_a_2075_, v_x_2076_, v___y_2077_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2080_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v_x_2080_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2083_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2088_, lean_object* v_inst_2089_, lean_object* v_handler_2090_, lean_object* v_config_2091_, lean_object* v_connectionContext_2092_, lean_object* v_events_2093_, lean_object* v_state_2094_){
_start:
{
lean_object* v___f_2096_; lean_object* v___f_2097_; lean_object* v___f_2098_; lean_object* v___x_2099_; size_t v_sz_2100_; size_t v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; lean_object* v___x_4072__overap_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___f_2096_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2097_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2097_, 0, v_config_2091_);
lean_closure_set(v___f_2097_, 1, v_inst_2088_);
lean_closure_set(v___f_2097_, 2, v___f_2096_);
lean_closure_set(v___f_2097_, 3, v_handler_2090_);
lean_closure_set(v___f_2097_, 4, v___f_2096_);
lean_closure_set(v___f_2097_, 5, v_inst_2089_);
lean_closure_set(v___f_2097_, 6, v___f_2096_);
lean_closure_set(v___f_2097_, 7, v_connectionContext_2092_);
v___f_2098_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2099_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2100_ = lean_array_size(v_events_2093_);
v___x_2101_ = ((size_t)0ULL);
v___x_2102_ = lean_unsigned_to_nat(0u);
v___x_2103_ = 0;
v___x_4072__overap_2104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2099_, v_events_2093_, v___f_2097_, v_sz_2100_, v___x_2101_, v_state_2094_);
v___x_2105_ = lean_apply_1(v___x_4072__overap_2104_, lean_box(0));
v___x_2106_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2102_, v___x_2103_, v___x_2105_, v___f_2098_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2107_, lean_object* v_inst_2108_, lean_object* v_handler_2109_, lean_object* v_config_2110_, lean_object* v_connectionContext_2111_, lean_object* v_events_2112_, lean_object* v_state_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2107_, v_inst_2108_, v_handler_2109_, v_config_2110_, v_connectionContext_2111_, v_events_2112_, v_state_2113_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2116_, lean_object* v_00_u03b2_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_handler_2120_, lean_object* v_config_2121_, lean_object* v_connectionContext_2122_, lean_object* v_events_2123_, lean_object* v_state_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2118_, v_inst_2119_, v_handler_2120_, v_config_2121_, v_connectionContext_2122_, v_events_2123_, v_state_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2127_, lean_object* v_00_u03b2_2128_, lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_handler_2131_, lean_object* v_config_2132_, lean_object* v_connectionContext_2133_, lean_object* v_events_2134_, lean_object* v_state_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2127_, v_00_u03b2_2128_, v_inst_2129_, v_inst_2130_, v_handler_2131_, v_config_2132_, v_connectionContext_2133_, v_events_2134_, v_state_2135_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2138_){
_start:
{
if (lean_obj_tag(v_x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; 
v_a_2139_ = lean_ctor_get(v_x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v_x_2138_, 1);
v___x_2140_ = lean_task_pure(v_a_2139_);
return v___x_2140_;
}
else
{
lean_object* v_a_2141_; 
v_a_2141_ = lean_ctor_get(v_x_2138_, 0);
lean_inc_ref(v_a_2141_);
lean_dec_ref_known(v_x_2138_, 1);
return v_a_2141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2142_, lean_object* v_requestStream_2143_, lean_object* v_keepAliveTimeout_2144_, lean_object* v_currentTimeout_2145_, lean_object* v_headerTimeout_2146_, lean_object* v_response_2147_, lean_object* v_respStream_2148_, uint8_t v_requiresData_2149_, lean_object* v_expectData_2150_, lean_object* v_x_2151_){
_start:
{
if (lean_obj_tag(v_x_2151_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_expectData_2150_);
lean_dec(v_respStream_2148_);
lean_dec_ref(v_response_2147_);
lean_dec(v_headerTimeout_2146_);
lean_dec(v_currentTimeout_2145_);
lean_dec(v_keepAliveTimeout_2144_);
lean_dec_ref(v_requestStream_2143_);
lean_dec_ref(v_machine_2142_);
v_a_2153_ = lean_ctor_get(v_x_2151_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_x_2151_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2155_ = v_x_2151_;
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v_x_2151_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2161_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; 
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
return v___x_2159_;
}
}
}
else
{
lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2172_; 
v_isSharedCheck_2172_ = !lean_is_exclusive(v_x_2151_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; 
v_unused_2173_ = lean_ctor_get(v_x_2151_, 0);
lean_dec(v_unused_2173_);
v___x_2163_ = v_x_2151_;
v_isShared_2164_ = v_isSharedCheck_2172_;
goto v_resetjp_2162_;
}
else
{
lean_dec(v_x_2151_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2172_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2165_ = 1;
v___x_2166_ = lean_box(0);
v___x_2167_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2167_, 0, v_machine_2142_);
lean_ctor_set(v___x_2167_, 1, v_requestStream_2143_);
lean_ctor_set(v___x_2167_, 2, v_keepAliveTimeout_2144_);
lean_ctor_set(v___x_2167_, 3, v_currentTimeout_2145_);
lean_ctor_set(v___x_2167_, 4, v_headerTimeout_2146_);
lean_ctor_set(v___x_2167_, 5, v_response_2147_);
lean_ctor_set(v___x_2167_, 6, v_respStream_2148_);
lean_ctor_set(v___x_2167_, 7, v_expectData_2150_);
lean_ctor_set(v___x_2167_, 8, v___x_2166_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*9, v_requiresData_2149_);
lean_ctor_set_uint8(v___x_2167_, sizeof(void*)*9 + 1, v___x_2165_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2167_);
v___x_2169_ = v___x_2163_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2170_; 
v___x_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
return v___x_2170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2174_, lean_object* v_requestStream_2175_, lean_object* v_keepAliveTimeout_2176_, lean_object* v_currentTimeout_2177_, lean_object* v_headerTimeout_2178_, lean_object* v_response_2179_, lean_object* v_respStream_2180_, lean_object* v_requiresData_2181_, lean_object* v_expectData_2182_, lean_object* v_x_2183_, lean_object* v___y_2184_){
_start:
{
uint8_t v_requiresData_boxed_2185_; lean_object* v_res_2186_; 
v_requiresData_boxed_2185_ = lean_unbox(v_requiresData_2181_);
v_res_2186_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2174_, v_requestStream_2175_, v_keepAliveTimeout_2176_, v_currentTimeout_2177_, v_headerTimeout_2178_, v_response_2179_, v_respStream_2180_, v_requiresData_boxed_2185_, v_expectData_2182_, v_x_2183_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2187_, lean_object* v_response_2188_, lean_object* v___x_2189_, lean_object* v___f_2190_, lean_object* v_x_2191_){
_start:
{
if (lean_obj_tag(v_x_2191_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2201_; 
lean_dec_ref(v___f_2190_);
lean_dec(v___x_2189_);
lean_dec_ref(v_response_2188_);
lean_dec_ref(v_toFunctor_2187_);
v_a_2193_ = lean_ctor_get(v_x_2191_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_x_2191_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2195_ = v_x_2191_;
v_isShared_2196_ = v_isSharedCheck_2201_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v_x_2191_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2201_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2216_; 
v_a_2202_ = lean_ctor_get(v_x_2191_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_x_2191_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2204_ = v_x_2191_;
v_isShared_2205_ = v_isSharedCheck_2216_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v_x_2191_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2216_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2206_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2206_, 0, lean_box(0));
lean_closure_set(v___x_2206_, 1, lean_box(0));
lean_closure_set(v___x_2206_, 2, v_toFunctor_2187_);
v___x_2207_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2207_, 0, lean_box(0));
lean_closure_set(v___x_2207_, 1, v_response_2188_);
v___x_2208_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2208_, 0, lean_box(0));
lean_closure_set(v___x_2208_, 1, lean_box(0));
lean_closure_set(v___x_2208_, 2, lean_box(0));
lean_closure_set(v___x_2208_, 3, v___x_2206_);
lean_closure_set(v___x_2208_, 4, v___x_2207_);
v___x_2209_ = 0;
lean_inc(v___x_2189_);
v___x_2210_ = l_BaseIO_chainTask___redArg(v_a_2202_, v___x_2208_, v___x_2189_, v___x_2209_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2210_);
v___x_2212_ = v___x_2204_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
v___x_2214_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2189_, v___x_2209_, v___x_2213_, v___f_2190_);
return v___x_2214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2217_, lean_object* v_response_2218_, lean_object* v___x_2219_, lean_object* v___f_2220_, lean_object* v_x_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2217_, v_response_2218_, v___x_2219_, v___f_2220_, v_x_2221_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2225_, lean_object* v_handler_2226_, lean_object* v_extensions_2227_, lean_object* v_connectionContext_2228_, lean_object* v_state_2229_){
_start:
{
lean_object* v___x_2231_; lean_object* v_toApplicative_2232_; lean_object* v_pendingHead_2233_; 
v___x_2231_ = l_instMonadBaseIO;
v_toApplicative_2232_ = lean_ctor_get(v___x_2231_, 0);
v_pendingHead_2233_ = lean_ctor_get(v_state_2229_, 8);
lean_inc(v_pendingHead_2233_);
if (lean_obj_tag(v_pendingHead_2233_) == 1)
{
lean_object* v_toFunctor_2234_; lean_object* v_machine_2235_; lean_object* v_requestStream_2236_; lean_object* v_keepAliveTimeout_2237_; lean_object* v_currentTimeout_2238_; lean_object* v_headerTimeout_2239_; lean_object* v_response_2240_; lean_object* v_respStream_2241_; uint8_t v_requiresData_2242_; lean_object* v_expectData_2243_; lean_object* v_val_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2266_; 
v_toFunctor_2234_ = lean_ctor_get(v_toApplicative_2232_, 0);
v_machine_2235_ = lean_ctor_get(v_state_2229_, 0);
lean_inc_ref(v_machine_2235_);
v_requestStream_2236_ = lean_ctor_get(v_state_2229_, 1);
lean_inc_ref(v_requestStream_2236_);
v_keepAliveTimeout_2237_ = lean_ctor_get(v_state_2229_, 2);
lean_inc(v_keepAliveTimeout_2237_);
v_currentTimeout_2238_ = lean_ctor_get(v_state_2229_, 3);
lean_inc(v_currentTimeout_2238_);
v_headerTimeout_2239_ = lean_ctor_get(v_state_2229_, 4);
lean_inc(v_headerTimeout_2239_);
v_response_2240_ = lean_ctor_get(v_state_2229_, 5);
lean_inc_ref(v_response_2240_);
v_respStream_2241_ = lean_ctor_get(v_state_2229_, 6);
lean_inc(v_respStream_2241_);
v_requiresData_2242_ = lean_ctor_get_uint8(v_state_2229_, sizeof(void*)*9);
v_expectData_2243_ = lean_ctor_get(v_state_2229_, 7);
lean_inc(v_expectData_2243_);
lean_dec_ref(v_state_2229_);
v_val_2244_ = lean_ctor_get(v_pendingHead_2233_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_pendingHead_2233_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2246_ = v_pendingHead_2233_;
v_isShared_2247_ = v_isSharedCheck_2266_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_val_2244_);
lean_dec(v_pendingHead_2233_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2266_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v_onRequest_2248_; lean_object* v___f_2249_; lean_object* v___x_2250_; lean_object* v___f_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___f_2255_; uint8_t v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v_onRequest_2248_ = lean_ctor_get(v_inst_2225_, 1);
lean_inc_ref(v_onRequest_2248_);
lean_dec_ref(v_inst_2225_);
v___f_2249_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2250_ = lean_box(v_requiresData_2242_);
lean_inc_ref(v_response_2240_);
lean_inc_ref(v_requestStream_2236_);
v___f_2251_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2251_, 0, v_machine_2235_);
lean_closure_set(v___f_2251_, 1, v_requestStream_2236_);
lean_closure_set(v___f_2251_, 2, v_keepAliveTimeout_2237_);
lean_closure_set(v___f_2251_, 3, v_currentTimeout_2238_);
lean_closure_set(v___f_2251_, 4, v_headerTimeout_2239_);
lean_closure_set(v___f_2251_, 5, v_response_2240_);
lean_closure_set(v___f_2251_, 6, v_respStream_2241_);
lean_closure_set(v___f_2251_, 7, v___x_2250_);
lean_closure_set(v___f_2251_, 8, v_expectData_2243_);
v___x_2252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2252_, 0, v_val_2244_);
lean_ctor_set(v___x_2252_, 1, v_requestStream_2236_);
lean_ctor_set(v___x_2252_, 2, v_extensions_2227_);
v___x_2253_ = lean_apply_3(v_onRequest_2248_, v_handler_2226_, v___x_2252_, v_connectionContext_2228_);
v___x_2254_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_toFunctor_2234_);
v___f_2255_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2255_, 0, v_toFunctor_2234_);
lean_closure_set(v___f_2255_, 1, v_response_2240_);
lean_closure_set(v___f_2255_, 2, v___x_2254_);
lean_closure_set(v___f_2255_, 3, v___f_2251_);
v___x_2256_ = 0;
v___x_2257_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2257_, 0, lean_box(0));
lean_closure_set(v___x_2257_, 1, v___x_2253_);
v___x_2258_ = lean_io_as_task(v___x_2257_, v___x_2254_);
v___x_2259_ = 1;
v___x_2260_ = lean_task_bind(v___x_2258_, v___f_2249_, v___x_2254_, v___x_2259_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2260_);
v___x_2262_ = v___x_2246_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
v___x_2264_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2254_, v___x_2256_, v___x_2263_, v___f_2255_);
return v___x_2264_;
}
}
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
lean_dec(v_pendingHead_2233_);
lean_dec_ref(v_connectionContext_2228_);
lean_dec(v_extensions_2227_);
lean_dec(v_handler_2226_);
lean_dec_ref(v_inst_2225_);
v___x_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_state_2229_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
return v___x_2268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2269_, lean_object* v_handler_2270_, lean_object* v_extensions_2271_, lean_object* v_connectionContext_2272_, lean_object* v_state_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2269_, v_handler_2270_, v_extensions_2271_, v_connectionContext_2272_, v_state_2273_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2276_, lean_object* v_inst_2277_, lean_object* v_handler_2278_, lean_object* v_extensions_2279_, lean_object* v_connectionContext_2280_, lean_object* v_state_2281_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2277_, v_handler_2278_, v_extensions_2279_, v_connectionContext_2280_, v_state_2281_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2284_, lean_object* v_inst_2285_, lean_object* v_handler_2286_, lean_object* v_extensions_2287_, lean_object* v_connectionContext_2288_, lean_object* v_state_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2284_, v_inst_2285_, v_handler_2286_, v_extensions_2287_, v_connectionContext_2288_, v_state_2289_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2292_, lean_object* v_____r_2293_){
_start:
{
lean_object* v_writer_2295_; lean_object* v_reader_2296_; lean_object* v_config_2297_; lean_object* v_events_2298_; lean_object* v_error_2299_; lean_object* v_instant_2300_; uint8_t v_keepAlive_2301_; uint8_t v_pullBodyStalled_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2329_; 
v_writer_2295_ = lean_ctor_get(v_machine_2292_, 1);
v_reader_2296_ = lean_ctor_get(v_machine_2292_, 0);
v_config_2297_ = lean_ctor_get(v_machine_2292_, 2);
v_events_2298_ = lean_ctor_get(v_machine_2292_, 3);
v_error_2299_ = lean_ctor_get(v_machine_2292_, 4);
v_instant_2300_ = lean_ctor_get(v_machine_2292_, 5);
v_keepAlive_2301_ = lean_ctor_get_uint8(v_machine_2292_, sizeof(void*)*6);
v_pullBodyStalled_2302_ = lean_ctor_get_uint8(v_machine_2292_, sizeof(void*)*6 + 1);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_machine_2292_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2304_ = v_machine_2292_;
v_isShared_2305_ = v_isSharedCheck_2329_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_instant_2300_);
lean_inc(v_error_2299_);
lean_inc(v_events_2298_);
lean_inc(v_config_2297_);
lean_inc(v_writer_2295_);
lean_inc(v_reader_2296_);
lean_dec(v_machine_2292_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2329_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v_userData_2306_; lean_object* v_outputData_2307_; lean_object* v_state_2308_; lean_object* v_knownSize_2309_; lean_object* v_messageHead_2310_; uint8_t v_sentMessage_2311_; uint8_t v_omitBody_2312_; lean_object* v_userDataBytes_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2328_; 
v_userData_2306_ = lean_ctor_get(v_writer_2295_, 0);
v_outputData_2307_ = lean_ctor_get(v_writer_2295_, 1);
v_state_2308_ = lean_ctor_get(v_writer_2295_, 2);
v_knownSize_2309_ = lean_ctor_get(v_writer_2295_, 3);
v_messageHead_2310_ = lean_ctor_get(v_writer_2295_, 4);
v_sentMessage_2311_ = lean_ctor_get_uint8(v_writer_2295_, sizeof(void*)*6);
v_omitBody_2312_ = lean_ctor_get_uint8(v_writer_2295_, sizeof(void*)*6 + 2);
v_userDataBytes_2313_ = lean_ctor_get(v_writer_2295_, 5);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_writer_2295_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2315_ = v_writer_2295_;
v_isShared_2316_ = v_isSharedCheck_2328_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_userDataBytes_2313_);
lean_inc(v_messageHead_2310_);
lean_inc(v_knownSize_2309_);
lean_inc(v_state_2308_);
lean_inc(v_outputData_2307_);
lean_inc(v_userData_2306_);
lean_dec(v_writer_2295_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2328_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
uint8_t v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = 1;
if (v_isShared_2316_ == 0)
{
v___x_2319_ = v___x_2315_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_userData_2306_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_outputData_2307_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_state_2308_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v_knownSize_2309_);
lean_ctor_set(v_reuseFailAlloc_2327_, 4, v_messageHead_2310_);
lean_ctor_set(v_reuseFailAlloc_2327_, 5, v_userDataBytes_2313_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*6, v_sentMessage_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*6 + 2, v_omitBody_2312_);
v___x_2319_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2321_; 
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*6 + 1, v___x_2317_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v___x_2319_);
v___x_2321_ = v___x_2304_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_reader_2296_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_config_2297_);
lean_ctor_set(v_reuseFailAlloc_2326_, 3, v_events_2298_);
lean_ctor_set(v_reuseFailAlloc_2326_, 4, v_error_2299_);
lean_ctor_set(v_reuseFailAlloc_2326_, 5, v_instant_2300_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, sizeof(void*)*6, v_keepAlive_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, sizeof(void*)*6 + 1, v_pullBodyStalled_2302_);
v___x_2321_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2321_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
return v___x_2325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2330_, lean_object* v_____r_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2330_, v_____r_2331_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2334_, lean_object* v_x2_2335_){
_start:
{
lean_object* v_data_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v_data_2336_ = lean_ctor_get(v_x2_2335_, 0);
v___x_2337_ = lean_byte_array_size(v_data_2336_);
v___x_2338_ = lean_nat_add(v_x1_2334_, v___x_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2339_, lean_object* v_x2_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2339_, v_x2_2340_);
lean_dec_ref(v_x2_2340_);
lean_dec(v_x1_2339_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2342_, lean_object* v_machine_2343_, lean_object* v_isClosed_2344_, lean_object* v___f_2345_, lean_object* v___f_2346_, lean_object* v_x_2347_){
_start:
{
lean_object* v___y_2350_; 
if (lean_obj_tag(v_x_2347_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v___f_2346_);
lean_dec_ref(v___f_2345_);
lean_dec_ref(v_isClosed_2344_);
lean_dec_ref(v_machine_2343_);
lean_dec(v_body_2342_);
v_a_2355_ = lean_ctor_get(v_x_2347_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_x_2347_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2357_ = v_x_2347_;
v_isShared_2358_ = v_isSharedCheck_2363_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v_x_2347_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2363_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; 
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2426_; 
v_a_2364_ = lean_ctor_get(v_x_2347_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_x_2347_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2366_ = v_x_2347_;
v_isShared_2367_ = v_isSharedCheck_2426_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v_x_2347_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2426_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
if (lean_obj_tag(v_a_2364_) == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
lean_dec_ref(v___f_2346_);
lean_dec_ref(v___f_2345_);
lean_dec_ref(v_isClosed_2344_);
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v_body_2342_);
v___x_2369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2369_, 0, v_machine_2343_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2369_);
v___x_2371_ = v___x_2366_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
return v___x_2372_;
}
}
else
{
lean_object* v_val_2374_; 
lean_del_object(v___x_2366_);
v_val_2374_ = lean_ctor_get(v_a_2364_, 0);
lean_inc(v_val_2374_);
lean_dec_ref_known(v_a_2364_, 1);
if (lean_obj_tag(v_val_2374_) == 0)
{
lean_object* v___x_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_dec_ref(v___f_2346_);
lean_dec_ref(v_machine_2343_);
v___x_2375_ = lean_unsigned_to_nat(0u);
v___x_2376_ = 0;
v___x_2377_ = lean_apply_2(v_isClosed_2344_, v_body_2342_, lean_box(0));
v___x_2378_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2375_, v___x_2376_, v___x_2377_, v___f_2345_);
return v___x_2378_;
}
else
{
lean_object* v_val_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
lean_dec_ref(v___f_2345_);
lean_dec_ref(v_isClosed_2344_);
v_val_2379_ = lean_ctor_get(v_val_2374_, 0);
lean_inc(v_val_2379_);
lean_dec_ref_known(v_val_2374_, 1);
v___x_2380_ = lean_unsigned_to_nat(1u);
v___x_2381_ = lean_mk_empty_array_with_capacity(v___x_2380_);
v___x_2382_ = lean_array_push(v___x_2381_, v_val_2379_);
v___x_2383_ = lean_array_get_size(v___x_2382_);
v___x_2384_ = lean_unsigned_to_nat(0u);
v___x_2385_ = lean_nat_dec_eq(v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v_reader_2386_; lean_object* v_writer_2387_; lean_object* v_config_2388_; lean_object* v_events_2389_; lean_object* v_error_2390_; lean_object* v_instant_2391_; uint8_t v_keepAlive_2392_; uint8_t v_pullBodyStalled_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2425_; 
v_reader_2386_ = lean_ctor_get(v_machine_2343_, 0);
v_writer_2387_ = lean_ctor_get(v_machine_2343_, 1);
v_config_2388_ = lean_ctor_get(v_machine_2343_, 2);
v_events_2389_ = lean_ctor_get(v_machine_2343_, 3);
v_error_2390_ = lean_ctor_get(v_machine_2343_, 4);
v_instant_2391_ = lean_ctor_get(v_machine_2343_, 5);
v_keepAlive_2392_ = lean_ctor_get_uint8(v_machine_2343_, sizeof(void*)*6);
v_pullBodyStalled_2393_ = lean_ctor_get_uint8(v_machine_2343_, sizeof(void*)*6 + 1);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_machine_2343_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2395_ = v_machine_2343_;
v_isShared_2396_ = v_isSharedCheck_2425_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_instant_2391_);
lean_inc(v_error_2390_);
lean_inc(v_events_2389_);
lean_inc(v_config_2388_);
lean_inc(v_writer_2387_);
lean_inc(v_reader_2386_);
lean_dec(v_machine_2343_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2425_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___y_2398_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_2421_ = lean_nat_dec_lt(v___x_2384_, v___x_2383_);
if (v___x_2421_ == 0)
{
lean_dec_ref(v___f_2346_);
v___y_2398_ = v___x_2384_;
goto v___jp_2397_;
}
else
{
size_t v___x_2422_; size_t v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = ((size_t)0ULL);
v___x_2423_ = lean_usize_of_nat(v___x_2383_);
lean_inc_ref(v___x_2382_);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2420_, v___f_2346_, v___x_2382_, v___x_2422_, v___x_2423_, v___x_2384_);
v___y_2398_ = v___x_2424_;
goto v___jp_2397_;
}
v___jp_2397_:
{
lean_object* v_userData_2399_; lean_object* v_outputData_2400_; lean_object* v_state_2401_; lean_object* v_knownSize_2402_; lean_object* v_messageHead_2403_; uint8_t v_sentMessage_2404_; uint8_t v_userClosedBody_2405_; uint8_t v_omitBody_2406_; lean_object* v_userDataBytes_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2419_; 
v_userData_2399_ = lean_ctor_get(v_writer_2387_, 0);
v_outputData_2400_ = lean_ctor_get(v_writer_2387_, 1);
v_state_2401_ = lean_ctor_get(v_writer_2387_, 2);
v_knownSize_2402_ = lean_ctor_get(v_writer_2387_, 3);
v_messageHead_2403_ = lean_ctor_get(v_writer_2387_, 4);
v_sentMessage_2404_ = lean_ctor_get_uint8(v_writer_2387_, sizeof(void*)*6);
v_userClosedBody_2405_ = lean_ctor_get_uint8(v_writer_2387_, sizeof(void*)*6 + 1);
v_omitBody_2406_ = lean_ctor_get_uint8(v_writer_2387_, sizeof(void*)*6 + 2);
v_userDataBytes_2407_ = lean_ctor_get(v_writer_2387_, 5);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_writer_2387_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2409_ = v_writer_2387_;
v_isShared_2410_ = v_isSharedCheck_2419_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_userDataBytes_2407_);
lean_inc(v_messageHead_2403_);
lean_inc(v_knownSize_2402_);
lean_inc(v_state_2401_);
lean_inc(v_outputData_2400_);
lean_inc(v_userData_2399_);
lean_dec(v_writer_2387_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2419_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2411_ = l_Array_append___redArg(v_userData_2399_, v___x_2382_);
lean_dec_ref(v___x_2382_);
v___x_2412_ = lean_nat_add(v_userDataBytes_2407_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec(v_userDataBytes_2407_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 5, v___x_2412_);
lean_ctor_set(v___x_2409_, 0, v___x_2411_);
v___x_2414_ = v___x_2409_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_outputData_2400_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v_state_2401_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v_knownSize_2402_);
lean_ctor_set(v_reuseFailAlloc_2418_, 4, v_messageHead_2403_);
lean_ctor_set(v_reuseFailAlloc_2418_, 5, v___x_2412_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*6, v_sentMessage_2404_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*6 + 1, v_userClosedBody_2405_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*6 + 2, v_omitBody_2406_);
v___x_2414_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 1, v___x_2414_);
v___x_2416_ = v___x_2395_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_reader_2386_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v_config_2388_);
lean_ctor_set(v_reuseFailAlloc_2417_, 3, v_events_2389_);
lean_ctor_set(v_reuseFailAlloc_2417_, 4, v_error_2390_);
lean_ctor_set(v_reuseFailAlloc_2417_, 5, v_instant_2391_);
lean_ctor_set_uint8(v_reuseFailAlloc_2417_, sizeof(void*)*6, v_keepAlive_2392_);
lean_ctor_set_uint8(v_reuseFailAlloc_2417_, sizeof(void*)*6 + 1, v_pullBodyStalled_2393_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
v___y_2350_ = v___x_2416_;
goto v___jp_2349_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2382_);
lean_dec_ref(v___f_2346_);
v___y_2350_ = v_machine_2343_;
goto v___jp_2349_;
}
}
}
}
}
v___jp_2349_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2351_, 0, v_body_2342_);
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___y_2350_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
return v___x_2354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2427_, lean_object* v_machine_2428_, lean_object* v_isClosed_2429_, lean_object* v___f_2430_, lean_object* v___f_2431_, lean_object* v_x_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2427_, v_machine_2428_, v_isClosed_2429_, v___f_2430_, v___f_2431_, v_x_2432_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2436_, lean_object* v_machine_2437_, lean_object* v_body_2438_){
_start:
{
lean_object* v_close_2440_; lean_object* v_isClosed_2441_; lean_object* v_tryRecv_2442_; lean_object* v___f_2443_; lean_object* v___f_2444_; lean_object* v___f_2445_; lean_object* v___f_2446_; lean_object* v___f_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_close_2440_ = lean_ctor_get(v_inst_2436_, 1);
lean_inc_ref(v_close_2440_);
v_isClosed_2441_ = lean_ctor_get(v_inst_2436_, 2);
lean_inc_ref(v_isClosed_2441_);
v_tryRecv_2442_ = lean_ctor_get(v_inst_2436_, 4);
lean_inc_ref(v_tryRecv_2442_);
lean_dec_ref(v_inst_2436_);
lean_inc_ref(v_machine_2437_);
v___f_2443_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2443_, 0, v_machine_2437_);
lean_inc_ref(v___f_2443_);
v___f_2444_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2444_, 0, v___f_2443_);
lean_inc_n(v_body_2438_, 2);
v___f_2445_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_2445_, 0, v_close_2440_);
lean_closure_set(v___f_2445_, 1, v_body_2438_);
lean_closure_set(v___f_2445_, 2, v___f_2444_);
lean_closure_set(v___f_2445_, 3, v___f_2443_);
v___f_2446_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2447_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2447_, 0, v_body_2438_);
lean_closure_set(v___f_2447_, 1, v_machine_2437_);
lean_closure_set(v___f_2447_, 2, v_isClosed_2441_);
lean_closure_set(v___f_2447_, 3, v___f_2445_);
lean_closure_set(v___f_2447_, 4, v___f_2446_);
v___x_2448_ = lean_unsigned_to_nat(0u);
v___x_2449_ = 0;
v___x_2450_ = lean_apply_2(v_tryRecv_2442_, v_body_2438_, lean_box(0));
v___x_2451_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2448_, v___x_2449_, v___x_2450_, v___f_2447_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2452_, lean_object* v_machine_2453_, lean_object* v_body_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2452_, v_machine_2453_, v_body_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2457_, lean_object* v_inst_2458_, lean_object* v_machine_2459_, lean_object* v_body_2460_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2458_, v_machine_2459_, v_body_2460_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2463_, lean_object* v_inst_2464_, lean_object* v_machine_2465_, lean_object* v_body_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2463_, v_inst_2464_, v_machine_2465_, v_body_2466_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2475_, lean_object* v_____r_2476_, lean_object* v_st_2477_){
_start:
{
lean_object* v_machine_2479_; lean_object* v_requestStream_2480_; lean_object* v_keepAliveTimeout_2481_; lean_object* v_currentTimeout_2482_; lean_object* v_headerTimeout_2483_; lean_object* v_response_2484_; lean_object* v_respStream_2485_; uint8_t v_requiresData_2486_; lean_object* v_expectData_2487_; uint8_t v_handlerDispatched_2488_; lean_object* v_pendingHead_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2570_; 
v_machine_2479_ = lean_ctor_get(v_st_2477_, 0);
v_requestStream_2480_ = lean_ctor_get(v_st_2477_, 1);
v_keepAliveTimeout_2481_ = lean_ctor_get(v_st_2477_, 2);
v_currentTimeout_2482_ = lean_ctor_get(v_st_2477_, 3);
v_headerTimeout_2483_ = lean_ctor_get(v_st_2477_, 4);
v_response_2484_ = lean_ctor_get(v_st_2477_, 5);
v_respStream_2485_ = lean_ctor_get(v_st_2477_, 6);
v_requiresData_2486_ = lean_ctor_get_uint8(v_st_2477_, sizeof(void*)*9);
v_expectData_2487_ = lean_ctor_get(v_st_2477_, 7);
v_handlerDispatched_2488_ = lean_ctor_get_uint8(v_st_2477_, sizeof(void*)*9 + 1);
v_pendingHead_2489_ = lean_ctor_get(v_st_2477_, 8);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_st_2477_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2491_ = v_st_2477_;
v_isShared_2492_ = v_isSharedCheck_2570_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_pendingHead_2489_);
lean_inc(v_expectData_2487_);
lean_inc(v_respStream_2485_);
lean_inc(v_response_2484_);
lean_inc(v_headerTimeout_2483_);
lean_inc(v_currentTimeout_2482_);
lean_inc(v_keepAliveTimeout_2481_);
lean_inc(v_requestStream_2480_);
lean_inc(v_machine_2479_);
lean_dec(v_st_2477_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2570_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___y_2494_; lean_object* v_reader_2503_; lean_object* v_state_2504_; 
v_reader_2503_ = lean_ctor_get(v_machine_2479_, 0);
lean_inc_ref(v_reader_2503_);
v_state_2504_ = lean_ctor_get(v_reader_2503_, 0);
lean_inc(v_state_2504_);
if (lean_obj_tag(v_state_2504_) == 6)
{
lean_dec_ref(v_reader_2503_);
lean_dec_ref(v_val_2475_);
v___y_2494_ = v_machine_2479_;
goto v___jp_2493_;
}
else
{
if (lean_obj_tag(v_state_2504_) == 7)
{
lean_dec_ref_known(v_state_2504_, 1);
lean_dec_ref(v_reader_2503_);
lean_dec_ref(v_val_2475_);
v___y_2494_ = v_machine_2479_;
goto v___jp_2493_;
}
else
{
lean_object* v_input_2505_; lean_object* v_writer_2506_; lean_object* v_config_2507_; lean_object* v_events_2508_; lean_object* v_error_2509_; lean_object* v_instant_2510_; uint8_t v_keepAlive_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2568_; 
v_input_2505_ = lean_ctor_get(v_reader_2503_, 1);
lean_inc_ref(v_input_2505_);
v_writer_2506_ = lean_ctor_get(v_machine_2479_, 1);
v_config_2507_ = lean_ctor_get(v_machine_2479_, 2);
v_events_2508_ = lean_ctor_get(v_machine_2479_, 3);
v_error_2509_ = lean_ctor_get(v_machine_2479_, 4);
v_instant_2510_ = lean_ctor_get(v_machine_2479_, 5);
v_keepAlive_2511_ = lean_ctor_get_uint8(v_machine_2479_, sizeof(void*)*6);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_machine_2479_);
if (v_isSharedCheck_2568_ == 0)
{
lean_object* v_unused_2569_; 
v_unused_2569_ = lean_ctor_get(v_machine_2479_, 0);
lean_dec(v_unused_2569_);
v___x_2513_ = v_machine_2479_;
v_isShared_2514_ = v_isSharedCheck_2568_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_instant_2510_);
lean_inc(v_error_2509_);
lean_inc(v_events_2508_);
lean_inc(v_config_2507_);
lean_inc(v_writer_2506_);
lean_dec(v_machine_2479_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2568_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v_messageHead_2515_; lean_object* v_messageCount_2516_; lean_object* v_bodyBytesRead_2517_; lean_object* v_headerBytesRead_2518_; uint8_t v_noMoreInput_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2565_; 
v_messageHead_2515_ = lean_ctor_get(v_reader_2503_, 2);
v_messageCount_2516_ = lean_ctor_get(v_reader_2503_, 3);
v_bodyBytesRead_2517_ = lean_ctor_get(v_reader_2503_, 4);
v_headerBytesRead_2518_ = lean_ctor_get(v_reader_2503_, 5);
v_noMoreInput_2519_ = lean_ctor_get_uint8(v_reader_2503_, sizeof(void*)*6);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_reader_2503_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; lean_object* v_unused_2567_; 
v_unused_2566_ = lean_ctor_get(v_reader_2503_, 1);
lean_dec(v_unused_2566_);
v_unused_2567_ = lean_ctor_get(v_reader_2503_, 0);
lean_dec(v_unused_2567_);
v___x_2521_ = v_reader_2503_;
v_isShared_2522_ = v_isSharedCheck_2565_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_headerBytesRead_2518_);
lean_inc(v_bodyBytesRead_2517_);
lean_inc(v_messageCount_2516_);
lean_inc(v_messageHead_2515_);
lean_dec(v_reader_2503_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2565_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v_array_2523_; lean_object* v_idx_2524_; uint8_t v___x_2525_; lean_object* v___y_2527_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v_array_2523_ = lean_ctor_get(v_input_2505_, 0);
lean_inc_ref(v_array_2523_);
v_idx_2524_ = lean_ctor_get(v_input_2505_, 1);
lean_inc(v_idx_2524_);
lean_dec_ref(v_input_2505_);
v___x_2525_ = 0;
v___x_2556_ = lean_byte_array_size(v_array_2523_);
v___x_2557_ = lean_nat_dec_le(v___x_2556_, v_idx_2524_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2558_ = l_ByteArray_extract(v_array_2523_, v_idx_2524_, v___x_2556_);
lean_dec_ref(v_array_2523_);
v___x_2559_ = lean_unsigned_to_nat(0u);
v___x_2560_ = lean_byte_array_size(v___x_2558_);
v___x_2561_ = lean_byte_array_size(v_val_2475_);
v___x_2562_ = lean_byte_array_copy_slice(v_val_2475_, v___x_2559_, v___x_2558_, v___x_2560_, v___x_2561_, v___x_2557_);
lean_dec_ref(v_val_2475_);
v___x_2563_ = l_ByteArray_mkIterator(v___x_2562_);
v___y_2527_ = v___x_2563_;
goto v___jp_2526_;
}
else
{
lean_object* v___x_2564_; 
lean_dec(v_idx_2524_);
lean_dec_ref(v_array_2523_);
v___x_2564_ = l_ByteArray_mkIterator(v_val_2475_);
v___y_2527_ = v___x_2564_;
goto v___jp_2526_;
}
v___jp_2526_:
{
lean_object* v_maxHeaderBytes_2528_; lean_object* v_maxStartLineLength_2529_; lean_object* v_maxChunkLineLength_2530_; lean_object* v_maxBodySize_2531_; lean_object* v_array_2532_; lean_object* v_idx_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v_maxHeaderBytes_2528_ = lean_ctor_get(v_config_2507_, 2);
v_maxStartLineLength_2529_ = lean_ctor_get(v_config_2507_, 5);
v_maxChunkLineLength_2530_ = lean_ctor_get(v_config_2507_, 13);
v_maxBodySize_2531_ = lean_ctor_get(v_config_2507_, 15);
v_array_2532_ = lean_ctor_get(v___y_2527_, 0);
v_idx_2533_ = lean_ctor_get(v___y_2527_, 1);
v___x_2534_ = lean_nat_add(v_maxBodySize_2531_, v_maxHeaderBytes_2528_);
v___x_2535_ = lean_nat_add(v___x_2534_, v_maxStartLineLength_2529_);
lean_dec(v___x_2534_);
v___x_2536_ = lean_nat_add(v___x_2535_, v_maxChunkLineLength_2530_);
lean_dec(v___x_2535_);
v___x_2537_ = lean_byte_array_size(v_array_2532_);
v___x_2538_ = lean_nat_sub(v___x_2537_, v_idx_2533_);
v___x_2539_ = lean_nat_dec_lt(v___x_2536_, v___x_2538_);
lean_dec(v___x_2538_);
lean_dec(v___x_2536_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2541_; 
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 1, v___y_2527_);
v___x_2541_ = v___x_2521_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_state_2504_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v___y_2527_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v_messageHead_2515_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v_messageCount_2516_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v_bodyBytesRead_2517_);
lean_ctor_set(v_reuseFailAlloc_2545_, 5, v_headerBytesRead_2518_);
lean_ctor_set_uint8(v_reuseFailAlloc_2545_, sizeof(void*)*6, v_noMoreInput_2519_);
v___x_2541_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v_machine_2543_; 
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v___x_2541_);
v_machine_2543_ = v___x_2513_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_writer_2506_);
lean_ctor_set(v_reuseFailAlloc_2544_, 2, v_config_2507_);
lean_ctor_set(v_reuseFailAlloc_2544_, 3, v_events_2508_);
lean_ctor_set(v_reuseFailAlloc_2544_, 4, v_error_2509_);
lean_ctor_set(v_reuseFailAlloc_2544_, 5, v_instant_2510_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*6, v_keepAlive_2511_);
v_machine_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_ctor_set_uint8(v_machine_2543_, sizeof(void*)*6 + 1, v___x_2525_);
v___y_2494_ = v_machine_2543_;
goto v___jp_2493_;
}
}
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2550_; 
lean_dec(v_error_2509_);
lean_dec(v_state_2504_);
v___x_2546_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2547_ = lean_array_push(v_events_2508_, v___x_2546_);
v___x_2548_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 1, v___y_2527_);
lean_ctor_set(v___x_2521_, 0, v___x_2548_);
v___x_2550_ = v___x_2521_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v___y_2527_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v_messageHead_2515_);
lean_ctor_set(v_reuseFailAlloc_2555_, 3, v_messageCount_2516_);
lean_ctor_set(v_reuseFailAlloc_2555_, 4, v_bodyBytesRead_2517_);
lean_ctor_set(v_reuseFailAlloc_2555_, 5, v_headerBytesRead_2518_);
lean_ctor_set_uint8(v_reuseFailAlloc_2555_, sizeof(void*)*6, v_noMoreInput_2519_);
v___x_2550_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2551_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 4, v___x_2551_);
lean_ctor_set(v___x_2513_, 3, v___x_2547_);
lean_ctor_set(v___x_2513_, 0, v___x_2550_);
v___x_2553_ = v___x_2513_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2550_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_writer_2506_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_config_2507_);
lean_ctor_set(v_reuseFailAlloc_2554_, 3, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2554_, 4, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2554_, 5, v_instant_2510_);
lean_ctor_set_uint8(v_reuseFailAlloc_2554_, sizeof(void*)*6, v_keepAlive_2511_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_ctor_set_uint8(v___x_2553_, sizeof(void*)*6 + 1, v___x_2525_);
v___y_2494_ = v___x_2553_;
goto v___jp_2493_;
}
}
}
}
}
}
}
}
v___jp_2493_:
{
lean_object* v___x_2496_; 
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 0, v___y_2494_);
v___x_2496_ = v___x_2491_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___y_2494_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_requestStream_2480_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v_keepAliveTimeout_2481_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v_currentTimeout_2482_);
lean_ctor_set(v_reuseFailAlloc_2502_, 4, v_headerTimeout_2483_);
lean_ctor_set(v_reuseFailAlloc_2502_, 5, v_response_2484_);
lean_ctor_set(v_reuseFailAlloc_2502_, 6, v_respStream_2485_);
lean_ctor_set(v_reuseFailAlloc_2502_, 7, v_expectData_2487_);
lean_ctor_set(v_reuseFailAlloc_2502_, 8, v_pendingHead_2489_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, sizeof(void*)*9, v_requiresData_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2502_, sizeof(void*)*9 + 1, v_handlerDispatched_2488_);
v___x_2496_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
uint8_t v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2497_ = 0;
v___x_2498_ = lean_box(v___x_2497_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2496_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2571_, lean_object* v_____r_2572_, lean_object* v_st_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2571_, v_____r_2572_, v_st_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2576_, lean_object* v_machine_2577_, lean_object* v_requestStream_2578_, lean_object* v_currentTimeout_2579_, lean_object* v_response_2580_, lean_object* v_respStream_2581_, uint8_t v_requiresData_2582_, lean_object* v_expectData_2583_, uint8_t v_handlerDispatched_2584_, lean_object* v_pendingHead_2585_, lean_object* v___f_2586_, lean_object* v_x_2587_){
_start:
{
if (lean_obj_tag(v_x_2587_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2597_; 
lean_dec_ref(v___f_2586_);
lean_dec(v_pendingHead_2585_);
lean_dec(v_expectData_2583_);
lean_dec(v_respStream_2581_);
lean_dec_ref(v_response_2580_);
lean_dec(v_currentTimeout_2579_);
lean_dec_ref(v_requestStream_2578_);
lean_dec_ref(v_machine_2577_);
v_a_2589_ = lean_ctor_get(v_x_2587_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_x_2587_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2591_ = v_x_2587_;
v_isShared_2592_ = v_isSharedCheck_2597_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v_x_2587_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2597_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; 
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v_headerTimeout_2599_; lean_object* v_second_2600_; lean_object* v_nano_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v_second_2605_; lean_object* v_nano_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v_nanos_2610_; lean_object* v___x_2611_; lean_object* v_nanos_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_a_2598_ = lean_ctor_get(v_x_2587_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v_x_2587_, 1);
v_headerTimeout_2599_ = lean_ctor_get(v_config_2576_, 6);
v_second_2600_ = lean_ctor_get(v_a_2598_, 0);
lean_inc(v_second_2600_);
v_nano_2601_ = lean_ctor_get(v_a_2598_, 1);
lean_inc(v_nano_2601_);
lean_dec(v_a_2598_);
v___x_2602_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_2603_ = lean_int_mul(v_headerTimeout_2599_, v___x_2602_);
v___x_2604_ = l_Std_Time_Duration_ofNanoseconds(v___x_2603_);
lean_dec(v___x_2603_);
v_second_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_second_2605_);
v_nano_2606_ = lean_ctor_get(v___x_2604_, 1);
lean_inc(v_nano_2606_);
lean_dec_ref(v___x_2604_);
v___x_2607_ = lean_box(0);
v___x_2608_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_2609_ = lean_int_mul(v_second_2600_, v___x_2608_);
lean_dec(v_second_2600_);
v_nanos_2610_ = lean_int_add(v___x_2609_, v_nano_2601_);
lean_dec(v_nano_2601_);
lean_dec(v___x_2609_);
v___x_2611_ = lean_int_mul(v_second_2605_, v___x_2608_);
lean_dec(v_second_2605_);
v_nanos_2612_ = lean_int_add(v___x_2611_, v_nano_2606_);
lean_dec(v_nano_2606_);
lean_dec(v___x_2611_);
v___x_2613_ = lean_int_add(v_nanos_2610_, v_nanos_2612_);
lean_dec(v_nanos_2612_);
lean_dec(v_nanos_2610_);
v___x_2614_ = l_Std_Time_Duration_ofNanoseconds(v___x_2613_);
lean_dec(v___x_2613_);
v___x_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2616_, 0, v_machine_2577_);
lean_ctor_set(v___x_2616_, 1, v_requestStream_2578_);
lean_ctor_set(v___x_2616_, 2, v___x_2607_);
lean_ctor_set(v___x_2616_, 3, v_currentTimeout_2579_);
lean_ctor_set(v___x_2616_, 4, v___x_2615_);
lean_ctor_set(v___x_2616_, 5, v_response_2580_);
lean_ctor_set(v___x_2616_, 6, v_respStream_2581_);
lean_ctor_set(v___x_2616_, 7, v_expectData_2583_);
lean_ctor_set(v___x_2616_, 8, v_pendingHead_2585_);
lean_ctor_set_uint8(v___x_2616_, sizeof(void*)*9, v_requiresData_2582_);
lean_ctor_set_uint8(v___x_2616_, sizeof(void*)*9 + 1, v_handlerDispatched_2584_);
v___x_2617_ = lean_box(0);
v___x_2618_ = lean_apply_3(v___f_2586_, v___x_2617_, v___x_2616_, lean_box(0));
return v___x_2618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2619_, lean_object* v_machine_2620_, lean_object* v_requestStream_2621_, lean_object* v_currentTimeout_2622_, lean_object* v_response_2623_, lean_object* v_respStream_2624_, lean_object* v_requiresData_2625_, lean_object* v_expectData_2626_, lean_object* v_handlerDispatched_2627_, lean_object* v_pendingHead_2628_, lean_object* v___f_2629_, lean_object* v_x_2630_, lean_object* v___y_2631_){
_start:
{
uint8_t v_requiresData_boxed_2632_; uint8_t v_handlerDispatched_boxed_2633_; lean_object* v_res_2634_; 
v_requiresData_boxed_2632_ = lean_unbox(v_requiresData_2625_);
v_handlerDispatched_boxed_2633_ = lean_unbox(v_handlerDispatched_2627_);
v_res_2634_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2619_, v_machine_2620_, v_requestStream_2621_, v_currentTimeout_2622_, v_response_2623_, v_respStream_2624_, v_requiresData_boxed_2632_, v_expectData_2626_, v_handlerDispatched_boxed_2633_, v_pendingHead_2628_, v___f_2629_, v_x_2630_);
lean_dec_ref(v_config_2619_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2635_, lean_object* v_requestStream_2636_, lean_object* v_keepAliveTimeout_2637_, lean_object* v_currentTimeout_2638_, lean_object* v_headerTimeout_2639_, lean_object* v_response_2640_, uint8_t v_requiresData_2641_, lean_object* v_expectData_2642_, uint8_t v_handlerDispatched_2643_, lean_object* v_pendingHead_2644_, lean_object* v_____r_2645_){
_start:
{
lean_object* v_writer_2647_; lean_object* v_reader_2648_; lean_object* v_config_2649_; lean_object* v_events_2650_; lean_object* v_error_2651_; lean_object* v_instant_2652_; uint8_t v_keepAlive_2653_; uint8_t v_pullBodyStalled_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2684_; 
v_writer_2647_ = lean_ctor_get(v_machine_2635_, 1);
v_reader_2648_ = lean_ctor_get(v_machine_2635_, 0);
v_config_2649_ = lean_ctor_get(v_machine_2635_, 2);
v_events_2650_ = lean_ctor_get(v_machine_2635_, 3);
v_error_2651_ = lean_ctor_get(v_machine_2635_, 4);
v_instant_2652_ = lean_ctor_get(v_machine_2635_, 5);
v_keepAlive_2653_ = lean_ctor_get_uint8(v_machine_2635_, sizeof(void*)*6);
v_pullBodyStalled_2654_ = lean_ctor_get_uint8(v_machine_2635_, sizeof(void*)*6 + 1);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_machine_2635_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2656_ = v_machine_2635_;
v_isShared_2657_ = v_isSharedCheck_2684_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_instant_2652_);
lean_inc(v_error_2651_);
lean_inc(v_events_2650_);
lean_inc(v_config_2649_);
lean_inc(v_writer_2647_);
lean_inc(v_reader_2648_);
lean_dec(v_machine_2635_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2684_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_userData_2658_; lean_object* v_outputData_2659_; lean_object* v_state_2660_; lean_object* v_knownSize_2661_; lean_object* v_messageHead_2662_; uint8_t v_sentMessage_2663_; uint8_t v_omitBody_2664_; lean_object* v_userDataBytes_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2683_; 
v_userData_2658_ = lean_ctor_get(v_writer_2647_, 0);
v_outputData_2659_ = lean_ctor_get(v_writer_2647_, 1);
v_state_2660_ = lean_ctor_get(v_writer_2647_, 2);
v_knownSize_2661_ = lean_ctor_get(v_writer_2647_, 3);
v_messageHead_2662_ = lean_ctor_get(v_writer_2647_, 4);
v_sentMessage_2663_ = lean_ctor_get_uint8(v_writer_2647_, sizeof(void*)*6);
v_omitBody_2664_ = lean_ctor_get_uint8(v_writer_2647_, sizeof(void*)*6 + 2);
v_userDataBytes_2665_ = lean_ctor_get(v_writer_2647_, 5);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_writer_2647_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2667_ = v_writer_2647_;
v_isShared_2668_ = v_isSharedCheck_2683_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_userDataBytes_2665_);
lean_inc(v_messageHead_2662_);
lean_inc(v_knownSize_2661_);
lean_inc(v_state_2660_);
lean_inc(v_outputData_2659_);
lean_inc(v_userData_2658_);
lean_dec(v_writer_2647_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2683_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
uint8_t v___x_2669_; lean_object* v___x_2671_; 
v___x_2669_ = 1;
if (v_isShared_2668_ == 0)
{
v___x_2671_ = v___x_2667_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_userData_2658_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_outputData_2659_);
lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_state_2660_);
lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_knownSize_2661_);
lean_ctor_set(v_reuseFailAlloc_2682_, 4, v_messageHead_2662_);
lean_ctor_set(v_reuseFailAlloc_2682_, 5, v_userDataBytes_2665_);
lean_ctor_set_uint8(v_reuseFailAlloc_2682_, sizeof(void*)*6, v_sentMessage_2663_);
lean_ctor_set_uint8(v_reuseFailAlloc_2682_, sizeof(void*)*6 + 2, v_omitBody_2664_);
v___x_2671_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2673_; 
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*6 + 1, v___x_2669_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 1, v___x_2671_);
v___x_2673_ = v___x_2656_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_reader_2648_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2681_, 2, v_config_2649_);
lean_ctor_set(v_reuseFailAlloc_2681_, 3, v_events_2650_);
lean_ctor_set(v_reuseFailAlloc_2681_, 4, v_error_2651_);
lean_ctor_set(v_reuseFailAlloc_2681_, 5, v_instant_2652_);
lean_ctor_set_uint8(v_reuseFailAlloc_2681_, sizeof(void*)*6, v_keepAlive_2653_);
lean_ctor_set_uint8(v_reuseFailAlloc_2681_, sizeof(void*)*6 + 1, v_pullBodyStalled_2654_);
v___x_2673_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2674_ = lean_box(0);
v___x_2675_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2675_, 0, v___x_2673_);
lean_ctor_set(v___x_2675_, 1, v_requestStream_2636_);
lean_ctor_set(v___x_2675_, 2, v_keepAliveTimeout_2637_);
lean_ctor_set(v___x_2675_, 3, v_currentTimeout_2638_);
lean_ctor_set(v___x_2675_, 4, v_headerTimeout_2639_);
lean_ctor_set(v___x_2675_, 5, v_response_2640_);
lean_ctor_set(v___x_2675_, 6, v___x_2674_);
lean_ctor_set(v___x_2675_, 7, v_expectData_2642_);
lean_ctor_set(v___x_2675_, 8, v_pendingHead_2644_);
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*9, v_requiresData_2641_);
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*9 + 1, v_handlerDispatched_2643_);
v___x_2676_ = 0;
v___x_2677_ = lean_box(v___x_2676_);
v___x_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2675_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
v___x_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
return v___x_2680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2685_, lean_object* v_requestStream_2686_, lean_object* v_keepAliveTimeout_2687_, lean_object* v_currentTimeout_2688_, lean_object* v_headerTimeout_2689_, lean_object* v_response_2690_, lean_object* v_requiresData_2691_, lean_object* v_expectData_2692_, lean_object* v_handlerDispatched_2693_, lean_object* v_pendingHead_2694_, lean_object* v_____r_2695_, lean_object* v___y_2696_){
_start:
{
uint8_t v_requiresData_boxed_2697_; uint8_t v_handlerDispatched_boxed_2698_; lean_object* v_res_2699_; 
v_requiresData_boxed_2697_ = lean_unbox(v_requiresData_2691_);
v_handlerDispatched_boxed_2698_ = lean_unbox(v_handlerDispatched_2693_);
v_res_2699_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2685_, v_requestStream_2686_, v_keepAliveTimeout_2687_, v_currentTimeout_2688_, v_headerTimeout_2689_, v_response_2690_, v_requiresData_boxed_2697_, v_expectData_2692_, v_handlerDispatched_boxed_2698_, v_pendingHead_2694_, v_____r_2695_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2700_, lean_object* v_x_2701_){
_start:
{
if (lean_obj_tag(v_x_2701_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v___f_2700_);
v_a_2703_ = lean_ctor_get(v_x_2701_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_x_2701_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2705_ = v_x_2701_;
v_isShared_2706_ = v_isSharedCheck_2711_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v_x_2701_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2711_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2709_; 
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2713_; 
v_a_2712_ = lean_ctor_get(v_x_2701_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v_x_2701_, 1);
v___x_2713_ = lean_apply_2(v___f_2700_, v_a_2712_, lean_box(0));
return v___x_2713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2714_, lean_object* v_x_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2714_, v_x_2715_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2718_, lean_object* v_val_2719_, lean_object* v___f_2720_, lean_object* v___f_2721_, lean_object* v_x_2722_){
_start:
{
if (lean_obj_tag(v_x_2722_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2732_; 
lean_dec_ref(v___f_2721_);
lean_dec_ref(v___f_2720_);
lean_dec(v_val_2719_);
lean_dec_ref(v_close_2718_);
v_a_2724_ = lean_ctor_get(v_x_2722_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_x_2722_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2726_ = v_x_2722_;
v_isShared_2727_ = v_isSharedCheck_2732_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v_x_2722_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2732_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_object* v___x_2730_; 
v___x_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
return v___x_2730_;
}
}
}
else
{
lean_object* v_a_2733_; uint8_t v___x_2734_; 
v_a_2733_ = lean_ctor_get(v_x_2722_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v_x_2722_, 1);
v___x_2734_ = lean_unbox(v_a_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; lean_object* v___x_2738_; 
lean_dec_ref(v___f_2721_);
v___x_2735_ = lean_unsigned_to_nat(0u);
v___x_2736_ = lean_apply_2(v_close_2718_, v_val_2719_, lean_box(0));
v___x_2737_ = lean_unbox(v_a_2733_);
lean_dec(v_a_2733_);
v___x_2738_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2735_, v___x_2737_, v___x_2736_, v___f_2720_);
return v___x_2738_;
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_dec(v_a_2733_);
lean_dec_ref(v___f_2720_);
lean_dec(v_val_2719_);
lean_dec_ref(v_close_2718_);
v___x_2739_ = lean_box(0);
v___x_2740_ = lean_apply_2(v___f_2721_, v___x_2739_, lean_box(0));
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2741_, lean_object* v_val_2742_, lean_object* v___f_2743_, lean_object* v___f_2744_, lean_object* v_x_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2741_, v_val_2742_, v___f_2743_, v___f_2744_, v_x_2745_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_inst_2748_, lean_object* v_handler_2749_, lean_object* v_x_2750_){
_start:
{
if (lean_obj_tag(v_x_2750_) == 0)
{
lean_object* v_a_2752_; lean_object* v_onFailure_2753_; lean_object* v___x_2754_; 
v_a_2752_ = lean_ctor_get(v_x_2750_, 0);
lean_inc(v_a_2752_);
lean_dec_ref_known(v_x_2750_, 1);
v_onFailure_2753_ = lean_ctor_get(v_inst_2748_, 2);
lean_inc_ref(v_onFailure_2753_);
lean_dec_ref(v_inst_2748_);
v___x_2754_ = lean_apply_3(v_onFailure_2753_, v_handler_2749_, v_a_2752_, lean_box(0));
return v___x_2754_;
}
else
{
lean_object* v___x_2755_; 
lean_dec(v_handler_2749_);
lean_dec_ref(v_inst_2748_);
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v_x_2750_);
return v___x_2755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_inst_2756_, lean_object* v_handler_2757_, lean_object* v_x_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_inst_2756_, v_handler_2757_, v_x_2758_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object* v_st_2761_, lean_object* v_____r_2762_){
_start:
{
uint8_t v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2764_ = 0;
v___x_2765_ = lean_box(v___x_2764_);
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v_st_2761_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_st_2769_, lean_object* v_____r_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_2769_, v_____r_2770_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2773_, lean_object* v___f_2774_, lean_object* v___f_2775_, lean_object* v_x_2776_){
_start:
{
if (lean_obj_tag(v_x_2776_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2786_; 
lean_dec_ref(v___f_2775_);
lean_dec_ref(v___f_2774_);
lean_dec_ref(v_requestStream_2773_);
v_a_2778_ = lean_ctor_get(v_x_2776_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_x_2776_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2780_ = v_x_2776_;
v_isShared_2781_ = v_isSharedCheck_2786_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v_x_2776_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2786_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
return v___x_2784_;
}
}
}
else
{
lean_object* v_a_2787_; uint8_t v___x_2788_; 
v_a_2787_ = lean_ctor_get(v_x_2776_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v_x_2776_, 1);
v___x_2788_ = lean_unbox(v_a_2787_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; lean_object* v___x_2792_; 
lean_dec_ref(v___f_2775_);
v___x_2789_ = lean_unsigned_to_nat(0u);
v___x_2790_ = l_Std_Http_Body_Stream_close(v_requestStream_2773_);
v___x_2791_ = lean_unbox(v_a_2787_);
lean_dec(v_a_2787_);
v___x_2792_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2789_, v___x_2791_, v___x_2790_, v___f_2774_);
return v___x_2792_;
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec(v_a_2787_);
lean_dec_ref(v___f_2774_);
lean_dec_ref(v_requestStream_2773_);
v___x_2793_ = lean_box(0);
v___x_2794_ = lean_apply_2(v___f_2775_, v___x_2793_, lean_box(0));
return v___x_2794_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2795_, lean_object* v___f_2796_, lean_object* v___f_2797_, lean_object* v_x_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2795_, v___f_2796_, v___f_2797_, v_x_2798_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(uint8_t v_final_2801_, lean_object* v___f_2802_, lean_object* v___f_2803_, lean_object* v_requestStream_2804_, lean_object* v___f_2805_, lean_object* v_x_2806_){
_start:
{
if (lean_obj_tag(v_x_2806_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2816_; 
lean_dec_ref(v___f_2805_);
lean_dec_ref(v_requestStream_2804_);
lean_dec_ref(v___f_2803_);
lean_dec_ref(v___f_2802_);
v_a_2808_ = lean_ctor_get(v_x_2806_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_x_2806_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2810_ = v_x_2806_;
v_isShared_2811_ = v_isSharedCheck_2816_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v_x_2806_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2816_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
return v___x_2814_;
}
}
}
else
{
lean_dec_ref_known(v_x_2806_, 1);
if (v_final_2801_ == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec_ref(v___f_2805_);
lean_dec_ref(v_requestStream_2804_);
lean_dec_ref(v___f_2803_);
v___x_2817_ = lean_box(0);
v___x_2818_ = lean_apply_2(v___f_2802_, v___x_2817_, lean_box(0));
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; uint8_t v___x_2820_; lean_object* v___x_2821_; lean_object* v___f_2822_; lean_object* v___f_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_6678__overap_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec_ref(v___f_2802_);
v___x_2819_ = lean_unsigned_to_nat(0u);
v___x_2820_ = 0;
v___x_2821_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2822_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2823_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2824_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2825_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2825_, 0, lean_box(0));
lean_closure_set(v___x_2825_, 1, lean_box(0));
lean_closure_set(v___x_2825_, 2, v___x_2821_);
lean_closure_set(v___x_2825_, 3, lean_box(0));
lean_closure_set(v___x_2825_, 4, lean_box(0));
lean_closure_set(v___x_2825_, 5, v___x_2824_);
lean_closure_set(v___x_2825_, 6, v___f_2803_);
v___x_6678__overap_2826_ = l_Std_Mutex_atomically___redArg(v___x_2821_, v___f_2822_, v___f_2823_, v_requestStream_2804_, v___x_2825_);
v___x_2827_ = lean_apply_1(v___x_6678__overap_2826_, lean_box(0));
v___x_2828_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2819_, v___x_2820_, v___x_2827_, v___f_2805_);
return v___x_2828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_final_2829_, lean_object* v___f_2830_, lean_object* v___f_2831_, lean_object* v_requestStream_2832_, lean_object* v___f_2833_, lean_object* v_x_2834_, lean_object* v___y_2835_){
_start:
{
uint8_t v_final_boxed_2836_; lean_object* v_res_2837_; 
v_final_boxed_2836_ = lean_unbox(v_final_2829_);
v_res_2837_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_final_boxed_2836_, v___f_2830_, v___f_2831_, v_requestStream_2832_, v___f_2833_, v_x_2834_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_2838_, lean_object* v_x_2839_){
_start:
{
if (lean_obj_tag(v_x_2839_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2849_; 
lean_dec_ref(v_state_2838_);
v_a_2841_ = lean_ctor_get(v_x_2839_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_x_2839_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2843_ = v_x_2839_;
v_isShared_2844_ = v_isSharedCheck_2849_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v_x_2839_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2849_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2847_; 
v___x_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
return v___x_2847_;
}
}
}
else
{
lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2879_; 
v_isSharedCheck_2879_ = !lean_is_exclusive(v_x_2839_);
if (v_isSharedCheck_2879_ == 0)
{
lean_object* v_unused_2880_; 
v_unused_2880_ = lean_ctor_get(v_x_2839_, 0);
lean_dec(v_unused_2880_);
v___x_2851_ = v_x_2839_;
v_isShared_2852_ = v_isSharedCheck_2879_;
goto v_resetjp_2850_;
}
else
{
lean_dec(v_x_2839_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2879_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v_machine_2853_; lean_object* v_requestStream_2854_; lean_object* v_keepAliveTimeout_2855_; lean_object* v_currentTimeout_2856_; lean_object* v_headerTimeout_2857_; lean_object* v_response_2858_; lean_object* v_respStream_2859_; uint8_t v_requiresData_2860_; lean_object* v_expectData_2861_; lean_object* v_pendingHead_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2878_; 
v_machine_2853_ = lean_ctor_get(v_state_2838_, 0);
v_requestStream_2854_ = lean_ctor_get(v_state_2838_, 1);
v_keepAliveTimeout_2855_ = lean_ctor_get(v_state_2838_, 2);
v_currentTimeout_2856_ = lean_ctor_get(v_state_2838_, 3);
v_headerTimeout_2857_ = lean_ctor_get(v_state_2838_, 4);
v_response_2858_ = lean_ctor_get(v_state_2838_, 5);
v_respStream_2859_ = lean_ctor_get(v_state_2838_, 6);
v_requiresData_2860_ = lean_ctor_get_uint8(v_state_2838_, sizeof(void*)*9);
v_expectData_2861_ = lean_ctor_get(v_state_2838_, 7);
v_pendingHead_2862_ = lean_ctor_get(v_state_2838_, 8);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_state_2838_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2864_ = v_state_2838_;
v_isShared_2865_ = v_isSharedCheck_2878_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_pendingHead_2862_);
lean_inc(v_expectData_2861_);
lean_inc(v_respStream_2859_);
lean_inc(v_response_2858_);
lean_inc(v_headerTimeout_2857_);
lean_inc(v_currentTimeout_2856_);
lean_inc(v_keepAliveTimeout_2855_);
lean_inc(v_requestStream_2854_);
lean_inc(v_machine_2853_);
lean_dec(v_state_2838_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2878_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; lean_object* v___x_2870_; 
v___x_2866_ = lean_box(52);
v___x_2867_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_2853_, v___x_2866_);
v___x_2868_ = 0;
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2867_);
v___x_2870_ = v___x_2864_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_requestStream_2854_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_keepAliveTimeout_2855_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v_currentTimeout_2856_);
lean_ctor_set(v_reuseFailAlloc_2877_, 4, v_headerTimeout_2857_);
lean_ctor_set(v_reuseFailAlloc_2877_, 5, v_response_2858_);
lean_ctor_set(v_reuseFailAlloc_2877_, 6, v_respStream_2859_);
lean_ctor_set(v_reuseFailAlloc_2877_, 7, v_expectData_2861_);
lean_ctor_set(v_reuseFailAlloc_2877_, 8, v_pendingHead_2862_);
lean_ctor_set_uint8(v_reuseFailAlloc_2877_, sizeof(void*)*9, v_requiresData_2860_);
v___x_2870_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
lean_ctor_set_uint8(v___x_2870_, sizeof(void*)*9 + 1, v___x_2868_);
v___x_2871_ = lean_box(v___x_2868_);
v___x_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2870_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2872_);
v___x_2874_ = v___x_2851_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2875_; 
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
return v___x_2875_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_2881_, lean_object* v_x_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_2881_, v_x_2882_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_2885_, lean_object* v_requestStream_2886_, lean_object* v_keepAliveTimeout_2887_, lean_object* v_currentTimeout_2888_, lean_object* v_headerTimeout_2889_, lean_object* v_response_2890_, lean_object* v_respStream_2891_, uint8_t v_requiresData_2892_, lean_object* v_expectData_2893_, lean_object* v_pendingHead_2894_, lean_object* v_____r_2895_){
_start:
{
uint8_t v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2897_ = 0;
v___x_2898_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2898_, 0, v_machine_2885_);
lean_ctor_set(v___x_2898_, 1, v_requestStream_2886_);
lean_ctor_set(v___x_2898_, 2, v_keepAliveTimeout_2887_);
lean_ctor_set(v___x_2898_, 3, v_currentTimeout_2888_);
lean_ctor_set(v___x_2898_, 4, v_headerTimeout_2889_);
lean_ctor_set(v___x_2898_, 5, v_response_2890_);
lean_ctor_set(v___x_2898_, 6, v_respStream_2891_);
lean_ctor_set(v___x_2898_, 7, v_expectData_2893_);
lean_ctor_set(v___x_2898_, 8, v_pendingHead_2894_);
lean_ctor_set_uint8(v___x_2898_, sizeof(void*)*9, v_requiresData_2892_);
lean_ctor_set_uint8(v___x_2898_, sizeof(void*)*9 + 1, v___x_2897_);
v___x_2899_ = lean_box(v___x_2897_);
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_2903_, lean_object* v_requestStream_2904_, lean_object* v_keepAliveTimeout_2905_, lean_object* v_currentTimeout_2906_, lean_object* v_headerTimeout_2907_, lean_object* v_response_2908_, lean_object* v_respStream_2909_, lean_object* v_requiresData_2910_, lean_object* v_expectData_2911_, lean_object* v_pendingHead_2912_, lean_object* v_____r_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v_requiresData_boxed_2915_; lean_object* v_res_2916_; 
v_requiresData_boxed_2915_ = lean_unbox(v_requiresData_2910_);
v_res_2916_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_2903_, v_requestStream_2904_, v_keepAliveTimeout_2905_, v_currentTimeout_2906_, v_headerTimeout_2907_, v_response_2908_, v_respStream_2909_, v_requiresData_boxed_2915_, v_expectData_2911_, v_pendingHead_2912_, v_____r_2913_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_2917_, lean_object* v_body_2918_, lean_object* v___f_2919_, lean_object* v___f_2920_, lean_object* v_x_2921_){
_start:
{
if (lean_obj_tag(v_x_2921_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2931_; 
lean_dec_ref(v___f_2920_);
lean_dec_ref(v___f_2919_);
lean_dec(v_body_2918_);
lean_dec_ref(v_close_2917_);
v_a_2923_ = lean_ctor_get(v_x_2921_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_x_2921_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2925_ = v_x_2921_;
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v_x_2921_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2931_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
return v___x_2929_;
}
}
}
else
{
lean_object* v_a_2932_; uint8_t v___x_2933_; 
v_a_2932_ = lean_ctor_get(v_x_2921_, 0);
lean_inc(v_a_2932_);
lean_dec_ref_known(v_x_2921_, 1);
v___x_2933_ = lean_unbox(v_a_2932_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; lean_object* v___x_2937_; 
lean_dec_ref(v___f_2920_);
v___x_2934_ = lean_unsigned_to_nat(0u);
v___x_2935_ = lean_apply_2(v_close_2917_, v_body_2918_, lean_box(0));
v___x_2936_ = lean_unbox(v_a_2932_);
lean_dec(v_a_2932_);
v___x_2937_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2934_, v___x_2936_, v___x_2935_, v___f_2919_);
return v___x_2937_;
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_dec(v_a_2932_);
lean_dec_ref(v___f_2919_);
lean_dec(v_body_2918_);
lean_dec_ref(v_close_2917_);
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_apply_2(v___f_2920_, v___x_2938_, lean_box(0));
return v___x_2939_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_2940_, lean_object* v_body_2941_, lean_object* v___f_2942_, lean_object* v___f_2943_, lean_object* v_x_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_2940_, v_body_2941_, v___f_2942_, v___f_2943_, v_x_2944_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_2947_, lean_object* v_keepAliveTimeout_2948_, lean_object* v_currentTimeout_2949_, lean_object* v_headerTimeout_2950_, lean_object* v_response_2951_, uint8_t v_requiresData_2952_, lean_object* v_expectData_2953_, uint8_t v___x_2954_, lean_object* v_pendingHead_2955_, lean_object* v_____x_2956_){
_start:
{
lean_object* v_snd_2958_; lean_object* v_fst_2959_; lean_object* v_fst_2960_; lean_object* v_snd_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2971_; 
v_snd_2958_ = lean_ctor_get(v_____x_2956_, 1);
lean_inc(v_snd_2958_);
v_fst_2959_ = lean_ctor_get(v_____x_2956_, 0);
lean_inc(v_fst_2959_);
lean_dec_ref(v_____x_2956_);
v_fst_2960_ = lean_ctor_get(v_snd_2958_, 0);
v_snd_2961_ = lean_ctor_get(v_snd_2958_, 1);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_snd_2958_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2963_ = v_snd_2958_;
v_isShared_2964_ = v_isSharedCheck_2971_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_snd_2961_);
lean_inc(v_fst_2960_);
lean_dec(v_snd_2958_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2971_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2965_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2965_, 0, v_fst_2959_);
lean_ctor_set(v___x_2965_, 1, v_requestStream_2947_);
lean_ctor_set(v___x_2965_, 2, v_keepAliveTimeout_2948_);
lean_ctor_set(v___x_2965_, 3, v_currentTimeout_2949_);
lean_ctor_set(v___x_2965_, 4, v_headerTimeout_2950_);
lean_ctor_set(v___x_2965_, 5, v_response_2951_);
lean_ctor_set(v___x_2965_, 6, v_fst_2960_);
lean_ctor_set(v___x_2965_, 7, v_expectData_2953_);
lean_ctor_set(v___x_2965_, 8, v_pendingHead_2955_);
lean_ctor_set_uint8(v___x_2965_, sizeof(void*)*9, v_requiresData_2952_);
lean_ctor_set_uint8(v___x_2965_, sizeof(void*)*9 + 1, v___x_2954_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2965_);
v___x_2967_ = v___x_2963_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_snd_2961_);
v___x_2967_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
v___x_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
return v___x_2969_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_2972_, lean_object* v_keepAliveTimeout_2973_, lean_object* v_currentTimeout_2974_, lean_object* v_headerTimeout_2975_, lean_object* v_response_2976_, lean_object* v_requiresData_2977_, lean_object* v_expectData_2978_, lean_object* v___x_2979_, lean_object* v_pendingHead_2980_, lean_object* v_____x_2981_, lean_object* v___y_2982_){
_start:
{
uint8_t v_requiresData_boxed_2983_; uint8_t v___x_7488__boxed_2984_; lean_object* v_res_2985_; 
v_requiresData_boxed_2983_ = lean_unbox(v_requiresData_2977_);
v___x_7488__boxed_2984_ = lean_unbox(v___x_2979_);
v_res_2985_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_2972_, v_keepAliveTimeout_2973_, v_currentTimeout_2974_, v_headerTimeout_2975_, v_response_2976_, v_requiresData_boxed_2983_, v_expectData_2978_, v___x_7488__boxed_2984_, v_pendingHead_2980_, v_____x_2981_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_2986_, lean_object* v_x_2987_){
_start:
{
if (lean_obj_tag(v_x_2987_) == 0)
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2997_; 
lean_dec_ref(v___f_2986_);
v_a_2989_ = lean_ctor_get(v_x_2987_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_x_2987_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2991_ = v_x_2987_;
v_isShared_2992_ = v_isSharedCheck_2997_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v_x_2987_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2997_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; 
v___x_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
return v___x_2995_;
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_2999_; 
v_a_2998_ = lean_ctor_get(v_x_2987_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v_x_2987_, 1);
v___x_2999_ = lean_apply_2(v___f_2986_, v_a_2998_, lean_box(0));
return v___x_2999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_3000_, lean_object* v_x_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_3000_, v_x_3001_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_3004_, lean_object* v_x_3005_){
_start:
{
if (lean_obj_tag(v_x_3005_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3015_; 
v_a_3007_ = lean_ctor_get(v_x_3005_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_x_3005_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3009_ = v_x_3005_;
v_isShared_3010_ = v_isSharedCheck_3015_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v_x_3005_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3015_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; 
v___x_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
return v___x_3013_;
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3035_; 
v_a_3016_ = lean_ctor_get(v_x_3005_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_x_3005_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3018_ = v_x_3005_;
v_isShared_3019_ = v_isSharedCheck_3035_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v_x_3005_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3035_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v_fst_3020_; lean_object* v_snd_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3034_; 
v_fst_3020_ = lean_ctor_get(v_a_3016_, 0);
v_snd_3021_ = lean_ctor_get(v_a_3016_, 1);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_a_3016_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3023_ = v_a_3016_;
v_isShared_3024_ = v_isSharedCheck_3034_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_snd_3021_);
lean_inc(v_fst_3020_);
lean_dec(v_a_3016_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3034_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3025_; lean_object* v___x_3027_; 
v___x_3025_ = lean_box(v___x_3004_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v___x_3025_);
lean_ctor_set(v___x_3023_, 0, v_snd_3021_);
v___x_3027_ = v___x_3023_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_snd_3021_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___x_3025_);
v___x_3027_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3028_, 0, v_fst_3020_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v___x_3028_);
v___x_3030_ = v___x_3018_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
return v___x_3031_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3036_, lean_object* v_x_3037_, lean_object* v___y_3038_){
_start:
{
uint8_t v___x_7556__boxed_3039_; lean_object* v_res_3040_; 
v___x_7556__boxed_3039_ = lean_unbox(v___x_3036_);
v_res_3040_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7556__boxed_3039_, v_x_3037_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_snd_3041_, uint8_t v___x_3042_, lean_object* v_fst_3043_, lean_object* v_x_3044_){
_start:
{
if (lean_obj_tag(v_x_3044_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3054_; 
lean_dec_ref(v_fst_3043_);
lean_dec(v_snd_3041_);
v_a_3046_ = lean_ctor_get(v_x_3044_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_x_3044_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3048_ = v_x_3044_;
v_isShared_3049_ = v_isSharedCheck_3054_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v_x_3044_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3054_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
return v___x_3052_;
}
}
}
else
{
lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3065_; 
v_isSharedCheck_3065_ = !lean_is_exclusive(v_x_3044_);
if (v_isSharedCheck_3065_ == 0)
{
lean_object* v_unused_3066_; 
v_unused_3066_ = lean_ctor_get(v_x_3044_, 0);
lean_dec(v_unused_3066_);
v___x_3056_ = v_x_3044_;
v_isShared_3057_ = v_isSharedCheck_3065_;
goto v_resetjp_3055_;
}
else
{
lean_dec(v_x_3044_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3065_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3058_ = lean_box(v___x_3042_);
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v_snd_3041_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v___x_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3060_, 0, v_fst_3043_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v___x_3060_);
v___x_3062_ = v___x_3056_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3063_; 
v___x_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
return v___x_3063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_snd_3067_, lean_object* v___x_3068_, lean_object* v_fst_3069_, lean_object* v_x_3070_, lean_object* v___y_3071_){
_start:
{
uint8_t v___x_7624__boxed_3072_; lean_object* v_res_3073_; 
v___x_7624__boxed_3072_ = lean_unbox(v___x_3068_);
v_res_3073_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3067_, v___x_7624__boxed_3072_, v_fst_3069_, v_x_3070_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object* v_inst_3074_, lean_object* v_handler_3075_, uint8_t v___x_3076_, lean_object* v___f_3077_, lean_object* v_x_3078_){
_start:
{
if (lean_obj_tag(v_x_3078_) == 0)
{
lean_object* v_a_3080_; lean_object* v_onFailure_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_a_3080_ = lean_ctor_get(v_x_3078_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v_x_3078_, 1);
v_onFailure_3081_ = lean_ctor_get(v_inst_3074_, 2);
lean_inc_ref(v_onFailure_3081_);
lean_dec_ref(v_inst_3074_);
v___x_3082_ = lean_unsigned_to_nat(0u);
v___x_3083_ = lean_apply_3(v_onFailure_3081_, v_handler_3075_, v_a_3080_, lean_box(0));
v___x_3084_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3082_, v___x_3076_, v___x_3083_, v___f_3077_);
return v___x_3084_;
}
else
{
lean_object* v___x_3085_; 
lean_dec_ref(v___f_3077_);
lean_dec(v_handler_3075_);
lean_dec_ref(v_inst_3074_);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v_x_3078_);
return v___x_3085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v_inst_3086_, lean_object* v_handler_3087_, lean_object* v___x_3088_, lean_object* v___f_3089_, lean_object* v_x_3090_, lean_object* v___y_3091_){
_start:
{
uint8_t v___x_7682__boxed_3092_; lean_object* v_res_3093_; 
v___x_7682__boxed_3092_ = lean_unbox(v___x_3088_);
v_res_3093_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3086_, v_handler_3087_, v___x_7682__boxed_3092_, v___f_3089_, v_x_3090_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t v___x_3094_, lean_object* v___f_3095_, uint8_t v___x_3096_, lean_object* v_inst_3097_, lean_object* v_handler_3098_, lean_object* v_inst_3099_, lean_object* v___f_3100_, lean_object* v___f_3101_, lean_object* v_x_3102_){
_start:
{
if (lean_obj_tag(v_x_3102_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3112_; 
lean_dec_ref(v___f_3101_);
lean_dec_ref(v___f_3100_);
lean_dec_ref(v_inst_3099_);
lean_dec(v_handler_3098_);
lean_dec_ref(v_inst_3097_);
lean_dec_ref(v___f_3095_);
v_a_3104_ = lean_ctor_get(v_x_3102_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_x_3102_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3106_ = v_x_3102_;
v_isShared_3107_ = v_isSharedCheck_3112_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v_x_3102_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3112_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
lean_object* v___x_3110_; 
v___x_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
return v___x_3110_;
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3146_; 
v_a_3113_ = lean_ctor_get(v_x_3102_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v_x_3102_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3115_ = v_x_3102_;
v_isShared_3116_ = v_isSharedCheck_3146_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v_x_3102_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3146_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v_snd_3117_; 
v_snd_3117_ = lean_ctor_get(v_a_3113_, 1);
lean_inc(v_snd_3117_);
if (lean_obj_tag(v_snd_3117_) == 0)
{
lean_object* v_fst_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v___f_3101_);
lean_dec_ref(v___f_3100_);
lean_dec_ref(v_inst_3099_);
lean_dec(v_handler_3098_);
lean_dec_ref(v_inst_3097_);
v_fst_3118_ = lean_ctor_get(v_a_3113_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_a_3113_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v_a_3113_, 1);
lean_dec(v_unused_3134_);
v___x_3120_ = v_a_3113_;
v_isShared_3121_ = v_isSharedCheck_3133_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_fst_3118_);
lean_dec(v_a_3113_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3133_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3122_ = lean_box(v___x_3094_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 1, v___x_3122_);
lean_ctor_set(v___x_3120_, 0, v_snd_3117_);
v___x_3124_ = v___x_3120_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_snd_3117_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_fst_3118_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = lean_unsigned_to_nat(0u);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v___x_3125_);
v___x_3128_ = v___x_3115_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3125_);
v___x_3128_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
v___x_3130_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3126_, v___x_3094_, v___x_3129_, v___f_3095_);
return v___x_3130_;
}
}
}
}
else
{
lean_object* v_fst_3135_; lean_object* v_val_3136_; lean_object* v___x_3137_; lean_object* v___f_3138_; lean_object* v___x_3139_; lean_object* v___f_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
lean_del_object(v___x_3115_);
lean_dec_ref(v___f_3095_);
v_fst_3135_ = lean_ctor_get(v_a_3113_, 0);
lean_inc_n(v_fst_3135_, 2);
lean_dec(v_a_3113_);
v_val_3136_ = lean_ctor_get(v_snd_3117_, 0);
lean_inc(v_val_3136_);
v___x_3137_ = lean_box(v___x_3096_);
v___f_3138_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_3138_, 0, v_snd_3117_);
lean_closure_set(v___f_3138_, 1, v___x_3137_);
lean_closure_set(v___f_3138_, 2, v_fst_3135_);
v___x_3139_ = lean_box(v___x_3094_);
v___f_3140_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 6, 4);
lean_closure_set(v___f_3140_, 0, v_inst_3097_);
lean_closure_set(v___f_3140_, 1, v_handler_3098_);
lean_closure_set(v___f_3140_, 2, v___x_3139_);
lean_closure_set(v___f_3140_, 3, v___f_3138_);
v___x_3141_ = lean_unsigned_to_nat(0u);
v___x_3142_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3099_, v_fst_3135_, v_val_3136_);
v___x_3143_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3141_, v___x_3094_, v___x_3142_, v___f_3100_);
v___x_3144_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3141_, v___x_3094_, v___x_3143_, v___f_3140_);
v___x_3145_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3141_, v___x_3094_, v___x_3144_, v___f_3101_);
return v___x_3145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v___x_3147_, lean_object* v___f_3148_, lean_object* v___x_3149_, lean_object* v_inst_3150_, lean_object* v_handler_3151_, lean_object* v_inst_3152_, lean_object* v___f_3153_, lean_object* v___f_3154_, lean_object* v_x_3155_, lean_object* v___y_3156_){
_start:
{
uint8_t v___x_7707__boxed_3157_; uint8_t v___x_7709__boxed_3158_; lean_object* v_res_3159_; 
v___x_7707__boxed_3157_ = lean_unbox(v___x_3147_);
v___x_7709__boxed_3158_ = lean_unbox(v___x_3149_);
v_res_3159_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_7707__boxed_3157_, v___f_3148_, v___x_7709__boxed_3158_, v_inst_3150_, v_handler_3151_, v_inst_3152_, v___f_3153_, v___f_3154_, v_x_3155_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object* v_state_3160_, lean_object* v_x_3161_){
_start:
{
if (lean_obj_tag(v_x_3161_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3171_; 
lean_dec_ref(v_state_3160_);
v_a_3163_ = lean_ctor_get(v_x_3161_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_x_3161_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3165_ = v_x_3161_;
v_isShared_3166_ = v_isSharedCheck_3171_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v_x_3161_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3171_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3169_; 
v___x_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
return v___x_3169_;
}
}
}
else
{
lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3201_; 
v_isSharedCheck_3201_ = !lean_is_exclusive(v_x_3161_);
if (v_isSharedCheck_3201_ == 0)
{
lean_object* v_unused_3202_; 
v_unused_3202_ = lean_ctor_get(v_x_3161_, 0);
lean_dec(v_unused_3202_);
v___x_3173_ = v_x_3161_;
v_isShared_3174_ = v_isSharedCheck_3201_;
goto v_resetjp_3172_;
}
else
{
lean_dec(v_x_3161_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3201_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v_machine_3175_; lean_object* v_requestStream_3176_; lean_object* v_keepAliveTimeout_3177_; lean_object* v_currentTimeout_3178_; lean_object* v_headerTimeout_3179_; lean_object* v_response_3180_; lean_object* v_respStream_3181_; uint8_t v_requiresData_3182_; lean_object* v_expectData_3183_; lean_object* v_pendingHead_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3200_; 
v_machine_3175_ = lean_ctor_get(v_state_3160_, 0);
v_requestStream_3176_ = lean_ctor_get(v_state_3160_, 1);
v_keepAliveTimeout_3177_ = lean_ctor_get(v_state_3160_, 2);
v_currentTimeout_3178_ = lean_ctor_get(v_state_3160_, 3);
v_headerTimeout_3179_ = lean_ctor_get(v_state_3160_, 4);
v_response_3180_ = lean_ctor_get(v_state_3160_, 5);
v_respStream_3181_ = lean_ctor_get(v_state_3160_, 6);
v_requiresData_3182_ = lean_ctor_get_uint8(v_state_3160_, sizeof(void*)*9);
v_expectData_3183_ = lean_ctor_get(v_state_3160_, 7);
v_pendingHead_3184_ = lean_ctor_get(v_state_3160_, 8);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_state_3160_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3186_ = v_state_3160_;
v_isShared_3187_ = v_isSharedCheck_3200_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_pendingHead_3184_);
lean_inc(v_expectData_3183_);
lean_inc(v_respStream_3181_);
lean_inc(v_response_3180_);
lean_inc(v_headerTimeout_3179_);
lean_inc(v_currentTimeout_3178_);
lean_inc(v_keepAliveTimeout_3177_);
lean_inc(v_requestStream_3176_);
lean_inc(v_machine_3175_);
lean_dec(v_state_3160_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3200_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; uint8_t v___x_3190_; lean_object* v___x_3192_; 
v___x_3188_ = lean_box(31);
v___x_3189_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3175_, v___x_3188_);
v___x_3190_ = 0;
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v___x_3189_);
v___x_3192_ = v___x_3186_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_requestStream_3176_);
lean_ctor_set(v_reuseFailAlloc_3199_, 2, v_keepAliveTimeout_3177_);
lean_ctor_set(v_reuseFailAlloc_3199_, 3, v_currentTimeout_3178_);
lean_ctor_set(v_reuseFailAlloc_3199_, 4, v_headerTimeout_3179_);
lean_ctor_set(v_reuseFailAlloc_3199_, 5, v_response_3180_);
lean_ctor_set(v_reuseFailAlloc_3199_, 6, v_respStream_3181_);
lean_ctor_set(v_reuseFailAlloc_3199_, 7, v_expectData_3183_);
lean_ctor_set(v_reuseFailAlloc_3199_, 8, v_pendingHead_3184_);
lean_ctor_set_uint8(v_reuseFailAlloc_3199_, sizeof(void*)*9, v_requiresData_3182_);
v___x_3192_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3196_; 
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*9 + 1, v___x_3190_);
v___x_3193_ = lean_box(v___x_3190_);
v___x_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3192_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 0, v___x_3194_);
v___x_3196_ = v___x_3173_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3197_; 
v___x_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
return v___x_3197_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v_state_3203_, lean_object* v_x_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_state_3203_, v_x_3204_);
return v_res_3206_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
v___x_3212_ = lean_mk_io_user_error(v___x_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3213_, lean_object* v_inst_3214_, lean_object* v_handler_3215_, lean_object* v_config_3216_, lean_object* v_event_3217_, lean_object* v_state_3218_){
_start:
{
switch(lean_obj_tag(v_event_3217_))
{
case 0:
{
lean_object* v_x_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3326_; 
lean_dec(v_handler_3215_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_inst_3213_);
v_x_3220_ = lean_ctor_get(v_event_3217_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v_event_3217_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3222_ = v_event_3217_;
v_isShared_3223_ = v_isSharedCheck_3326_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_x_3220_);
lean_dec(v_event_3217_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3326_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
if (lean_obj_tag(v_x_3220_) == 0)
{
lean_object* v_machine_3224_; lean_object* v_reader_3225_; lean_object* v_requestStream_3226_; lean_object* v_keepAliveTimeout_3227_; lean_object* v_currentTimeout_3228_; lean_object* v_headerTimeout_3229_; lean_object* v_response_3230_; lean_object* v_respStream_3231_; uint8_t v_requiresData_3232_; lean_object* v_expectData_3233_; uint8_t v_handlerDispatched_3234_; lean_object* v_pendingHead_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v_config_3216_);
v_machine_3224_ = lean_ctor_get(v_state_3218_, 0);
lean_inc_ref(v_machine_3224_);
v_reader_3225_ = lean_ctor_get(v_machine_3224_, 0);
lean_inc_ref(v_reader_3225_);
v_requestStream_3226_ = lean_ctor_get(v_state_3218_, 1);
v_keepAliveTimeout_3227_ = lean_ctor_get(v_state_3218_, 2);
v_currentTimeout_3228_ = lean_ctor_get(v_state_3218_, 3);
v_headerTimeout_3229_ = lean_ctor_get(v_state_3218_, 4);
v_response_3230_ = lean_ctor_get(v_state_3218_, 5);
v_respStream_3231_ = lean_ctor_get(v_state_3218_, 6);
v_requiresData_3232_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9);
v_expectData_3233_ = lean_ctor_get(v_state_3218_, 7);
v_handlerDispatched_3234_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9 + 1);
v_pendingHead_3235_ = lean_ctor_get(v_state_3218_, 8);
v_isSharedCheck_3277_ = !lean_is_exclusive(v_state_3218_);
if (v_isSharedCheck_3277_ == 0)
{
lean_object* v_unused_3278_; 
v_unused_3278_ = lean_ctor_get(v_state_3218_, 0);
lean_dec(v_unused_3278_);
v___x_3237_ = v_state_3218_;
v_isShared_3238_ = v_isSharedCheck_3277_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_pendingHead_3235_);
lean_inc(v_expectData_3233_);
lean_inc(v_respStream_3231_);
lean_inc(v_response_3230_);
lean_inc(v_headerTimeout_3229_);
lean_inc(v_currentTimeout_3228_);
lean_inc(v_keepAliveTimeout_3227_);
lean_inc(v_requestStream_3226_);
lean_dec(v_state_3218_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3277_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v_writer_3239_; lean_object* v_config_3240_; lean_object* v_events_3241_; lean_object* v_error_3242_; lean_object* v_instant_3243_; uint8_t v_keepAlive_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3275_; 
v_writer_3239_ = lean_ctor_get(v_machine_3224_, 1);
v_config_3240_ = lean_ctor_get(v_machine_3224_, 2);
v_events_3241_ = lean_ctor_get(v_machine_3224_, 3);
v_error_3242_ = lean_ctor_get(v_machine_3224_, 4);
v_instant_3243_ = lean_ctor_get(v_machine_3224_, 5);
v_keepAlive_3244_ = lean_ctor_get_uint8(v_machine_3224_, sizeof(void*)*6);
v_isSharedCheck_3275_ = !lean_is_exclusive(v_machine_3224_);
if (v_isSharedCheck_3275_ == 0)
{
lean_object* v_unused_3276_; 
v_unused_3276_ = lean_ctor_get(v_machine_3224_, 0);
lean_dec(v_unused_3276_);
v___x_3246_ = v_machine_3224_;
v_isShared_3247_ = v_isSharedCheck_3275_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_instant_3243_);
lean_inc(v_error_3242_);
lean_inc(v_events_3241_);
lean_inc(v_config_3240_);
lean_inc(v_writer_3239_);
lean_dec(v_machine_3224_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3275_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v_state_3248_; lean_object* v_input_3249_; lean_object* v_messageHead_3250_; lean_object* v_messageCount_3251_; lean_object* v_bodyBytesRead_3252_; lean_object* v_headerBytesRead_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3274_; 
v_state_3248_ = lean_ctor_get(v_reader_3225_, 0);
v_input_3249_ = lean_ctor_get(v_reader_3225_, 1);
v_messageHead_3250_ = lean_ctor_get(v_reader_3225_, 2);
v_messageCount_3251_ = lean_ctor_get(v_reader_3225_, 3);
v_bodyBytesRead_3252_ = lean_ctor_get(v_reader_3225_, 4);
v_headerBytesRead_3253_ = lean_ctor_get(v_reader_3225_, 5);
v_isSharedCheck_3274_ = !lean_is_exclusive(v_reader_3225_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3255_ = v_reader_3225_;
v_isShared_3256_ = v_isSharedCheck_3274_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_headerBytesRead_3253_);
lean_inc(v_bodyBytesRead_3252_);
lean_inc(v_messageCount_3251_);
lean_inc(v_messageHead_3250_);
lean_inc(v_input_3249_);
lean_inc(v_state_3248_);
lean_dec(v_reader_3225_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3274_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
uint8_t v___x_3257_; lean_object* v___x_3259_; 
v___x_3257_ = 1;
if (v_isShared_3256_ == 0)
{
v___x_3259_ = v___x_3255_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_state_3248_);
lean_ctor_set(v_reuseFailAlloc_3273_, 1, v_input_3249_);
lean_ctor_set(v_reuseFailAlloc_3273_, 2, v_messageHead_3250_);
lean_ctor_set(v_reuseFailAlloc_3273_, 3, v_messageCount_3251_);
lean_ctor_set(v_reuseFailAlloc_3273_, 4, v_bodyBytesRead_3252_);
lean_ctor_set(v_reuseFailAlloc_3273_, 5, v_headerBytesRead_3253_);
v___x_3259_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
uint8_t v___x_3260_; lean_object* v___x_3262_; 
lean_ctor_set_uint8(v___x_3259_, sizeof(void*)*6, v___x_3257_);
v___x_3260_ = 0;
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v___x_3259_);
v___x_3262_ = v___x_3246_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3259_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_writer_3239_);
lean_ctor_set(v_reuseFailAlloc_3272_, 2, v_config_3240_);
lean_ctor_set(v_reuseFailAlloc_3272_, 3, v_events_3241_);
lean_ctor_set(v_reuseFailAlloc_3272_, 4, v_error_3242_);
lean_ctor_set(v_reuseFailAlloc_3272_, 5, v_instant_3243_);
lean_ctor_set_uint8(v_reuseFailAlloc_3272_, sizeof(void*)*6, v_keepAlive_3244_);
v___x_3262_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
lean_object* v___x_3264_; 
lean_ctor_set_uint8(v___x_3262_, sizeof(void*)*6 + 1, v___x_3260_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3262_);
v___x_3264_ = v___x_3237_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3262_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_requestStream_3226_);
lean_ctor_set(v_reuseFailAlloc_3271_, 2, v_keepAliveTimeout_3227_);
lean_ctor_set(v_reuseFailAlloc_3271_, 3, v_currentTimeout_3228_);
lean_ctor_set(v_reuseFailAlloc_3271_, 4, v_headerTimeout_3229_);
lean_ctor_set(v_reuseFailAlloc_3271_, 5, v_response_3230_);
lean_ctor_set(v_reuseFailAlloc_3271_, 6, v_respStream_3231_);
lean_ctor_set(v_reuseFailAlloc_3271_, 7, v_expectData_3233_);
lean_ctor_set(v_reuseFailAlloc_3271_, 8, v_pendingHead_3235_);
lean_ctor_set_uint8(v_reuseFailAlloc_3271_, sizeof(void*)*9, v_requiresData_3232_);
lean_ctor_set_uint8(v_reuseFailAlloc_3271_, sizeof(void*)*9 + 1, v_handlerDispatched_3234_);
v___x_3264_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3265_ = lean_box(v___x_3260_);
v___x_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3264_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set_tag(v___x_3222_, 1);
lean_ctor_set(v___x_3222_, 0, v___x_3266_);
v___x_3268_ = v___x_3222_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3266_);
v___x_3268_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; 
v___x_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
return v___x_3269_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_val_3279_; lean_object* v_machine_3280_; lean_object* v_requestStream_3281_; lean_object* v_keepAliveTimeout_3282_; lean_object* v_currentTimeout_3283_; lean_object* v_response_3284_; lean_object* v_respStream_3285_; uint8_t v_requiresData_3286_; lean_object* v_expectData_3287_; uint8_t v_handlerDispatched_3288_; lean_object* v_pendingHead_3289_; lean_object* v___f_3290_; 
lean_del_object(v___x_3222_);
v_val_3279_ = lean_ctor_get(v_x_3220_, 0);
lean_inc_n(v_val_3279_, 2);
lean_dec_ref_known(v_x_3220_, 1);
v_machine_3280_ = lean_ctor_get(v_state_3218_, 0);
v_requestStream_3281_ = lean_ctor_get(v_state_3218_, 1);
v_keepAliveTimeout_3282_ = lean_ctor_get(v_state_3218_, 2);
lean_inc(v_keepAliveTimeout_3282_);
v_currentTimeout_3283_ = lean_ctor_get(v_state_3218_, 3);
v_response_3284_ = lean_ctor_get(v_state_3218_, 5);
v_respStream_3285_ = lean_ctor_get(v_state_3218_, 6);
v_requiresData_3286_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9);
v_expectData_3287_ = lean_ctor_get(v_state_3218_, 7);
v_handlerDispatched_3288_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9 + 1);
v_pendingHead_3289_ = lean_ctor_get(v_state_3218_, 8);
v___f_3290_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3290_, 0, v_val_3279_);
if (lean_obj_tag(v_keepAliveTimeout_3282_) == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
lean_dec_ref(v___f_3290_);
lean_dec_ref(v_config_3216_);
v___x_3291_ = lean_box(0);
v___x_3292_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3279_, v___x_3291_, v_state_3218_);
return v___x_3292_;
}
else
{
lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3324_; 
lean_inc(v_pendingHead_3289_);
lean_inc(v_expectData_3287_);
lean_inc(v_respStream_3285_);
lean_inc_ref(v_response_3284_);
lean_inc(v_currentTimeout_3283_);
lean_inc_ref(v_requestStream_3281_);
lean_inc_ref(v_machine_3280_);
lean_dec(v_val_3279_);
lean_dec_ref(v_state_3218_);
v_isSharedCheck_3324_ = !lean_is_exclusive(v_keepAliveTimeout_3282_);
if (v_isSharedCheck_3324_ == 0)
{
lean_object* v_unused_3325_; 
v_unused_3325_ = lean_ctor_get(v_keepAliveTimeout_3282_, 0);
lean_dec(v_unused_3325_);
v___x_3294_ = v_keepAliveTimeout_3282_;
v_isShared_3295_ = v_isSharedCheck_3324_;
goto v_resetjp_3293_;
}
else
{
lean_dec(v_keepAliveTimeout_3282_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3324_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___f_3298_; lean_object* v___x_3299_; uint8_t v___x_3300_; lean_object* v_val_3302_; lean_object* v___x_3307_; 
v___x_3296_ = lean_box(v_requiresData_3286_);
v___x_3297_ = lean_box(v_handlerDispatched_3288_);
v___f_3298_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3298_, 0, v_config_3216_);
lean_closure_set(v___f_3298_, 1, v_machine_3280_);
lean_closure_set(v___f_3298_, 2, v_requestStream_3281_);
lean_closure_set(v___f_3298_, 3, v_currentTimeout_3283_);
lean_closure_set(v___f_3298_, 4, v_response_3284_);
lean_closure_set(v___f_3298_, 5, v_respStream_3285_);
lean_closure_set(v___f_3298_, 6, v___x_3296_);
lean_closure_set(v___f_3298_, 7, v_expectData_3287_);
lean_closure_set(v___f_3298_, 8, v___x_3297_);
lean_closure_set(v___f_3298_, 9, v_pendingHead_3289_);
lean_closure_set(v___f_3298_, 10, v___f_3290_);
v___x_3299_ = lean_unsigned_to_nat(0u);
v___x_3300_ = 0;
v___x_3307_ = lean_get_current_time();
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3307_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3307_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
lean_ctor_set_tag(v___x_3310_, 1);
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
v_val_3302_ = v___x_3313_;
goto v___jp_3301_;
}
}
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
v_a_3316_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3307_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3307_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
lean_ctor_set_tag(v___x_3318_, 0);
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
v_val_3302_ = v___x_3321_;
goto v___jp_3301_;
}
}
}
v___jp_3301_:
{
lean_object* v___x_3304_; 
if (v_isShared_3295_ == 0)
{
lean_ctor_set_tag(v___x_3294_, 0);
lean_ctor_set(v___x_3294_, 0, v_val_3302_);
v___x_3304_ = v___x_3294_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_val_3302_);
v___x_3304_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
lean_object* v___x_3305_; 
v___x_3305_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3299_, v___x_3300_, v___x_3304_, v___f_3298_);
return v___x_3305_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3437_; 
lean_dec_ref(v_config_3216_);
lean_dec(v_handler_3215_);
lean_dec_ref(v_inst_3213_);
v_x_3327_ = lean_ctor_get(v_event_3217_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_event_3217_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3329_ = v_event_3217_;
v_isShared_3330_ = v_isSharedCheck_3437_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_x_3327_);
lean_dec(v_event_3217_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3437_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
if (lean_obj_tag(v_x_3327_) == 0)
{
lean_object* v_machine_3331_; lean_object* v_requestStream_3332_; lean_object* v_keepAliveTimeout_3333_; lean_object* v_currentTimeout_3334_; lean_object* v_headerTimeout_3335_; lean_object* v_response_3336_; lean_object* v_respStream_3337_; uint8_t v_requiresData_3338_; lean_object* v_expectData_3339_; uint8_t v_handlerDispatched_3340_; lean_object* v_pendingHead_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___f_3344_; 
lean_del_object(v___x_3329_);
v_machine_3331_ = lean_ctor_get(v_state_3218_, 0);
lean_inc_ref_n(v_machine_3331_, 2);
v_requestStream_3332_ = lean_ctor_get(v_state_3218_, 1);
lean_inc_ref_n(v_requestStream_3332_, 2);
v_keepAliveTimeout_3333_ = lean_ctor_get(v_state_3218_, 2);
lean_inc_n(v_keepAliveTimeout_3333_, 2);
v_currentTimeout_3334_ = lean_ctor_get(v_state_3218_, 3);
lean_inc_n(v_currentTimeout_3334_, 2);
v_headerTimeout_3335_ = lean_ctor_get(v_state_3218_, 4);
lean_inc_n(v_headerTimeout_3335_, 2);
v_response_3336_ = lean_ctor_get(v_state_3218_, 5);
lean_inc_ref_n(v_response_3336_, 2);
v_respStream_3337_ = lean_ctor_get(v_state_3218_, 6);
lean_inc(v_respStream_3337_);
v_requiresData_3338_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9);
v_expectData_3339_ = lean_ctor_get(v_state_3218_, 7);
lean_inc_n(v_expectData_3339_, 2);
v_handlerDispatched_3340_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9 + 1);
v_pendingHead_3341_ = lean_ctor_get(v_state_3218_, 8);
lean_inc_n(v_pendingHead_3341_, 2);
lean_dec_ref(v_state_3218_);
v___x_3342_ = lean_box(v_requiresData_3338_);
v___x_3343_ = lean_box(v_handlerDispatched_3340_);
v___f_3344_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3344_, 0, v_machine_3331_);
lean_closure_set(v___f_3344_, 1, v_requestStream_3332_);
lean_closure_set(v___f_3344_, 2, v_keepAliveTimeout_3333_);
lean_closure_set(v___f_3344_, 3, v_currentTimeout_3334_);
lean_closure_set(v___f_3344_, 4, v_headerTimeout_3335_);
lean_closure_set(v___f_3344_, 5, v_response_3336_);
lean_closure_set(v___f_3344_, 6, v___x_3342_);
lean_closure_set(v___f_3344_, 7, v_expectData_3339_);
lean_closure_set(v___f_3344_, 8, v___x_3343_);
lean_closure_set(v___f_3344_, 9, v_pendingHead_3341_);
if (lean_obj_tag(v_respStream_3337_) == 1)
{
lean_object* v_val_3345_; lean_object* v_close_3346_; lean_object* v_isClosed_3347_; lean_object* v___f_3348_; lean_object* v___f_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec(v_pendingHead_3341_);
lean_dec(v_expectData_3339_);
lean_dec_ref(v_response_3336_);
lean_dec(v_headerTimeout_3335_);
lean_dec(v_currentTimeout_3334_);
lean_dec(v_keepAliveTimeout_3333_);
lean_dec_ref(v_requestStream_3332_);
lean_dec_ref(v_machine_3331_);
v_val_3345_ = lean_ctor_get(v_respStream_3337_, 0);
lean_inc_n(v_val_3345_, 2);
lean_dec_ref_known(v_respStream_3337_, 1);
v_close_3346_ = lean_ctor_get(v_inst_3214_, 1);
lean_inc_ref(v_close_3346_);
v_isClosed_3347_ = lean_ctor_get(v_inst_3214_, 2);
lean_inc_ref(v_isClosed_3347_);
lean_dec_ref(v_inst_3214_);
lean_inc_ref(v___f_3344_);
v___f_3348_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3348_, 0, v___f_3344_);
v___f_3349_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3349_, 0, v_close_3346_);
lean_closure_set(v___f_3349_, 1, v_val_3345_);
lean_closure_set(v___f_3349_, 2, v___f_3348_);
lean_closure_set(v___f_3349_, 3, v___f_3344_);
v___x_3350_ = lean_unsigned_to_nat(0u);
v___x_3351_ = 0;
v___x_3352_ = lean_apply_2(v_isClosed_3347_, v_val_3345_, lean_box(0));
v___x_3353_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3350_, v___x_3351_, v___x_3352_, v___f_3349_);
return v___x_3353_;
}
else
{
lean_object* v___x_3354_; lean_object* v___x_3355_; 
lean_dec_ref(v___f_3344_);
lean_dec(v_respStream_3337_);
lean_dec_ref(v_inst_3214_);
v___x_3354_ = lean_box(0);
v___x_3355_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3331_, v_requestStream_3332_, v_keepAliveTimeout_3333_, v_currentTimeout_3334_, v_headerTimeout_3335_, v_response_3336_, v_requiresData_3338_, v_expectData_3339_, v_handlerDispatched_3340_, v_pendingHead_3341_, v___x_3354_);
return v___x_3355_;
}
}
else
{
lean_object* v_val_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3436_; 
lean_dec_ref(v_inst_3214_);
v_val_3356_ = lean_ctor_get(v_x_3327_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v_x_3327_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3358_ = v_x_3327_;
v_isShared_3359_ = v_isSharedCheck_3436_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_val_3356_);
lean_dec(v_x_3327_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3436_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v_machine_3360_; lean_object* v_requestStream_3361_; lean_object* v_keepAliveTimeout_3362_; lean_object* v_currentTimeout_3363_; lean_object* v_headerTimeout_3364_; lean_object* v_response_3365_; lean_object* v_respStream_3366_; uint8_t v_requiresData_3367_; lean_object* v_expectData_3368_; uint8_t v_handlerDispatched_3369_; lean_object* v_pendingHead_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3435_; 
v_machine_3360_ = lean_ctor_get(v_state_3218_, 0);
v_requestStream_3361_ = lean_ctor_get(v_state_3218_, 1);
v_keepAliveTimeout_3362_ = lean_ctor_get(v_state_3218_, 2);
v_currentTimeout_3363_ = lean_ctor_get(v_state_3218_, 3);
v_headerTimeout_3364_ = lean_ctor_get(v_state_3218_, 4);
v_response_3365_ = lean_ctor_get(v_state_3218_, 5);
v_respStream_3366_ = lean_ctor_get(v_state_3218_, 6);
v_requiresData_3367_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9);
v_expectData_3368_ = lean_ctor_get(v_state_3218_, 7);
v_handlerDispatched_3369_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9 + 1);
v_pendingHead_3370_ = lean_ctor_get(v_state_3218_, 8);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_state_3218_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3372_ = v_state_3218_;
v_isShared_3373_ = v_isSharedCheck_3435_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_pendingHead_3370_);
lean_inc(v_expectData_3368_);
lean_inc(v_respStream_3366_);
lean_inc(v_response_3365_);
lean_inc(v_headerTimeout_3364_);
lean_inc(v_currentTimeout_3363_);
lean_inc(v_keepAliveTimeout_3362_);
lean_inc(v_requestStream_3361_);
lean_inc(v_machine_3360_);
lean_dec(v_state_3218_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3435_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___y_3375_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3388_ = lean_unsigned_to_nat(1u);
v___x_3389_ = lean_mk_empty_array_with_capacity(v___x_3388_);
v___x_3390_ = lean_array_push(v___x_3389_, v_val_3356_);
v___x_3391_ = lean_array_get_size(v___x_3390_);
v___x_3392_ = lean_unsigned_to_nat(0u);
v___x_3393_ = lean_nat_dec_eq(v___x_3391_, v___x_3392_);
if (v___x_3393_ == 0)
{
lean_object* v_reader_3394_; lean_object* v_writer_3395_; lean_object* v_config_3396_; lean_object* v_events_3397_; lean_object* v_error_3398_; lean_object* v_instant_3399_; uint8_t v_keepAlive_3400_; uint8_t v_pullBodyStalled_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3434_; 
v_reader_3394_ = lean_ctor_get(v_machine_3360_, 0);
v_writer_3395_ = lean_ctor_get(v_machine_3360_, 1);
v_config_3396_ = lean_ctor_get(v_machine_3360_, 2);
v_events_3397_ = lean_ctor_get(v_machine_3360_, 3);
v_error_3398_ = lean_ctor_get(v_machine_3360_, 4);
v_instant_3399_ = lean_ctor_get(v_machine_3360_, 5);
v_keepAlive_3400_ = lean_ctor_get_uint8(v_machine_3360_, sizeof(void*)*6);
v_pullBodyStalled_3401_ = lean_ctor_get_uint8(v_machine_3360_, sizeof(void*)*6 + 1);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_machine_3360_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3403_ = v_machine_3360_;
v_isShared_3404_ = v_isSharedCheck_3434_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_instant_3399_);
lean_inc(v_error_3398_);
lean_inc(v_events_3397_);
lean_inc(v_config_3396_);
lean_inc(v_writer_3395_);
lean_inc(v_reader_3394_);
lean_dec(v_machine_3360_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3434_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___y_3406_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v___x_3428_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_3429_ = lean_nat_dec_lt(v___x_3392_, v___x_3391_);
if (v___x_3429_ == 0)
{
v___y_3406_ = v___x_3392_;
goto v___jp_3405_;
}
else
{
lean_object* v___f_3430_; size_t v___x_3431_; size_t v___x_3432_; lean_object* v___x_3433_; 
v___f_3430_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3431_ = ((size_t)0ULL);
v___x_3432_ = lean_usize_of_nat(v___x_3391_);
lean_inc_ref(v___x_3390_);
v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3428_, v___f_3430_, v___x_3390_, v___x_3431_, v___x_3432_, v___x_3392_);
v___y_3406_ = v___x_3433_;
goto v___jp_3405_;
}
v___jp_3405_:
{
lean_object* v_userData_3407_; lean_object* v_outputData_3408_; lean_object* v_state_3409_; lean_object* v_knownSize_3410_; lean_object* v_messageHead_3411_; uint8_t v_sentMessage_3412_; uint8_t v_userClosedBody_3413_; uint8_t v_omitBody_3414_; lean_object* v_userDataBytes_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3427_; 
v_userData_3407_ = lean_ctor_get(v_writer_3395_, 0);
v_outputData_3408_ = lean_ctor_get(v_writer_3395_, 1);
v_state_3409_ = lean_ctor_get(v_writer_3395_, 2);
v_knownSize_3410_ = lean_ctor_get(v_writer_3395_, 3);
v_messageHead_3411_ = lean_ctor_get(v_writer_3395_, 4);
v_sentMessage_3412_ = lean_ctor_get_uint8(v_writer_3395_, sizeof(void*)*6);
v_userClosedBody_3413_ = lean_ctor_get_uint8(v_writer_3395_, sizeof(void*)*6 + 1);
v_omitBody_3414_ = lean_ctor_get_uint8(v_writer_3395_, sizeof(void*)*6 + 2);
v_userDataBytes_3415_ = lean_ctor_get(v_writer_3395_, 5);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_writer_3395_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3417_ = v_writer_3395_;
v_isShared_3418_ = v_isSharedCheck_3427_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_userDataBytes_3415_);
lean_inc(v_messageHead_3411_);
lean_inc(v_knownSize_3410_);
lean_inc(v_state_3409_);
lean_inc(v_outputData_3408_);
lean_inc(v_userData_3407_);
lean_dec(v_writer_3395_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3427_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3419_ = l_Array_append___redArg(v_userData_3407_, v___x_3390_);
lean_dec_ref(v___x_3390_);
v___x_3420_ = lean_nat_add(v_userDataBytes_3415_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec(v_userDataBytes_3415_);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 5, v___x_3420_);
lean_ctor_set(v___x_3417_, 0, v___x_3419_);
v___x_3422_ = v___x_3417_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_outputData_3408_);
lean_ctor_set(v_reuseFailAlloc_3426_, 2, v_state_3409_);
lean_ctor_set(v_reuseFailAlloc_3426_, 3, v_knownSize_3410_);
lean_ctor_set(v_reuseFailAlloc_3426_, 4, v_messageHead_3411_);
lean_ctor_set(v_reuseFailAlloc_3426_, 5, v___x_3420_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, sizeof(void*)*6, v_sentMessage_3412_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, sizeof(void*)*6 + 1, v_userClosedBody_3413_);
lean_ctor_set_uint8(v_reuseFailAlloc_3426_, sizeof(void*)*6 + 2, v_omitBody_3414_);
v___x_3422_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3424_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 1, v___x_3422_);
v___x_3424_ = v___x_3403_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_reader_3394_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v_config_3396_);
lean_ctor_set(v_reuseFailAlloc_3425_, 3, v_events_3397_);
lean_ctor_set(v_reuseFailAlloc_3425_, 4, v_error_3398_);
lean_ctor_set(v_reuseFailAlloc_3425_, 5, v_instant_3399_);
lean_ctor_set_uint8(v_reuseFailAlloc_3425_, sizeof(void*)*6, v_keepAlive_3400_);
lean_ctor_set_uint8(v_reuseFailAlloc_3425_, sizeof(void*)*6 + 1, v_pullBodyStalled_3401_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
v___y_3375_ = v___x_3424_;
goto v___jp_3374_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3390_);
v___y_3375_ = v_machine_3360_;
goto v___jp_3374_;
}
v___jp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___y_3375_);
v___x_3377_ = v___x_3372_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___y_3375_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_requestStream_3361_);
lean_ctor_set(v_reuseFailAlloc_3387_, 2, v_keepAliveTimeout_3362_);
lean_ctor_set(v_reuseFailAlloc_3387_, 3, v_currentTimeout_3363_);
lean_ctor_set(v_reuseFailAlloc_3387_, 4, v_headerTimeout_3364_);
lean_ctor_set(v_reuseFailAlloc_3387_, 5, v_response_3365_);
lean_ctor_set(v_reuseFailAlloc_3387_, 6, v_respStream_3366_);
lean_ctor_set(v_reuseFailAlloc_3387_, 7, v_expectData_3368_);
lean_ctor_set(v_reuseFailAlloc_3387_, 8, v_pendingHead_3370_);
lean_ctor_set_uint8(v_reuseFailAlloc_3387_, sizeof(void*)*9, v_requiresData_3367_);
lean_ctor_set_uint8(v_reuseFailAlloc_3387_, sizeof(void*)*9 + 1, v_handlerDispatched_3369_);
v___x_3377_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
uint8_t v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3382_; 
v___x_3378_ = 0;
v___x_3379_ = lean_box(v___x_3378_);
v___x_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3377_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v___x_3380_);
v___x_3382_ = v___x_3358_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
lean_object* v___x_3384_; 
if (v_isShared_3330_ == 0)
{
lean_ctor_set_tag(v___x_3329_, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3382_);
v___x_3384_ = v___x_3329_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
}
}
}
}
case 2:
{
uint8_t v_x_3438_; 
lean_dec_ref(v_config_3216_);
lean_dec_ref(v_inst_3214_);
v_x_3438_ = lean_ctor_get_uint8(v_event_3217_, 0);
lean_dec_ref_known(v_event_3217_, 0);
if (v_x_3438_ == 0)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
lean_dec(v_handler_3215_);
lean_dec_ref(v_inst_3213_);
v___x_3439_ = lean_box(v_x_3438_);
v___x_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3440_, 0, v_state_3218_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
v___x_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
v___x_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
return v___x_3442_;
}
else
{
lean_object* v_machine_3443_; lean_object* v_requestStream_3444_; lean_object* v_keepAliveTimeout_3445_; lean_object* v_currentTimeout_3446_; lean_object* v_headerTimeout_3447_; lean_object* v_response_3448_; lean_object* v_respStream_3449_; uint8_t v_requiresData_3450_; lean_object* v_expectData_3451_; uint8_t v_handlerDispatched_3452_; lean_object* v_pendingHead_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3502_; 
v_machine_3443_ = lean_ctor_get(v_state_3218_, 0);
v_requestStream_3444_ = lean_ctor_get(v_state_3218_, 1);
v_keepAliveTimeout_3445_ = lean_ctor_get(v_state_3218_, 2);
v_currentTimeout_3446_ = lean_ctor_get(v_state_3218_, 3);
v_headerTimeout_3447_ = lean_ctor_get(v_state_3218_, 4);
v_response_3448_ = lean_ctor_get(v_state_3218_, 5);
v_respStream_3449_ = lean_ctor_get(v_state_3218_, 6);
v_requiresData_3450_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9);
v_expectData_3451_ = lean_ctor_get(v_state_3218_, 7);
v_handlerDispatched_3452_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9 + 1);
v_pendingHead_3453_ = lean_ctor_get(v_state_3218_, 8);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_state_3218_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3455_ = v_state_3218_;
v_isShared_3456_ = v_isSharedCheck_3502_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_pendingHead_3453_);
lean_inc(v_expectData_3451_);
lean_inc(v_respStream_3449_);
lean_inc(v_response_3448_);
lean_inc(v_headerTimeout_3447_);
lean_inc(v_currentTimeout_3446_);
lean_inc(v_keepAliveTimeout_3445_);
lean_inc(v_requestStream_3444_);
lean_inc(v_machine_3443_);
lean_dec(v_state_3218_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3502_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
uint8_t v___x_3457_; lean_object* v___x_3458_; lean_object* v_fst_3459_; lean_object* v_snd_3460_; lean_object* v_reader_3461_; lean_object* v_writer_3462_; lean_object* v_config_3463_; lean_object* v_events_3464_; lean_object* v_error_3465_; lean_object* v_instant_3466_; uint8_t v_keepAlive_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3501_; 
v___x_3457_ = 0;
v___x_3458_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3457_, v_machine_3443_);
v_fst_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_fst_3459_);
v_snd_3460_ = lean_ctor_get(v___x_3458_, 1);
lean_inc(v_snd_3460_);
lean_dec_ref(v___x_3458_);
v_reader_3461_ = lean_ctor_get(v_fst_3459_, 0);
v_writer_3462_ = lean_ctor_get(v_fst_3459_, 1);
v_config_3463_ = lean_ctor_get(v_fst_3459_, 2);
v_events_3464_ = lean_ctor_get(v_fst_3459_, 3);
v_error_3465_ = lean_ctor_get(v_fst_3459_, 4);
v_instant_3466_ = lean_ctor_get(v_fst_3459_, 5);
v_keepAlive_3467_ = lean_ctor_get_uint8(v_fst_3459_, sizeof(void*)*6);
v_isSharedCheck_3501_ = !lean_is_exclusive(v_fst_3459_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3469_ = v_fst_3459_;
v_isShared_3470_ = v_isSharedCheck_3501_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_instant_3466_);
lean_inc(v_error_3465_);
lean_inc(v_events_3464_);
lean_inc(v_config_3463_);
lean_inc(v_writer_3462_);
lean_inc(v_reader_3461_);
lean_dec(v_fst_3459_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3501_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___f_3471_; lean_object* v___f_3472_; uint8_t v___y_3474_; 
v___f_3471_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_3472_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_3472_, 0, v_inst_3213_);
lean_closure_set(v___f_3472_, 1, v_handler_3215_);
if (lean_obj_tag(v_snd_3460_) == 0)
{
uint8_t v_sentMessage_3497_; 
v_sentMessage_3497_ = lean_ctor_get_uint8(v_writer_3462_, sizeof(void*)*6);
if (v_sentMessage_3497_ == 0)
{
lean_object* v_state_3498_; 
v_state_3498_ = lean_ctor_get(v_reader_3461_, 0);
if (lean_obj_tag(v_state_3498_) == 2)
{
v___y_3474_ = v_x_3438_;
goto v___jp_3473_;
}
else
{
v___y_3474_ = v_sentMessage_3497_;
goto v___jp_3473_;
}
}
else
{
uint8_t v___x_3499_; 
v___x_3499_ = 0;
v___y_3474_ = v___x_3499_;
goto v___jp_3473_;
}
}
else
{
uint8_t v___x_3500_; 
v___x_3500_ = 0;
v___y_3474_ = v___x_3500_;
goto v___jp_3473_;
}
v___jp_3473_:
{
lean_object* v___x_3476_; 
if (v_isShared_3470_ == 0)
{
v___x_3476_ = v___x_3469_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_reader_3461_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_writer_3462_);
lean_ctor_set(v_reuseFailAlloc_3496_, 2, v_config_3463_);
lean_ctor_set(v_reuseFailAlloc_3496_, 3, v_events_3464_);
lean_ctor_set(v_reuseFailAlloc_3496_, 4, v_error_3465_);
lean_ctor_set(v_reuseFailAlloc_3496_, 5, v_instant_3466_);
lean_ctor_set_uint8(v_reuseFailAlloc_3496_, sizeof(void*)*6, v_keepAlive_3467_);
v___x_3476_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v_st_3478_; 
lean_ctor_set_uint8(v___x_3476_, sizeof(void*)*6 + 1, v___y_3474_);
lean_inc_ref(v_requestStream_3444_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3476_);
v_st_3478_ = v___x_3455_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_requestStream_3444_);
lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_keepAliveTimeout_3445_);
lean_ctor_set(v_reuseFailAlloc_3495_, 3, v_currentTimeout_3446_);
lean_ctor_set(v_reuseFailAlloc_3495_, 4, v_headerTimeout_3447_);
lean_ctor_set(v_reuseFailAlloc_3495_, 5, v_response_3448_);
lean_ctor_set(v_reuseFailAlloc_3495_, 6, v_respStream_3449_);
lean_ctor_set(v_reuseFailAlloc_3495_, 7, v_expectData_3451_);
lean_ctor_set(v_reuseFailAlloc_3495_, 8, v_pendingHead_3453_);
lean_ctor_set_uint8(v_reuseFailAlloc_3495_, sizeof(void*)*9, v_requiresData_3450_);
lean_ctor_set_uint8(v_reuseFailAlloc_3495_, sizeof(void*)*9 + 1, v_handlerDispatched_3452_);
v_st_3478_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___f_3479_; 
lean_inc_ref(v_st_3478_);
v___f_3479_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3479_, 0, v_st_3478_);
if (lean_obj_tag(v_snd_3460_) == 1)
{
lean_object* v_val_3480_; uint8_t v_final_3481_; uint8_t v_incomplete_3482_; lean_object* v_chunk_3483_; lean_object* v___f_3484_; lean_object* v___f_3485_; lean_object* v___x_3486_; lean_object* v___f_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
lean_dec_ref(v_st_3478_);
v_val_3480_ = lean_ctor_get(v_snd_3460_, 0);
lean_inc(v_val_3480_);
lean_dec_ref_known(v_snd_3460_, 1);
v_final_3481_ = lean_ctor_get_uint8(v_val_3480_, sizeof(void*)*1);
v_incomplete_3482_ = lean_ctor_get_uint8(v_val_3480_, sizeof(void*)*1 + 1);
v_chunk_3483_ = lean_ctor_get(v_val_3480_, 0);
lean_inc_ref(v_chunk_3483_);
lean_dec(v_val_3480_);
lean_inc_ref_n(v___f_3479_, 2);
v___f_3484_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3484_, 0, v___f_3479_);
lean_inc_ref_n(v_requestStream_3444_, 2);
v___f_3485_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3485_, 0, v_requestStream_3444_);
lean_closure_set(v___f_3485_, 1, v___f_3484_);
lean_closure_set(v___f_3485_, 2, v___f_3479_);
v___x_3486_ = lean_box(v_final_3481_);
v___f_3487_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 7, 5);
lean_closure_set(v___f_3487_, 0, v___x_3486_);
lean_closure_set(v___f_3487_, 1, v___f_3479_);
lean_closure_set(v___f_3487_, 2, v___f_3471_);
lean_closure_set(v___f_3487_, 3, v_requestStream_3444_);
lean_closure_set(v___f_3487_, 4, v___f_3485_);
v___x_3488_ = lean_unsigned_to_nat(0u);
v___x_3489_ = 0;
v___x_3490_ = l_Std_Http_Body_Stream_send(v_requestStream_3444_, v_chunk_3483_, v_incomplete_3482_);
v___x_3491_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3488_, v___x_3489_, v___x_3490_, v___f_3472_);
v___x_3492_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3488_, v___x_3489_, v___x_3491_, v___f_3487_);
return v___x_3492_;
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
lean_dec_ref(v___f_3479_);
lean_dec_ref(v___f_3472_);
lean_dec(v_snd_3460_);
lean_dec_ref(v_requestStream_3444_);
v___x_3493_ = lean_box(0);
v___x_3494_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_3478_, v___x_3493_);
return v___x_3494_;
}
}
}
}
}
}
}
}
case 3:
{
lean_object* v_x_3503_; 
v_x_3503_ = lean_ctor_get(v_event_3217_, 0);
lean_inc_ref(v_x_3503_);
lean_dec_ref_known(v_event_3217_, 1);
if (lean_obj_tag(v_x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v_onFailure_3505_; lean_object* v___f_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
lean_dec_ref(v_config_3216_);
lean_dec_ref(v_inst_3214_);
v_a_3504_ = lean_ctor_get(v_x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v_x_3503_, 1);
v_onFailure_3505_ = lean_ctor_get(v_inst_3213_, 2);
lean_inc_ref(v_onFailure_3505_);
lean_dec_ref(v_inst_3213_);
v___f_3506_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3506_, 0, v_state_3218_);
v___x_3507_ = lean_unsigned_to_nat(0u);
v___x_3508_ = 0;
v___x_3509_ = lean_apply_3(v_onFailure_3505_, v_handler_3215_, v_a_3504_, lean_box(0));
v___x_3510_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3507_, v___x_3508_, v___x_3509_, v___f_3506_);
return v___x_3510_;
}
else
{
lean_object* v_machine_3511_; lean_object* v_reader_3512_; lean_object* v_state_3513_; 
v_machine_3511_ = lean_ctor_get(v_state_3218_, 0);
lean_inc_ref(v_machine_3511_);
v_reader_3512_ = lean_ctor_get(v_machine_3511_, 0);
v_state_3513_ = lean_ctor_get(v_reader_3512_, 0);
if (lean_obj_tag(v_state_3513_) == 7)
{
lean_object* v_a_3514_; lean_object* v_requestStream_3515_; lean_object* v_keepAliveTimeout_3516_; lean_object* v_currentTimeout_3517_; lean_object* v_headerTimeout_3518_; lean_object* v_response_3519_; lean_object* v_respStream_3520_; uint8_t v_requiresData_3521_; lean_object* v_expectData_3522_; lean_object* v_pendingHead_3523_; lean_object* v_close_3524_; lean_object* v_isClosed_3525_; lean_object* v_body_3526_; lean_object* v___x_3527_; lean_object* v___f_3528_; lean_object* v___f_3529_; lean_object* v___f_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
lean_dec_ref(v_config_3216_);
lean_dec(v_handler_3215_);
lean_dec_ref(v_inst_3213_);
v_a_3514_ = lean_ctor_get(v_x_3503_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v_x_3503_, 1);
v_requestStream_3515_ = lean_ctor_get(v_state_3218_, 1);
lean_inc_ref(v_requestStream_3515_);
v_keepAliveTimeout_3516_ = lean_ctor_get(v_state_3218_, 2);
lean_inc(v_keepAliveTimeout_3516_);
v_currentTimeout_3517_ = lean_ctor_get(v_state_3218_, 3);
lean_inc(v_currentTimeout_3517_);
v_headerTimeout_3518_ = lean_ctor_get(v_state_3218_, 4);
lean_inc(v_headerTimeout_3518_);
v_response_3519_ = lean_ctor_get(v_state_3218_, 5);
lean_inc_ref(v_response_3519_);
v_respStream_3520_ = lean_ctor_get(v_state_3218_, 6);
lean_inc(v_respStream_3520_);
v_requiresData_3521_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9);
v_expectData_3522_ = lean_ctor_get(v_state_3218_, 7);
lean_inc(v_expectData_3522_);
v_pendingHead_3523_ = lean_ctor_get(v_state_3218_, 8);
lean_inc(v_pendingHead_3523_);
lean_dec_ref(v_state_3218_);
v_close_3524_ = lean_ctor_get(v_inst_3214_, 1);
lean_inc_ref(v_close_3524_);
v_isClosed_3525_ = lean_ctor_get(v_inst_3214_, 2);
lean_inc_ref(v_isClosed_3525_);
lean_dec_ref(v_inst_3214_);
v_body_3526_ = lean_ctor_get(v_a_3514_, 1);
lean_inc_n(v_body_3526_, 2);
lean_dec(v_a_3514_);
v___x_3527_ = lean_box(v_requiresData_3521_);
v___f_3528_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3528_, 0, v_machine_3511_);
lean_closure_set(v___f_3528_, 1, v_requestStream_3515_);
lean_closure_set(v___f_3528_, 2, v_keepAliveTimeout_3516_);
lean_closure_set(v___f_3528_, 3, v_currentTimeout_3517_);
lean_closure_set(v___f_3528_, 4, v_headerTimeout_3518_);
lean_closure_set(v___f_3528_, 5, v_response_3519_);
lean_closure_set(v___f_3528_, 6, v_respStream_3520_);
lean_closure_set(v___f_3528_, 7, v___x_3527_);
lean_closure_set(v___f_3528_, 8, v_expectData_3522_);
lean_closure_set(v___f_3528_, 9, v_pendingHead_3523_);
lean_inc_ref(v___f_3528_);
v___f_3529_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3529_, 0, v___f_3528_);
v___f_3530_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3530_, 0, v_close_3524_);
lean_closure_set(v___f_3530_, 1, v_body_3526_);
lean_closure_set(v___f_3530_, 2, v___f_3529_);
lean_closure_set(v___f_3530_, 3, v___f_3528_);
v___x_3531_ = lean_unsigned_to_nat(0u);
v___x_3532_ = 0;
v___x_3533_ = lean_apply_2(v_isClosed_3525_, v_body_3526_, lean_box(0));
v___x_3534_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3531_, v___x_3532_, v___x_3533_, v___f_3530_);
return v___x_3534_;
}
else
{
lean_object* v_a_3535_; lean_object* v_requestStream_3536_; lean_object* v_keepAliveTimeout_3537_; lean_object* v_currentTimeout_3538_; lean_object* v_headerTimeout_3539_; lean_object* v_response_3540_; uint8_t v_requiresData_3541_; lean_object* v_expectData_3542_; lean_object* v_pendingHead_3543_; uint8_t v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___f_3547_; lean_object* v___f_3548_; lean_object* v___f_3549_; uint8_t v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___f_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v_a_3535_ = lean_ctor_get(v_x_3503_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v_x_3503_, 1);
v_requestStream_3536_ = lean_ctor_get(v_state_3218_, 1);
lean_inc_ref(v_requestStream_3536_);
v_keepAliveTimeout_3537_ = lean_ctor_get(v_state_3218_, 2);
lean_inc(v_keepAliveTimeout_3537_);
v_currentTimeout_3538_ = lean_ctor_get(v_state_3218_, 3);
lean_inc(v_currentTimeout_3538_);
v_headerTimeout_3539_ = lean_ctor_get(v_state_3218_, 4);
lean_inc(v_headerTimeout_3539_);
v_response_3540_ = lean_ctor_get(v_state_3218_, 5);
lean_inc_ref(v_response_3540_);
v_requiresData_3541_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9);
v_expectData_3542_ = lean_ctor_get(v_state_3218_, 7);
lean_inc(v_expectData_3542_);
v_pendingHead_3543_ = lean_ctor_get(v_state_3218_, 8);
lean_inc(v_pendingHead_3543_);
lean_dec_ref(v_state_3218_);
v___x_3544_ = 0;
v___x_3545_ = lean_box(v_requiresData_3541_);
v___x_3546_ = lean_box(v___x_3544_);
v___f_3547_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3547_, 0, v_requestStream_3536_);
lean_closure_set(v___f_3547_, 1, v_keepAliveTimeout_3537_);
lean_closure_set(v___f_3547_, 2, v_currentTimeout_3538_);
lean_closure_set(v___f_3547_, 3, v_headerTimeout_3539_);
lean_closure_set(v___f_3547_, 4, v_response_3540_);
lean_closure_set(v___f_3547_, 5, v___x_3545_);
lean_closure_set(v___f_3547_, 6, v_expectData_3542_);
lean_closure_set(v___f_3547_, 7, v___x_3546_);
lean_closure_set(v___f_3547_, 8, v_pendingHead_3543_);
v___f_3548_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3548_, 0, v___f_3547_);
v___f_3549_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3550_ = 1;
v___x_3551_ = lean_box(v___x_3544_);
v___x_3552_ = lean_box(v___x_3550_);
lean_inc_ref(v_inst_3214_);
lean_inc_ref(v___f_3548_);
v___f_3553_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 10, 8);
lean_closure_set(v___f_3553_, 0, v___x_3551_);
lean_closure_set(v___f_3553_, 1, v___f_3548_);
lean_closure_set(v___f_3553_, 2, v___x_3552_);
lean_closure_set(v___f_3553_, 3, v_inst_3213_);
lean_closure_set(v___f_3553_, 4, v_handler_3215_);
lean_closure_set(v___f_3553_, 5, v_inst_3214_);
lean_closure_set(v___f_3553_, 6, v___f_3549_);
lean_closure_set(v___f_3553_, 7, v___f_3548_);
v___x_3554_ = lean_unsigned_to_nat(0u);
v___x_3555_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3214_, v_config_3216_, v_machine_3511_, v_a_3535_);
v___x_3556_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3554_, v___x_3544_, v___x_3555_, v___f_3553_);
return v___x_3556_;
}
}
}
case 4:
{
lean_object* v_onFailure_3557_; lean_object* v___f_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
lean_dec_ref(v_config_3216_);
lean_dec_ref(v_inst_3214_);
v_onFailure_3557_ = lean_ctor_get(v_inst_3213_, 2);
lean_inc_ref(v_onFailure_3557_);
lean_dec_ref(v_inst_3213_);
v___f_3558_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 3, 1);
lean_closure_set(v___f_3558_, 0, v_state_3218_);
v___x_3559_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2);
v___x_3560_ = lean_unsigned_to_nat(0u);
v___x_3561_ = 0;
v___x_3562_ = lean_apply_3(v_onFailure_3557_, v_handler_3215_, v___x_3559_, lean_box(0));
v___x_3563_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3560_, v___x_3561_, v___x_3562_, v___f_3558_);
return v___x_3563_;
}
case 5:
{
lean_object* v_machine_3564_; lean_object* v_requestStream_3565_; lean_object* v_keepAliveTimeout_3566_; lean_object* v_currentTimeout_3567_; lean_object* v_headerTimeout_3568_; lean_object* v_response_3569_; lean_object* v_respStream_3570_; uint8_t v_requiresData_3571_; lean_object* v_expectData_3572_; lean_object* v_pendingHead_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3587_; 
lean_dec_ref(v_config_3216_);
lean_dec(v_handler_3215_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_inst_3213_);
v_machine_3564_ = lean_ctor_get(v_state_3218_, 0);
v_requestStream_3565_ = lean_ctor_get(v_state_3218_, 1);
v_keepAliveTimeout_3566_ = lean_ctor_get(v_state_3218_, 2);
v_currentTimeout_3567_ = lean_ctor_get(v_state_3218_, 3);
v_headerTimeout_3568_ = lean_ctor_get(v_state_3218_, 4);
v_response_3569_ = lean_ctor_get(v_state_3218_, 5);
v_respStream_3570_ = lean_ctor_get(v_state_3218_, 6);
v_requiresData_3571_ = lean_ctor_get_uint8(v_state_3218_, sizeof(void*)*9);
v_expectData_3572_ = lean_ctor_get(v_state_3218_, 7);
v_pendingHead_3573_ = lean_ctor_get(v_state_3218_, 8);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_state_3218_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3575_ = v_state_3218_;
v_isShared_3576_ = v_isSharedCheck_3587_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_pendingHead_3573_);
lean_inc(v_expectData_3572_);
lean_inc(v_respStream_3570_);
lean_inc(v_response_3569_);
lean_inc(v_headerTimeout_3568_);
lean_inc(v_currentTimeout_3567_);
lean_inc(v_keepAliveTimeout_3566_);
lean_inc(v_requestStream_3565_);
lean_inc(v_machine_3564_);
lean_dec(v_state_3218_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3587_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; lean_object* v___x_3581_; 
v___x_3577_ = lean_box(55);
v___x_3578_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3564_, v___x_3577_);
v___x_3579_ = 0;
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3578_);
v___x_3581_ = v___x_3575_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_requestStream_3565_);
lean_ctor_set(v_reuseFailAlloc_3586_, 2, v_keepAliveTimeout_3566_);
lean_ctor_set(v_reuseFailAlloc_3586_, 3, v_currentTimeout_3567_);
lean_ctor_set(v_reuseFailAlloc_3586_, 4, v_headerTimeout_3568_);
lean_ctor_set(v_reuseFailAlloc_3586_, 5, v_response_3569_);
lean_ctor_set(v_reuseFailAlloc_3586_, 6, v_respStream_3570_);
lean_ctor_set(v_reuseFailAlloc_3586_, 7, v_expectData_3572_);
lean_ctor_set(v_reuseFailAlloc_3586_, 8, v_pendingHead_3573_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, sizeof(void*)*9, v_requiresData_3571_);
v___x_3581_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
lean_ctor_set_uint8(v___x_3581_, sizeof(void*)*9 + 1, v___x_3579_);
v___x_3582_ = lean_box(v___x_3579_);
v___x_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3581_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
v___x_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
v___x_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
return v___x_3585_;
}
}
}
default: 
{
uint8_t v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
lean_dec_ref(v_config_3216_);
lean_dec(v_handler_3215_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_inst_3213_);
v___x_3588_ = 1;
v___x_3589_ = lean_box(v___x_3588_);
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v_state_3218_);
lean_ctor_set(v___x_3590_, 1, v___x_3589_);
v___x_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3590_);
v___x_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
return v___x_3592_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3593_, lean_object* v_inst_3594_, lean_object* v_handler_3595_, lean_object* v_config_3596_, lean_object* v_event_3597_, lean_object* v_state_3598_, lean_object* v_a_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3593_, v_inst_3594_, v_handler_3595_, v_config_3596_, v_event_3597_, v_state_3598_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3601_, lean_object* v_00_u03b2_3602_, lean_object* v_inst_3603_, lean_object* v_inst_3604_, lean_object* v_handler_3605_, lean_object* v_config_3606_, lean_object* v_event_3607_, lean_object* v_state_3608_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3603_, v_inst_3604_, v_handler_3605_, v_config_3606_, v_event_3607_, v_state_3608_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3611_, lean_object* v_00_u03b2_3612_, lean_object* v_inst_3613_, lean_object* v_inst_3614_, lean_object* v_handler_3615_, lean_object* v_config_3616_, lean_object* v_event_3617_, lean_object* v_state_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3611_, v_00_u03b2_3612_, v_inst_3613_, v_inst_3614_, v_handler_3615_, v_config_3616_, v_event_3617_, v_state_3618_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3621_, uint8_t v_handlerDispatched_3622_, lean_object* v_keepAliveTimeout_3623_, lean_object* v_respStream_3624_, lean_object* v_headerTimeout_3625_, lean_object* v_currentTimeout_3626_, lean_object* v_expectData_3627_, lean_object* v_response_3628_, lean_object* v_socket_3629_, uint8_t v_requiresData_3630_, uint8_t v_sentMessage_3631_, lean_object* v_reader_3632_, uint8_t v_requestBodyInterested_3633_, lean_object* v_requestBody_3634_){
_start:
{
lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3648_; 
if (v_requiresData_3630_ == 0)
{
if (v_handlerDispatched_3622_ == 0)
{
goto v___jp_3651_;
}
else
{
if (lean_obj_tag(v_respStream_3624_) == 0)
{
if (v_sentMessage_3631_ == 0)
{
lean_object* v_state_3655_; 
v_state_3655_ = lean_ctor_get(v_reader_3632_, 0);
if (lean_obj_tag(v_state_3655_) == 2)
{
if (v_requestBodyInterested_3633_ == 0)
{
lean_dec(v_socket_3629_);
goto v___jp_3653_;
}
else
{
goto v___jp_3651_;
}
}
else
{
lean_dec(v_socket_3629_);
goto v___jp_3653_;
}
}
else
{
goto v___jp_3651_;
}
}
else
{
goto v___jp_3651_;
}
}
}
else
{
goto v___jp_3651_;
}
v___jp_3636_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3644_, 0, v___y_3638_);
lean_ctor_set(v___x_3644_, 1, v___y_3642_);
lean_ctor_set(v___x_3644_, 2, v___y_3643_);
lean_ctor_set(v___x_3644_, 3, v___y_3639_);
lean_ctor_set(v___x_3644_, 4, v_requestBody_3634_);
lean_ctor_set(v___x_3644_, 5, v___y_3641_);
lean_ctor_set(v___x_3644_, 6, v___y_3637_);
lean_ctor_set(v___x_3644_, 7, v___y_3640_);
lean_ctor_set(v___x_3644_, 8, v_connectionContext_3621_);
v___x_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
v___x_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
return v___x_3646_;
}
v___jp_3647_:
{
if (v_handlerDispatched_3622_ == 0)
{
lean_object* v___x_3649_; 
lean_dec_ref(v_response_3628_);
v___x_3649_ = lean_box(0);
v___y_3637_ = v_keepAliveTimeout_3623_;
v___y_3638_ = v___y_3648_;
v___y_3639_ = v_respStream_3624_;
v___y_3640_ = v_headerTimeout_3625_;
v___y_3641_ = v_currentTimeout_3626_;
v___y_3642_ = v_expectData_3627_;
v___y_3643_ = v___x_3649_;
goto v___jp_3636_;
}
else
{
lean_object* v___x_3650_; 
v___x_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3650_, 0, v_response_3628_);
v___y_3637_ = v_keepAliveTimeout_3623_;
v___y_3638_ = v___y_3648_;
v___y_3639_ = v_respStream_3624_;
v___y_3640_ = v_headerTimeout_3625_;
v___y_3641_ = v_currentTimeout_3626_;
v___y_3642_ = v_expectData_3627_;
v___y_3643_ = v___x_3650_;
goto v___jp_3636_;
}
}
v___jp_3651_:
{
lean_object* v___x_3652_; 
v___x_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3652_, 0, v_socket_3629_);
v___y_3648_ = v___x_3652_;
goto v___jp_3647_;
}
v___jp_3653_:
{
lean_object* v___x_3654_; 
v___x_3654_ = lean_box(0);
v___y_3648_ = v___x_3654_;
goto v___jp_3647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3656_, lean_object* v_handlerDispatched_3657_, lean_object* v_keepAliveTimeout_3658_, lean_object* v_respStream_3659_, lean_object* v_headerTimeout_3660_, lean_object* v_currentTimeout_3661_, lean_object* v_expectData_3662_, lean_object* v_response_3663_, lean_object* v_socket_3664_, lean_object* v_requiresData_3665_, lean_object* v_sentMessage_3666_, lean_object* v_reader_3667_, lean_object* v_requestBodyInterested_3668_, lean_object* v_requestBody_3669_, lean_object* v___y_3670_){
_start:
{
uint8_t v_handlerDispatched_boxed_3671_; uint8_t v_requiresData_boxed_3672_; uint8_t v_sentMessage_boxed_3673_; uint8_t v_requestBodyInterested_boxed_3674_; lean_object* v_res_3675_; 
v_handlerDispatched_boxed_3671_ = lean_unbox(v_handlerDispatched_3657_);
v_requiresData_boxed_3672_ = lean_unbox(v_requiresData_3665_);
v_sentMessage_boxed_3673_ = lean_unbox(v_sentMessage_3666_);
v_requestBodyInterested_boxed_3674_ = lean_unbox(v_requestBodyInterested_3668_);
v_res_3675_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3656_, v_handlerDispatched_boxed_3671_, v_keepAliveTimeout_3658_, v_respStream_3659_, v_headerTimeout_3660_, v_currentTimeout_3661_, v_expectData_3662_, v_response_3663_, v_socket_3664_, v_requiresData_boxed_3672_, v_sentMessage_boxed_3673_, v_reader_3667_, v_requestBodyInterested_boxed_3674_, v_requestBody_3669_);
lean_dec_ref(v_reader_3667_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3676_, lean_object* v_x_3677_){
_start:
{
if (lean_obj_tag(v_x_3677_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3687_; 
lean_dec_ref(v___f_3676_);
v_a_3679_ = lean_ctor_get(v_x_3677_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_x_3677_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3681_ = v_x_3677_;
v_isShared_3682_ = v_isSharedCheck_3687_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v_x_3677_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3687_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; 
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
return v___x_3685_;
}
}
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3689_; 
v_a_3688_ = lean_ctor_get(v_x_3677_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v_x_3677_, 1);
v___x_3689_ = lean_apply_2(v___f_3676_, v_a_3688_, lean_box(0));
return v___x_3689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3690_, lean_object* v_x_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3690_, v_x_3691_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3698_, uint8_t v_handlerDispatched_3699_, lean_object* v_keepAliveTimeout_3700_, lean_object* v_respStream_3701_, lean_object* v_headerTimeout_3702_, lean_object* v_currentTimeout_3703_, lean_object* v_expectData_3704_, lean_object* v_response_3705_, lean_object* v_socket_3706_, uint8_t v_requiresData_3707_, uint8_t v_sentMessage_3708_, lean_object* v_reader_3709_, uint8_t v_pullBodyStalled_3710_, uint8_t v_requestBodyOpen_3711_, lean_object* v_requestStream_3712_, uint8_t v_requestBodyInterested_3713_){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___f_3719_; lean_object* v___f_3720_; uint8_t v___y_3722_; 
v___x_3715_ = lean_box(v_handlerDispatched_3699_);
v___x_3716_ = lean_box(v_requiresData_3707_);
v___x_3717_ = lean_box(v_sentMessage_3708_);
v___x_3718_ = lean_box(v_requestBodyInterested_3713_);
lean_inc_ref(v_reader_3709_);
v___f_3719_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3719_, 0, v_connectionContext_3698_);
lean_closure_set(v___f_3719_, 1, v___x_3715_);
lean_closure_set(v___f_3719_, 2, v_keepAliveTimeout_3700_);
lean_closure_set(v___f_3719_, 3, v_respStream_3701_);
lean_closure_set(v___f_3719_, 4, v_headerTimeout_3702_);
lean_closure_set(v___f_3719_, 5, v_currentTimeout_3703_);
lean_closure_set(v___f_3719_, 6, v_expectData_3704_);
lean_closure_set(v___f_3719_, 7, v_response_3705_);
lean_closure_set(v___f_3719_, 8, v_socket_3706_);
lean_closure_set(v___f_3719_, 9, v___x_3716_);
lean_closure_set(v___f_3719_, 10, v___x_3717_);
lean_closure_set(v___f_3719_, 11, v_reader_3709_);
lean_closure_set(v___f_3719_, 12, v___x_3718_);
v___f_3720_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3720_, 0, v___f_3719_);
if (v_sentMessage_3708_ == 0)
{
lean_object* v_state_3726_; 
v_state_3726_ = lean_ctor_get(v_reader_3709_, 0);
lean_inc(v_state_3726_);
lean_dec_ref(v_reader_3709_);
if (lean_obj_tag(v_state_3726_) == 2)
{
lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3737_; 
v_isSharedCheck_3737_ = !lean_is_exclusive(v_state_3726_);
if (v_isSharedCheck_3737_ == 0)
{
lean_object* v_unused_3738_; 
v_unused_3738_ = lean_ctor_get(v_state_3726_, 0);
lean_dec(v_unused_3738_);
v___x_3728_ = v_state_3726_;
v_isShared_3729_ = v_isSharedCheck_3737_;
goto v_resetjp_3727_;
}
else
{
lean_dec(v_state_3726_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3737_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
if (v_pullBodyStalled_3710_ == 0)
{
if (v_requestBodyOpen_3711_ == 0)
{
lean_del_object(v___x_3728_);
lean_dec_ref(v_requestStream_3712_);
v___y_3722_ = v_requestBodyOpen_3711_;
goto v___jp_3721_;
}
else
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
lean_ctor_set_tag(v___x_3728_, 1);
lean_ctor_set(v___x_3728_, 0, v_requestStream_3712_);
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_requestStream_3712_);
v___x_3731_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3732_ = lean_unsigned_to_nat(0u);
v___x_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
v___x_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
v___x_3735_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3732_, v_pullBodyStalled_3710_, v___x_3734_, v___f_3720_);
return v___x_3735_;
}
}
}
else
{
lean_del_object(v___x_3728_);
lean_dec_ref(v_requestStream_3712_);
v___y_3722_ = v_sentMessage_3708_;
goto v___jp_3721_;
}
}
}
else
{
lean_dec(v_state_3726_);
lean_dec_ref(v_requestStream_3712_);
v___y_3722_ = v_sentMessage_3708_;
goto v___jp_3721_;
}
}
else
{
uint8_t v___x_3739_; 
lean_dec_ref(v_requestStream_3712_);
lean_dec_ref(v_reader_3709_);
v___x_3739_ = 0;
v___y_3722_ = v___x_3739_;
goto v___jp_3721_;
}
v___jp_3721_:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3723_ = lean_unsigned_to_nat(0u);
v___x_3724_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3725_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3723_, v___y_3722_, v___x_3724_, v___f_3720_);
return v___x_3725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3740_ = _args[0];
lean_object* v_handlerDispatched_3741_ = _args[1];
lean_object* v_keepAliveTimeout_3742_ = _args[2];
lean_object* v_respStream_3743_ = _args[3];
lean_object* v_headerTimeout_3744_ = _args[4];
lean_object* v_currentTimeout_3745_ = _args[5];
lean_object* v_expectData_3746_ = _args[6];
lean_object* v_response_3747_ = _args[7];
lean_object* v_socket_3748_ = _args[8];
lean_object* v_requiresData_3749_ = _args[9];
lean_object* v_sentMessage_3750_ = _args[10];
lean_object* v_reader_3751_ = _args[11];
lean_object* v_pullBodyStalled_3752_ = _args[12];
lean_object* v_requestBodyOpen_3753_ = _args[13];
lean_object* v_requestStream_3754_ = _args[14];
lean_object* v_requestBodyInterested_3755_ = _args[15];
lean_object* v___y_3756_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3757_; uint8_t v_requiresData_boxed_3758_; uint8_t v_sentMessage_boxed_3759_; uint8_t v_pullBodyStalled_boxed_3760_; uint8_t v_requestBodyOpen_boxed_3761_; uint8_t v_requestBodyInterested_boxed_3762_; lean_object* v_res_3763_; 
v_handlerDispatched_boxed_3757_ = lean_unbox(v_handlerDispatched_3741_);
v_requiresData_boxed_3758_ = lean_unbox(v_requiresData_3749_);
v_sentMessage_boxed_3759_ = lean_unbox(v_sentMessage_3750_);
v_pullBodyStalled_boxed_3760_ = lean_unbox(v_pullBodyStalled_3752_);
v_requestBodyOpen_boxed_3761_ = lean_unbox(v_requestBodyOpen_3753_);
v_requestBodyInterested_boxed_3762_ = lean_unbox(v_requestBodyInterested_3755_);
v_res_3763_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3740_, v_handlerDispatched_boxed_3757_, v_keepAliveTimeout_3742_, v_respStream_3743_, v_headerTimeout_3744_, v_currentTimeout_3745_, v_expectData_3746_, v_response_3747_, v_socket_3748_, v_requiresData_boxed_3758_, v_sentMessage_boxed_3759_, v_reader_3751_, v_pullBodyStalled_boxed_3760_, v_requestBodyOpen_boxed_3761_, v_requestStream_3754_, v_requestBodyInterested_boxed_3762_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3764_, lean_object* v_x_3765_){
_start:
{
if (lean_obj_tag(v_x_3765_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v___f_3764_);
v_a_3767_ = lean_ctor_get(v_x_3765_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_x_3765_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3769_ = v_x_3765_;
v_isShared_3770_ = v_isSharedCheck_3775_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v_x_3765_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3775_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3773_; 
v___x_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
return v___x_3773_;
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3777_; 
v_a_3776_ = lean_ctor_get(v_x_3765_, 0);
lean_inc(v_a_3776_);
lean_dec_ref_known(v_x_3765_, 1);
v___x_3777_ = lean_apply_2(v___f_3764_, v_a_3776_, lean_box(0));
return v___x_3777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3778_, lean_object* v_x_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v_res_3781_; 
v_res_3781_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3778_, v_x_3779_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_3782_, uint8_t v_handlerDispatched_3783_, lean_object* v_keepAliveTimeout_3784_, lean_object* v_respStream_3785_, lean_object* v_headerTimeout_3786_, lean_object* v_currentTimeout_3787_, lean_object* v_expectData_3788_, lean_object* v_response_3789_, lean_object* v_socket_3790_, uint8_t v_requiresData_3791_, uint8_t v_sentMessage_3792_, lean_object* v_reader_3793_, uint8_t v_pullBodyStalled_3794_, lean_object* v_requestStream_3795_, uint8_t v_requestBodyOpen_3796_){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___f_3803_; lean_object* v___f_3804_; uint8_t v___y_3806_; 
v___x_3798_ = lean_box(v_handlerDispatched_3783_);
v___x_3799_ = lean_box(v_requiresData_3791_);
v___x_3800_ = lean_box(v_sentMessage_3792_);
v___x_3801_ = lean_box(v_pullBodyStalled_3794_);
v___x_3802_ = lean_box(v_requestBodyOpen_3796_);
lean_inc_ref(v_requestStream_3795_);
lean_inc_ref(v_reader_3793_);
v___f_3803_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3803_, 0, v_connectionContext_3782_);
lean_closure_set(v___f_3803_, 1, v___x_3798_);
lean_closure_set(v___f_3803_, 2, v_keepAliveTimeout_3784_);
lean_closure_set(v___f_3803_, 3, v_respStream_3785_);
lean_closure_set(v___f_3803_, 4, v_headerTimeout_3786_);
lean_closure_set(v___f_3803_, 5, v_currentTimeout_3787_);
lean_closure_set(v___f_3803_, 6, v_expectData_3788_);
lean_closure_set(v___f_3803_, 7, v_response_3789_);
lean_closure_set(v___f_3803_, 8, v_socket_3790_);
lean_closure_set(v___f_3803_, 9, v___x_3799_);
lean_closure_set(v___f_3803_, 10, v___x_3800_);
lean_closure_set(v___f_3803_, 11, v_reader_3793_);
lean_closure_set(v___f_3803_, 12, v___x_3801_);
lean_closure_set(v___f_3803_, 13, v___x_3802_);
lean_closure_set(v___f_3803_, 14, v_requestStream_3795_);
v___f_3804_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3804_, 0, v___f_3803_);
if (v_sentMessage_3792_ == 0)
{
lean_object* v_state_3812_; 
v_state_3812_ = lean_ctor_get(v_reader_3793_, 0);
lean_inc(v_state_3812_);
lean_dec_ref(v_reader_3793_);
if (lean_obj_tag(v_state_3812_) == 2)
{
lean_dec_ref_known(v_state_3812_, 1);
if (v_requestBodyOpen_3796_ == 0)
{
lean_dec_ref(v_requestStream_3795_);
v___y_3806_ = v_requestBodyOpen_3796_;
goto v___jp_3805_;
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = lean_unsigned_to_nat(0u);
v___x_3814_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3795_);
v___x_3815_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3813_, v_sentMessage_3792_, v___x_3814_, v___f_3804_);
return v___x_3815_;
}
}
else
{
lean_dec(v_state_3812_);
lean_dec_ref(v_requestStream_3795_);
v___y_3806_ = v_sentMessage_3792_;
goto v___jp_3805_;
}
}
else
{
uint8_t v___x_3816_; 
lean_dec_ref(v_requestStream_3795_);
lean_dec_ref(v_reader_3793_);
v___x_3816_ = 0;
v___y_3806_ = v___x_3816_;
goto v___jp_3805_;
}
v___jp_3805_:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3807_ = lean_unsigned_to_nat(0u);
v___x_3808_ = lean_box(v___y_3806_);
v___x_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
v___x_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
v___x_3811_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3807_, v___y_3806_, v___x_3810_, v___f_3804_);
return v___x_3811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_3817_, lean_object* v_handlerDispatched_3818_, lean_object* v_keepAliveTimeout_3819_, lean_object* v_respStream_3820_, lean_object* v_headerTimeout_3821_, lean_object* v_currentTimeout_3822_, lean_object* v_expectData_3823_, lean_object* v_response_3824_, lean_object* v_socket_3825_, lean_object* v_requiresData_3826_, lean_object* v_sentMessage_3827_, lean_object* v_reader_3828_, lean_object* v_pullBodyStalled_3829_, lean_object* v_requestStream_3830_, lean_object* v_requestBodyOpen_3831_, lean_object* v___y_3832_){
_start:
{
uint8_t v_handlerDispatched_boxed_3833_; uint8_t v_requiresData_boxed_3834_; uint8_t v_sentMessage_boxed_3835_; uint8_t v_pullBodyStalled_boxed_3836_; uint8_t v_requestBodyOpen_boxed_3837_; lean_object* v_res_3838_; 
v_handlerDispatched_boxed_3833_ = lean_unbox(v_handlerDispatched_3818_);
v_requiresData_boxed_3834_ = lean_unbox(v_requiresData_3826_);
v_sentMessage_boxed_3835_ = lean_unbox(v_sentMessage_3827_);
v_pullBodyStalled_boxed_3836_ = lean_unbox(v_pullBodyStalled_3829_);
v_requestBodyOpen_boxed_3837_ = lean_unbox(v_requestBodyOpen_3831_);
v_res_3838_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_3817_, v_handlerDispatched_boxed_3833_, v_keepAliveTimeout_3819_, v_respStream_3820_, v_headerTimeout_3821_, v_currentTimeout_3822_, v_expectData_3823_, v_response_3824_, v_socket_3825_, v_requiresData_boxed_3834_, v_sentMessage_boxed_3835_, v_reader_3828_, v_pullBodyStalled_boxed_3836_, v_requestStream_3830_, v_requestBodyOpen_boxed_3837_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3839_, lean_object* v___f_3840_, uint8_t v___x_3841_, lean_object* v_x_3842_){
_start:
{
uint8_t v___y_3845_; 
if (lean_obj_tag(v_x_3842_) == 0)
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3859_; 
lean_dec_ref(v___f_3840_);
v_a_3851_ = lean_ctor_get(v_x_3842_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v_x_3842_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3853_ = v_x_3842_;
v_isShared_3854_ = v_isSharedCheck_3859_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v_x_3842_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3859_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
return v___x_3857_;
}
}
}
else
{
lean_object* v_a_3860_; uint8_t v___x_3861_; 
v_a_3860_ = lean_ctor_get(v_x_3842_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v_x_3842_, 1);
v___x_3861_ = lean_unbox(v_a_3860_);
lean_dec(v_a_3860_);
if (v___x_3861_ == 0)
{
v___y_3845_ = v___x_3841_;
goto v___jp_3844_;
}
else
{
v___y_3845_ = v_sentMessage_3839_;
goto v___jp_3844_;
}
}
v___jp_3844_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3846_ = lean_unsigned_to_nat(0u);
v___x_3847_ = lean_box(v___y_3845_);
v___x_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
v___x_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3848_);
v___x_3850_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3846_, v_sentMessage_3839_, v___x_3849_, v___f_3840_);
return v___x_3850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_3862_, lean_object* v___f_3863_, lean_object* v___x_3864_, lean_object* v_x_3865_, lean_object* v___y_3866_){
_start:
{
uint8_t v_sentMessage_boxed_3867_; uint8_t v___x_2885__boxed_3868_; lean_object* v_res_3869_; 
v_sentMessage_boxed_3867_ = lean_unbox(v_sentMessage_3862_);
v___x_2885__boxed_3868_ = lean_unbox(v___x_3864_);
v_res_3869_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_3867_, v___f_3863_, v___x_2885__boxed_3868_, v_x_3865_);
return v_res_3869_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___f_3870_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_3871_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3872_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_3873_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_3873_, 0, lean_box(0));
lean_closure_set(v___x_3873_, 1, lean_box(0));
lean_closure_set(v___x_3873_, 2, v___x_3872_);
lean_closure_set(v___x_3873_, 3, lean_box(0));
lean_closure_set(v___x_3873_, 4, lean_box(0));
lean_closure_set(v___x_3873_, 5, v___x_3871_);
lean_closure_set(v___x_3873_, 6, v___f_3870_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_3874_, lean_object* v_connectionContext_3875_, lean_object* v_state_3876_){
_start:
{
lean_object* v_machine_3878_; lean_object* v_writer_3879_; lean_object* v_requestStream_3880_; lean_object* v_keepAliveTimeout_3881_; lean_object* v_currentTimeout_3882_; lean_object* v_headerTimeout_3883_; lean_object* v_response_3884_; lean_object* v_respStream_3885_; uint8_t v_requiresData_3886_; lean_object* v_expectData_3887_; uint8_t v_handlerDispatched_3888_; lean_object* v_reader_3889_; uint8_t v_pullBodyStalled_3890_; uint8_t v_sentMessage_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___f_3896_; lean_object* v___f_3897_; uint8_t v___y_3899_; 
v_machine_3878_ = lean_ctor_get(v_state_3876_, 0);
lean_inc_ref(v_machine_3878_);
v_writer_3879_ = lean_ctor_get(v_machine_3878_, 1);
lean_inc_ref(v_writer_3879_);
v_requestStream_3880_ = lean_ctor_get(v_state_3876_, 1);
lean_inc_ref_n(v_requestStream_3880_, 2);
v_keepAliveTimeout_3881_ = lean_ctor_get(v_state_3876_, 2);
lean_inc(v_keepAliveTimeout_3881_);
v_currentTimeout_3882_ = lean_ctor_get(v_state_3876_, 3);
lean_inc(v_currentTimeout_3882_);
v_headerTimeout_3883_ = lean_ctor_get(v_state_3876_, 4);
lean_inc(v_headerTimeout_3883_);
v_response_3884_ = lean_ctor_get(v_state_3876_, 5);
lean_inc_ref(v_response_3884_);
v_respStream_3885_ = lean_ctor_get(v_state_3876_, 6);
lean_inc(v_respStream_3885_);
v_requiresData_3886_ = lean_ctor_get_uint8(v_state_3876_, sizeof(void*)*9);
v_expectData_3887_ = lean_ctor_get(v_state_3876_, 7);
lean_inc(v_expectData_3887_);
v_handlerDispatched_3888_ = lean_ctor_get_uint8(v_state_3876_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_3876_);
v_reader_3889_ = lean_ctor_get(v_machine_3878_, 0);
lean_inc_ref_n(v_reader_3889_, 2);
v_pullBodyStalled_3890_ = lean_ctor_get_uint8(v_machine_3878_, sizeof(void*)*6 + 1);
lean_dec_ref(v_machine_3878_);
v_sentMessage_3891_ = lean_ctor_get_uint8(v_writer_3879_, sizeof(void*)*6);
lean_dec_ref(v_writer_3879_);
v___x_3892_ = lean_box(v_handlerDispatched_3888_);
v___x_3893_ = lean_box(v_requiresData_3886_);
v___x_3894_ = lean_box(v_sentMessage_3891_);
v___x_3895_ = lean_box(v_pullBodyStalled_3890_);
v___f_3896_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_3896_, 0, v_connectionContext_3875_);
lean_closure_set(v___f_3896_, 1, v___x_3892_);
lean_closure_set(v___f_3896_, 2, v_keepAliveTimeout_3881_);
lean_closure_set(v___f_3896_, 3, v_respStream_3885_);
lean_closure_set(v___f_3896_, 4, v_headerTimeout_3883_);
lean_closure_set(v___f_3896_, 5, v_currentTimeout_3882_);
lean_closure_set(v___f_3896_, 6, v_expectData_3887_);
lean_closure_set(v___f_3896_, 7, v_response_3884_);
lean_closure_set(v___f_3896_, 8, v_socket_3874_);
lean_closure_set(v___f_3896_, 9, v___x_3893_);
lean_closure_set(v___f_3896_, 10, v___x_3894_);
lean_closure_set(v___f_3896_, 11, v_reader_3889_);
lean_closure_set(v___f_3896_, 12, v___x_3895_);
lean_closure_set(v___f_3896_, 13, v_requestStream_3880_);
v___f_3897_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3897_, 0, v___f_3896_);
if (v_sentMessage_3891_ == 0)
{
lean_object* v_state_3905_; 
v_state_3905_ = lean_ctor_get(v_reader_3889_, 0);
lean_inc(v_state_3905_);
lean_dec_ref(v_reader_3889_);
if (lean_obj_tag(v_state_3905_) == 2)
{
uint8_t v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___f_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___f_3912_; lean_object* v___f_3913_; lean_object* v___x_3914_; lean_object* v___x_2535__overap_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
lean_dec_ref_known(v_state_3905_, 1);
v___x_3906_ = 1;
v___x_3907_ = lean_box(v_sentMessage_3891_);
v___x_3908_ = lean_box(v___x_3906_);
v___f_3909_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3909_, 0, v___x_3907_);
lean_closure_set(v___f_3909_, 1, v___f_3897_);
lean_closure_set(v___f_3909_, 2, v___x_3908_);
v___x_3910_ = lean_unsigned_to_nat(0u);
v___x_3911_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3912_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3913_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3914_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_2535__overap_3915_ = l_Std_Mutex_atomically___redArg(v___x_3911_, v___f_3912_, v___f_3913_, v_requestStream_3880_, v___x_3914_);
v___x_3916_ = lean_apply_1(v___x_2535__overap_3915_, lean_box(0));
v___x_3917_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3910_, v_sentMessage_3891_, v___x_3916_, v___f_3909_);
return v___x_3917_;
}
else
{
lean_dec(v_state_3905_);
lean_dec_ref(v_requestStream_3880_);
v___y_3899_ = v_sentMessage_3891_;
goto v___jp_3898_;
}
}
else
{
uint8_t v___x_3918_; 
lean_dec_ref(v_reader_3889_);
lean_dec_ref(v_requestStream_3880_);
v___x_3918_ = 0;
v___y_3899_ = v___x_3918_;
goto v___jp_3898_;
}
v___jp_3898_:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3900_ = lean_unsigned_to_nat(0u);
v___x_3901_ = lean_box(v___y_3899_);
v___x_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3901_);
v___x_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
v___x_3904_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3900_, v___y_3899_, v___x_3903_, v___f_3897_);
return v___x_3904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_3919_, lean_object* v_connectionContext_3920_, lean_object* v_state_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3919_, v_connectionContext_3920_, v_state_3921_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_3924_, lean_object* v_00_u03b2_3925_, lean_object* v_inst_3926_, lean_object* v_socket_3927_, lean_object* v_connectionContext_3928_, lean_object* v_state_3929_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3927_, v_connectionContext_3928_, v_state_3929_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_3932_, lean_object* v_00_u03b2_3933_, lean_object* v_inst_3934_, lean_object* v_socket_3935_, lean_object* v_connectionContext_3936_, lean_object* v_state_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_3932_, v_00_u03b2_3933_, v_inst_3934_, v_socket_3935_, v_connectionContext_3936_, v_state_3937_);
lean_dec_ref(v_inst_3934_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_3940_){
_start:
{
if (lean_obj_tag(v_x_3940_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3950_; 
v_a_3942_ = lean_ctor_get(v_x_3940_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v_x_3940_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3944_ = v_x_3940_;
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v_x_3940_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
lean_object* v___x_3948_; 
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3947_);
return v___x_3948_;
}
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3960_; 
v_a_3951_ = lean_ctor_get(v_x_3940_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v_x_3940_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3953_ = v_x_3940_;
v_isShared_3954_ = v_isSharedCheck_3960_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v_x_3940_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3960_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3955_; lean_object* v___x_3957_; 
v___x_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3955_, 0, v_a_3951_);
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 0, v___x_3955_);
v___x_3957_ = v___x_3953_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3955_);
v___x_3957_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
lean_object* v___x_3958_; 
v___x_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
return v___x_3958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_3961_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_3968_){
_start:
{
if (lean_obj_tag(v_x_3968_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3978_; 
v_a_3970_ = lean_ctor_get(v_x_3968_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v_x_3968_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3972_ = v_x_3968_;
v_isShared_3973_ = v_isSharedCheck_3978_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v_x_3968_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3978_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3976_; 
v___x_3976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
return v___x_3976_;
}
}
}
else
{
lean_object* v___x_3979_; 
lean_dec_ref_known(v_x_3968_, 1);
v___x_3979_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1));
return v___x_3979_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_3980_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_onFailure_3983_, lean_object* v_handler_3984_, lean_object* v___f_3985_, lean_object* v_x_3986_){
_start:
{
if (lean_obj_tag(v_x_3986_) == 0)
{
lean_object* v_a_3988_; lean_object* v___x_3989_; uint8_t v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v_a_3988_ = lean_ctor_get(v_x_3986_, 0);
lean_inc(v_a_3988_);
lean_dec_ref_known(v_x_3986_, 1);
v___x_3989_ = lean_unsigned_to_nat(0u);
v___x_3990_ = 0;
v___x_3991_ = lean_apply_3(v_onFailure_3983_, v_handler_3984_, v_a_3988_, lean_box(0));
v___x_3992_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3989_, v___x_3990_, v___x_3991_, v___f_3985_);
return v___x_3992_;
}
else
{
lean_object* v___x_3993_; 
lean_dec_ref(v___f_3985_);
lean_dec(v_handler_3984_);
lean_dec_ref(v_onFailure_3983_);
v___x_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3993_, 0, v_x_3986_);
return v___x_3993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_onFailure_3994_, lean_object* v_handler_3995_, lean_object* v___f_3996_, lean_object* v_x_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_onFailure_3994_, v_handler_3995_, v___f_3996_, v_x_3997_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_x_4000_){
_start:
{
if (lean_obj_tag(v_x_4000_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4010_; 
v_a_4002_ = lean_ctor_get(v_x_4000_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v_x_4000_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4004_ = v_x_4000_;
v_isShared_4005_ = v_isSharedCheck_4010_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v_x_4000_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4010_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4008_; 
v___x_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
return v___x_4008_;
}
}
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4029_; 
v_a_4011_ = lean_ctor_get(v_x_4000_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v_x_4000_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4013_ = v_x_4000_;
v_isShared_4014_ = v_isSharedCheck_4029_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v_x_4000_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4029_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v_snd_4015_; uint8_t v___x_4016_; 
v_snd_4015_ = lean_ctor_get(v_a_4011_, 1);
v___x_4016_ = lean_unbox(v_snd_4015_);
if (v___x_4016_ == 0)
{
lean_object* v_fst_4017_; lean_object* v___x_4018_; lean_object* v___x_4020_; 
v_fst_4017_ = lean_ctor_get(v_a_4011_, 0);
lean_inc(v_fst_4017_);
lean_dec(v_a_4011_);
v___x_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4018_, 0, v_fst_4017_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4018_);
v___x_4020_ = v___x_4013_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4018_);
v___x_4020_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
lean_object* v___x_4021_; 
v___x_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4020_);
return v___x_4021_;
}
}
else
{
lean_object* v_fst_4023_; lean_object* v___x_4024_; lean_object* v___x_4026_; 
v_fst_4023_ = lean_ctor_get(v_a_4011_, 0);
lean_inc(v_fst_4023_);
lean_dec(v_a_4011_);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v_fst_4023_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4024_);
v___x_4026_ = v___x_4013_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4024_);
v___x_4026_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
lean_object* v___x_4027_; 
v___x_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4026_);
return v___x_4027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_x_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_x_4030_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4033_, lean_object* v_socket_4034_, lean_object* v_____r_4035_){
_start:
{
lean_object* v_val_4038_; lean_object* v_close_4040_; lean_object* v___x_4041_; 
v_close_4040_ = lean_ctor_get(v_inst_4033_, 3);
lean_inc_ref(v_close_4040_);
lean_dec_ref(v_inst_4033_);
v___x_4041_ = lean_apply_2(v_close_4040_, v_socket_4034_, lean_box(0));
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4041_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4041_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
lean_ctor_set_tag(v___x_4044_, 1);
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
v_val_4038_ = v___x_4047_;
goto v___jp_4037_;
}
}
}
else
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
v_a_4050_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_4041_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4041_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
lean_ctor_set_tag(v___x_4052_, 0);
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
v_val_4038_ = v___x_4055_;
goto v___jp_4037_;
}
}
}
v___jp_4037_:
{
lean_object* v___x_4039_; 
v___x_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4039_, 0, v_val_4038_);
return v___x_4039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4058_, lean_object* v_socket_4059_, lean_object* v_____r_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4058_, v_socket_4059_, v_____r_4060_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4063_, lean_object* v_x_4064_){
_start:
{
if (lean_obj_tag(v_x_4064_) == 0)
{
lean_object* v___x_4066_; 
lean_dec_ref(v___f_4063_);
v___x_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4066_, 0, v_x_4064_);
return v___x_4066_;
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4068_; 
v_a_4067_ = lean_ctor_get(v_x_4064_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v_x_4064_, 1);
v___x_4068_ = lean_apply_2(v___f_4063_, v_a_4067_, lean_box(0));
return v___x_4068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4069_, lean_object* v_x_4070_, lean_object* v___y_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4069_, v_x_4070_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4073_, lean_object* v_val_4074_, lean_object* v___f_4075_, lean_object* v___f_4076_, lean_object* v_x_4077_){
_start:
{
if (lean_obj_tag(v_x_4077_) == 0)
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4087_; 
lean_dec_ref(v___f_4076_);
lean_dec_ref(v___f_4075_);
lean_dec(v_val_4074_);
lean_dec_ref(v_close_4073_);
v_a_4079_ = lean_ctor_get(v_x_4077_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_x_4077_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4081_ = v_x_4077_;
v_isShared_4082_ = v_isSharedCheck_4087_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v_x_4077_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4087_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
lean_object* v___x_4085_; 
v___x_4085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
return v___x_4085_;
}
}
}
else
{
lean_object* v_a_4088_; uint8_t v___x_4089_; 
v_a_4088_ = lean_ctor_get(v_x_4077_, 0);
lean_inc(v_a_4088_);
lean_dec_ref_known(v_x_4077_, 1);
v___x_4089_ = lean_unbox(v_a_4088_);
if (v___x_4089_ == 0)
{
lean_object* v___x_4090_; lean_object* v___x_4091_; uint8_t v___x_4092_; lean_object* v___x_4093_; 
lean_dec_ref(v___f_4076_);
v___x_4090_ = lean_unsigned_to_nat(0u);
v___x_4091_ = lean_apply_2(v_close_4073_, v_val_4074_, lean_box(0));
v___x_4092_ = lean_unbox(v_a_4088_);
lean_dec(v_a_4088_);
v___x_4093_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4090_, v___x_4092_, v___x_4091_, v___f_4075_);
return v___x_4093_;
}
else
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
lean_dec(v_a_4088_);
lean_dec_ref(v___f_4075_);
lean_dec(v_val_4074_);
lean_dec_ref(v_close_4073_);
v___x_4094_ = lean_box(0);
v___x_4095_ = lean_apply_2(v___f_4076_, v___x_4094_, lean_box(0));
return v___x_4095_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4096_, lean_object* v_val_4097_, lean_object* v___f_4098_, lean_object* v___f_4099_, lean_object* v_x_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4096_, v_val_4097_, v___f_4098_, v___f_4099_, v_x_4100_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4103_, lean_object* v_responseBodyInstance_4104_, lean_object* v___f_4105_, lean_object* v___f_4106_, lean_object* v_____r_4107_){
_start:
{
if (lean_obj_tag(v_respStream_4103_) == 1)
{
lean_object* v_val_4109_; lean_object* v_close_4110_; lean_object* v_isClosed_4111_; lean_object* v___f_4112_; lean_object* v___x_4113_; uint8_t v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v_val_4109_ = lean_ctor_get(v_respStream_4103_, 0);
lean_inc_n(v_val_4109_, 2);
lean_dec_ref_known(v_respStream_4103_, 1);
v_close_4110_ = lean_ctor_get(v_responseBodyInstance_4104_, 1);
lean_inc_ref(v_close_4110_);
v_isClosed_4111_ = lean_ctor_get(v_responseBodyInstance_4104_, 2);
lean_inc_ref(v_isClosed_4111_);
lean_dec_ref(v_responseBodyInstance_4104_);
v___f_4112_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4112_, 0, v_close_4110_);
lean_closure_set(v___f_4112_, 1, v_val_4109_);
lean_closure_set(v___f_4112_, 2, v___f_4105_);
lean_closure_set(v___f_4112_, 3, v___f_4106_);
v___x_4113_ = lean_unsigned_to_nat(0u);
v___x_4114_ = 0;
v___x_4115_ = lean_apply_2(v_isClosed_4111_, v_val_4109_, lean_box(0));
v___x_4116_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4113_, v___x_4114_, v___x_4115_, v___f_4112_);
return v___x_4116_;
}
else
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
lean_dec_ref(v___f_4105_);
lean_dec_ref(v_responseBodyInstance_4104_);
lean_dec(v_respStream_4103_);
v___x_4117_ = lean_box(0);
v___x_4118_ = lean_apply_2(v___f_4106_, v___x_4117_, lean_box(0));
return v___x_4118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4119_, lean_object* v_responseBodyInstance_4120_, lean_object* v___f_4121_, lean_object* v___f_4122_, lean_object* v_____r_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4119_, v_responseBodyInstance_4120_, v___f_4121_, v___f_4122_, v_____r_4123_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4126_, lean_object* v___f_4127_, lean_object* v___f_4128_, lean_object* v_x_4129_){
_start:
{
if (lean_obj_tag(v_x_4129_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4139_; 
lean_dec_ref(v___f_4128_);
lean_dec_ref(v___f_4127_);
lean_dec_ref(v_requestStream_4126_);
v_a_4131_ = lean_ctor_get(v_x_4129_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v_x_4129_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4133_ = v_x_4129_;
v_isShared_4134_ = v_isSharedCheck_4139_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v_x_4129_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4139_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4137_; 
v___x_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
return v___x_4137_;
}
}
}
else
{
lean_object* v_a_4140_; uint8_t v___x_4141_; 
v_a_4140_ = lean_ctor_get(v_x_4129_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v_x_4129_, 1);
v___x_4141_ = lean_unbox(v_a_4140_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4142_; lean_object* v___x_4143_; uint8_t v___x_4144_; lean_object* v___x_4145_; 
lean_dec_ref(v___f_4128_);
v___x_4142_ = lean_unsigned_to_nat(0u);
v___x_4143_ = l_Std_Http_Body_Stream_close(v_requestStream_4126_);
v___x_4144_ = lean_unbox(v_a_4140_);
lean_dec(v_a_4140_);
v___x_4145_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4142_, v___x_4144_, v___x_4143_, v___f_4127_);
return v___x_4145_;
}
else
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
lean_dec(v_a_4140_);
lean_dec_ref(v___f_4127_);
lean_dec_ref(v_requestStream_4126_);
v___x_4146_ = lean_box(0);
v___x_4147_ = lean_apply_2(v___f_4128_, v___x_4146_, lean_box(0));
return v___x_4147_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4148_, lean_object* v___f_4149_, lean_object* v___f_4150_, lean_object* v_x_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4148_, v___f_4149_, v___f_4150_, v_x_4151_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v_responseBodyInstance_4154_, lean_object* v___f_4155_, lean_object* v___f_4156_, lean_object* v___f_4157_, lean_object* v_x_4158_){
_start:
{
if (lean_obj_tag(v_x_4158_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4168_; 
lean_dec_ref(v___f_4157_);
lean_dec_ref(v___f_4156_);
lean_dec_ref(v___f_4155_);
lean_dec_ref(v_responseBodyInstance_4154_);
v_a_4160_ = lean_ctor_get(v_x_4158_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v_x_4158_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4162_ = v_x_4158_;
v_isShared_4163_ = v_isSharedCheck_4168_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v_x_4158_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4168_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
lean_object* v___x_4166_; 
v___x_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
return v___x_4166_;
}
}
}
else
{
lean_object* v_a_4169_; lean_object* v_requestStream_4170_; lean_object* v_respStream_4171_; lean_object* v___f_4172_; lean_object* v___f_4173_; lean_object* v___f_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; lean_object* v___x_4177_; lean_object* v___f_4178_; lean_object* v___f_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4531__overap_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v_a_4169_ = lean_ctor_get(v_x_4158_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v_x_4158_, 1);
v_requestStream_4170_ = lean_ctor_get(v_a_4169_, 1);
lean_inc_ref_n(v_requestStream_4170_, 2);
v_respStream_4171_ = lean_ctor_get(v_a_4169_, 6);
lean_inc(v_respStream_4171_);
lean_dec(v_a_4169_);
v___f_4172_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4172_, 0, v_respStream_4171_);
lean_closure_set(v___f_4172_, 1, v_responseBodyInstance_4154_);
lean_closure_set(v___f_4172_, 2, v___f_4155_);
lean_closure_set(v___f_4172_, 3, v___f_4156_);
lean_inc_ref(v___f_4172_);
v___f_4173_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4173_, 0, v___f_4172_);
v___f_4174_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4174_, 0, v_requestStream_4170_);
lean_closure_set(v___f_4174_, 1, v___f_4173_);
lean_closure_set(v___f_4174_, 2, v___f_4172_);
v___x_4175_ = lean_unsigned_to_nat(0u);
v___x_4176_ = 0;
v___x_4177_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4178_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4179_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4180_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4181_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4181_, 0, lean_box(0));
lean_closure_set(v___x_4181_, 1, lean_box(0));
lean_closure_set(v___x_4181_, 2, v___x_4177_);
lean_closure_set(v___x_4181_, 3, lean_box(0));
lean_closure_set(v___x_4181_, 4, lean_box(0));
lean_closure_set(v___x_4181_, 5, v___x_4180_);
lean_closure_set(v___x_4181_, 6, v___f_4157_);
v___x_4531__overap_4182_ = l_Std_Mutex_atomically___redArg(v___x_4177_, v___f_4178_, v___f_4179_, v_requestStream_4170_, v___x_4181_);
v___x_4183_ = lean_apply_1(v___x_4531__overap_4182_, lean_box(0));
v___x_4184_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4175_, v___x_4176_, v___x_4183_, v___f_4174_);
return v___x_4184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v_responseBodyInstance_4185_, lean_object* v___f_4186_, lean_object* v___f_4187_, lean_object* v___f_4188_, lean_object* v_x_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v_responseBodyInstance_4185_, v___f_4186_, v___f_4187_, v___f_4188_, v_x_4189_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4192_, lean_object* v_responseBodyInstance_4193_, lean_object* v_handler_4194_, lean_object* v_config_4195_, lean_object* v___x_4196_, uint8_t v___x_4197_, lean_object* v___f_4198_, lean_object* v_x_4199_){
_start:
{
if (lean_obj_tag(v_x_4199_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4209_; 
lean_dec_ref(v___f_4198_);
lean_dec_ref(v___x_4196_);
lean_dec_ref(v_config_4195_);
lean_dec(v_handler_4194_);
lean_dec_ref(v_responseBodyInstance_4193_);
lean_dec_ref(v_h_4192_);
v_a_4201_ = lean_ctor_get(v_x_4199_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v_x_4199_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4203_ = v_x_4199_;
v_isShared_4204_ = v_isSharedCheck_4209_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v_x_4199_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4209_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
lean_object* v___x_4207_; 
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
return v___x_4207_;
}
}
}
else
{
lean_object* v_a_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v_a_4210_ = lean_ctor_get(v_x_4199_, 0);
lean_inc(v_a_4210_);
lean_dec_ref_known(v_x_4199_, 1);
v___x_4211_ = lean_unsigned_to_nat(0u);
v___x_4212_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4192_, v_responseBodyInstance_4193_, v_handler_4194_, v_config_4195_, v_a_4210_, v___x_4196_);
v___x_4213_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4211_, v___x_4197_, v___x_4212_, v___f_4198_);
return v___x_4213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4214_, lean_object* v_responseBodyInstance_4215_, lean_object* v_handler_4216_, lean_object* v_config_4217_, lean_object* v___x_4218_, lean_object* v___x_4219_, lean_object* v___f_4220_, lean_object* v_x_4221_, lean_object* v___y_4222_){
_start:
{
uint8_t v___x_5197__boxed_4223_; lean_object* v_res_4224_; 
v___x_5197__boxed_4223_ = lean_unbox(v___x_4219_);
v_res_4224_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4214_, v_responseBodyInstance_4215_, v_handler_4216_, v_config_4217_, v___x_4218_, v___x_5197__boxed_4223_, v___f_4220_, v_x_4221_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4225_, lean_object* v_h_4226_, lean_object* v_responseBodyInstance_4227_, lean_object* v_config_4228_, lean_object* v_handler_4229_, uint8_t v___x_4230_, lean_object* v___f_4231_, lean_object* v_x_4232_){
_start:
{
if (lean_obj_tag(v_x_4232_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4242_; 
lean_dec_ref(v___f_4231_);
lean_dec(v_handler_4229_);
lean_dec_ref(v_config_4228_);
lean_dec_ref(v_responseBodyInstance_4227_);
lean_dec_ref(v_h_4226_);
lean_dec_ref(v_inst_4225_);
v_a_4234_ = lean_ctor_get(v_x_4232_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_x_4232_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4236_ = v_x_4232_;
v_isShared_4237_ = v_isSharedCheck_4242_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v_x_4232_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4242_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4240_; 
v___x_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
return v___x_4240_;
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v_a_4243_ = lean_ctor_get(v_x_4232_, 0);
lean_inc(v_a_4243_);
lean_dec_ref_known(v_x_4232_, 1);
v___x_4244_ = lean_unsigned_to_nat(0u);
v___x_4245_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4225_, v_h_4226_, v_responseBodyInstance_4227_, v_config_4228_, v_handler_4229_, v_a_4243_);
v___x_4246_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4244_, v___x_4230_, v___x_4245_, v___f_4231_);
return v___x_4246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4247_, lean_object* v_h_4248_, lean_object* v_responseBodyInstance_4249_, lean_object* v_config_4250_, lean_object* v_handler_4251_, lean_object* v___x_4252_, lean_object* v___f_4253_, lean_object* v_x_4254_, lean_object* v___y_4255_){
_start:
{
uint8_t v___x_5238__boxed_4256_; lean_object* v_res_4257_; 
v___x_5238__boxed_4256_ = lean_unbox(v___x_4252_);
v_res_4257_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4247_, v_h_4248_, v_responseBodyInstance_4249_, v_config_4250_, v_handler_4251_, v___x_5238__boxed_4256_, v___f_4253_, v_x_4254_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4258_, lean_object* v_h_4259_, lean_object* v_responseBodyInstance_4260_, lean_object* v_handler_4261_, lean_object* v_config_4262_, lean_object* v___f_4263_, lean_object* v_inst_4264_, lean_object* v_socket_4265_, lean_object* v_connectionContext_4266_, lean_object* v_x_4267_){
_start:
{
if (lean_obj_tag(v_x_4267_) == 0)
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4277_; 
lean_dec_ref(v_connectionContext_4266_);
lean_dec(v_socket_4265_);
lean_dec_ref(v_inst_4264_);
lean_dec_ref(v___f_4263_);
lean_dec_ref(v_config_4262_);
lean_dec(v_handler_4261_);
lean_dec_ref(v_responseBodyInstance_4260_);
lean_dec_ref(v_h_4259_);
v_a_4269_ = lean_ctor_get(v_x_4267_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v_x_4267_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4271_ = v_x_4267_;
v_isShared_4272_ = v_isSharedCheck_4277_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v_x_4267_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4277_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
lean_object* v___x_4275_; 
v___x_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4274_);
return v___x_4275_;
}
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4312_; 
v_a_4278_ = lean_ctor_get(v_x_4267_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v_x_4267_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4280_ = v_x_4267_;
v_isShared_4281_ = v_isSharedCheck_4312_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v_x_4267_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4312_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v_machine_4288_; lean_object* v_requestStream_4289_; lean_object* v_keepAliveTimeout_4290_; lean_object* v_currentTimeout_4291_; lean_object* v_headerTimeout_4292_; lean_object* v_response_4293_; lean_object* v_respStream_4294_; uint8_t v_requiresData_4295_; lean_object* v_expectData_4296_; uint8_t v_handlerDispatched_4297_; lean_object* v_pendingHead_4298_; 
v_machine_4288_ = lean_ctor_get(v_a_4278_, 0);
v_requestStream_4289_ = lean_ctor_get(v_a_4278_, 1);
v_keepAliveTimeout_4290_ = lean_ctor_get(v_a_4278_, 2);
v_currentTimeout_4291_ = lean_ctor_get(v_a_4278_, 3);
v_headerTimeout_4292_ = lean_ctor_get(v_a_4278_, 4);
v_response_4293_ = lean_ctor_get(v_a_4278_, 5);
v_respStream_4294_ = lean_ctor_get(v_a_4278_, 6);
v_requiresData_4295_ = lean_ctor_get_uint8(v_a_4278_, sizeof(void*)*9);
v_expectData_4296_ = lean_ctor_get(v_a_4278_, 7);
v_handlerDispatched_4297_ = lean_ctor_get_uint8(v_a_4278_, sizeof(void*)*9 + 1);
v_pendingHead_4298_ = lean_ctor_get(v_a_4278_, 8);
if (v_requiresData_4295_ == 0)
{
if (v_handlerDispatched_4297_ == 0)
{
if (lean_obj_tag(v_respStream_4294_) == 0)
{
lean_object* v_writer_4308_; uint8_t v_sentMessage_4309_; 
v_writer_4308_ = lean_ctor_get(v_machine_4288_, 1);
v_sentMessage_4309_ = lean_ctor_get_uint8(v_writer_4308_, sizeof(void*)*6);
if (v_sentMessage_4309_ == 0)
{
lean_object* v_reader_4310_; lean_object* v_state_4311_; 
v_reader_4310_ = lean_ctor_get(v_machine_4288_, 0);
v_state_4311_ = lean_ctor_get(v_reader_4310_, 0);
if (lean_obj_tag(v_state_4311_) == 2)
{
lean_inc(v_respStream_4294_);
lean_inc(v_pendingHead_4298_);
lean_inc(v_expectData_4296_);
lean_inc_ref(v_response_4293_);
lean_inc(v_headerTimeout_4292_);
lean_inc(v_currentTimeout_4291_);
lean_inc(v_keepAliveTimeout_4290_);
lean_inc_ref(v_requestStream_4289_);
lean_inc_ref(v_machine_4288_);
lean_del_object(v___x_4280_);
lean_dec(v_a_4278_);
goto v___jp_4299_;
}
else
{
lean_dec_ref(v_connectionContext_4266_);
lean_dec(v_socket_4265_);
lean_dec_ref(v_inst_4264_);
lean_dec_ref(v___f_4263_);
lean_dec_ref(v_config_4262_);
lean_dec(v_handler_4261_);
lean_dec_ref(v_responseBodyInstance_4260_);
lean_dec_ref(v_h_4259_);
goto v___jp_4282_;
}
}
else
{
lean_dec_ref(v_connectionContext_4266_);
lean_dec(v_socket_4265_);
lean_dec_ref(v_inst_4264_);
lean_dec_ref(v___f_4263_);
lean_dec_ref(v_config_4262_);
lean_dec(v_handler_4261_);
lean_dec_ref(v_responseBodyInstance_4260_);
lean_dec_ref(v_h_4259_);
goto v___jp_4282_;
}
}
else
{
lean_inc_ref(v_respStream_4294_);
lean_inc(v_pendingHead_4298_);
lean_inc(v_expectData_4296_);
lean_inc_ref(v_response_4293_);
lean_inc(v_headerTimeout_4292_);
lean_inc(v_currentTimeout_4291_);
lean_inc(v_keepAliveTimeout_4290_);
lean_inc_ref(v_requestStream_4289_);
lean_inc_ref(v_machine_4288_);
lean_del_object(v___x_4280_);
lean_dec(v_a_4278_);
goto v___jp_4299_;
}
}
else
{
lean_inc(v_pendingHead_4298_);
lean_inc(v_expectData_4296_);
lean_inc(v_respStream_4294_);
lean_inc_ref(v_response_4293_);
lean_inc(v_headerTimeout_4292_);
lean_inc(v_currentTimeout_4291_);
lean_inc(v_keepAliveTimeout_4290_);
lean_inc_ref(v_requestStream_4289_);
lean_inc_ref(v_machine_4288_);
lean_del_object(v___x_4280_);
lean_dec(v_a_4278_);
goto v___jp_4299_;
}
}
else
{
lean_inc(v_pendingHead_4298_);
lean_inc(v_expectData_4296_);
lean_inc(v_respStream_4294_);
lean_inc_ref(v_response_4293_);
lean_inc(v_headerTimeout_4292_);
lean_inc(v_currentTimeout_4291_);
lean_inc(v_keepAliveTimeout_4290_);
lean_inc_ref(v_requestStream_4289_);
lean_inc_ref(v_machine_4288_);
lean_del_object(v___x_4280_);
lean_dec(v_a_4278_);
goto v___jp_4299_;
}
v___jp_4282_:
{
lean_object* v___x_4283_; lean_object* v___x_4285_; 
v___x_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4283_, 0, v_a_4278_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 0, v___x_4283_);
v___x_4285_ = v___x_4280_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4283_);
v___x_4285_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
lean_object* v___x_4286_; 
v___x_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4285_);
return v___x_4286_;
}
}
v___jp_4299_:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___f_4302_; lean_object* v___x_4303_; lean_object* v___f_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4300_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4300_, 0, v_machine_4288_);
lean_ctor_set(v___x_4300_, 1, v_requestStream_4289_);
lean_ctor_set(v___x_4300_, 2, v_keepAliveTimeout_4290_);
lean_ctor_set(v___x_4300_, 3, v_currentTimeout_4291_);
lean_ctor_set(v___x_4300_, 4, v_headerTimeout_4292_);
lean_ctor_set(v___x_4300_, 5, v_response_4293_);
lean_ctor_set(v___x_4300_, 6, v_respStream_4294_);
lean_ctor_set(v___x_4300_, 7, v_expectData_4296_);
lean_ctor_set(v___x_4300_, 8, v_pendingHead_4298_);
lean_ctor_set_uint8(v___x_4300_, sizeof(void*)*9, v___x_4258_);
lean_ctor_set_uint8(v___x_4300_, sizeof(void*)*9 + 1, v_handlerDispatched_4297_);
v___x_4301_ = lean_box(v___x_4258_);
lean_inc_ref(v___x_4300_);
lean_inc_ref(v_config_4262_);
lean_inc(v_handler_4261_);
lean_inc_ref(v_responseBodyInstance_4260_);
lean_inc_ref(v_h_4259_);
v___f_4302_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4302_, 0, v_h_4259_);
lean_closure_set(v___f_4302_, 1, v_responseBodyInstance_4260_);
lean_closure_set(v___f_4302_, 2, v_handler_4261_);
lean_closure_set(v___f_4302_, 3, v_config_4262_);
lean_closure_set(v___f_4302_, 4, v___x_4300_);
lean_closure_set(v___f_4302_, 5, v___x_4301_);
lean_closure_set(v___f_4302_, 6, v___f_4263_);
v___x_4303_ = lean_box(v___x_4258_);
v___f_4304_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4304_, 0, v_inst_4264_);
lean_closure_set(v___f_4304_, 1, v_h_4259_);
lean_closure_set(v___f_4304_, 2, v_responseBodyInstance_4260_);
lean_closure_set(v___f_4304_, 3, v_config_4262_);
lean_closure_set(v___f_4304_, 4, v_handler_4261_);
lean_closure_set(v___f_4304_, 5, v___x_4303_);
lean_closure_set(v___f_4304_, 6, v___f_4302_);
v___x_4305_ = lean_unsigned_to_nat(0u);
v___x_4306_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4265_, v_connectionContext_4266_, v___x_4300_);
v___x_4307_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4305_, v___x_4258_, v___x_4306_, v___f_4304_);
return v___x_4307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4313_, lean_object* v_h_4314_, lean_object* v_responseBodyInstance_4315_, lean_object* v_handler_4316_, lean_object* v_config_4317_, lean_object* v___f_4318_, lean_object* v_inst_4319_, lean_object* v_socket_4320_, lean_object* v_connectionContext_4321_, lean_object* v_x_4322_, lean_object* v___y_4323_){
_start:
{
uint8_t v___x_5278__boxed_4324_; lean_object* v_res_4325_; 
v___x_5278__boxed_4324_ = lean_unbox(v___x_4313_);
v_res_4325_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5278__boxed_4324_, v_h_4314_, v_responseBodyInstance_4315_, v_handler_4316_, v_config_4317_, v___f_4318_, v_inst_4319_, v_socket_4320_, v_connectionContext_4321_, v_x_4322_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4326_, lean_object* v_handler_4327_, lean_object* v_extensions_4328_, lean_object* v_connectionContext_4329_, uint8_t v___x_4330_, lean_object* v___f_4331_, lean_object* v_x_4332_){
_start:
{
if (lean_obj_tag(v_x_4332_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4342_; 
lean_dec_ref(v___f_4331_);
lean_dec_ref(v_connectionContext_4329_);
lean_dec(v_extensions_4328_);
lean_dec(v_handler_4327_);
lean_dec_ref(v_h_4326_);
v_a_4334_ = lean_ctor_get(v_x_4332_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v_x_4332_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4336_ = v_x_4332_;
v_isShared_4337_ = v_isSharedCheck_4342_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v_x_4332_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4342_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
lean_object* v___x_4340_; 
v___x_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4339_);
return v___x_4340_;
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_a_4343_ = lean_ctor_get(v_x_4332_, 0);
lean_inc(v_a_4343_);
lean_dec_ref_known(v_x_4332_, 1);
v___x_4344_ = lean_unsigned_to_nat(0u);
v___x_4345_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4326_, v_handler_4327_, v_extensions_4328_, v_connectionContext_4329_, v_a_4343_);
v___x_4346_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4344_, v___x_4330_, v___x_4345_, v___f_4331_);
return v___x_4346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4347_, lean_object* v_handler_4348_, lean_object* v_extensions_4349_, lean_object* v_connectionContext_4350_, lean_object* v___x_4351_, lean_object* v___f_4352_, lean_object* v_x_4353_, lean_object* v___y_4354_){
_start:
{
uint8_t v___x_5353__boxed_4355_; lean_object* v_res_4356_; 
v___x_5353__boxed_4355_ = lean_unbox(v___x_4351_);
v_res_4356_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4347_, v_handler_4348_, v_extensions_4349_, v_connectionContext_4350_, v___x_5353__boxed_4355_, v___f_4352_, v_x_4353_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4357_, lean_object* v_responseBodyInstance_4358_, lean_object* v_handler_4359_, lean_object* v_config_4360_, lean_object* v_connectionContext_4361_, lean_object* v_events_4362_, lean_object* v___x_4363_, uint8_t v___x_4364_, lean_object* v___f_4365_, lean_object* v_____r_4366_){
_start:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4368_ = lean_unsigned_to_nat(0u);
v___x_4369_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4357_, v_responseBodyInstance_4358_, v_handler_4359_, v_config_4360_, v_connectionContext_4361_, v_events_4362_, v___x_4363_);
v___x_4370_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4368_, v___x_4364_, v___x_4369_, v___f_4365_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4371_, lean_object* v_responseBodyInstance_4372_, lean_object* v_handler_4373_, lean_object* v_config_4374_, lean_object* v_connectionContext_4375_, lean_object* v_events_4376_, lean_object* v___x_4377_, lean_object* v___x_4378_, lean_object* v___f_4379_, lean_object* v_____r_4380_, lean_object* v___y_4381_){
_start:
{
uint8_t v___x_5392__boxed_4382_; lean_object* v_res_4383_; 
v___x_5392__boxed_4382_ = lean_unbox(v___x_4378_);
v_res_4383_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4371_, v_responseBodyInstance_4372_, v_handler_4373_, v_config_4374_, v_connectionContext_4375_, v_events_4376_, v___x_4377_, v___x_5392__boxed_4382_, v___f_4379_, v_____r_4380_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4384_, lean_object* v___f_4385_, lean_object* v_x_4386_){
_start:
{
if (lean_obj_tag(v_x_4386_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4396_; 
lean_dec_ref(v___f_4385_);
lean_dec_ref(v___x_4384_);
v_a_4388_ = lean_ctor_get(v_x_4386_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v_x_4386_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4390_ = v_x_4386_;
v_isShared_4391_ = v_isSharedCheck_4396_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v_x_4386_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4396_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4394_; 
v___x_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4393_);
return v___x_4394_;
}
}
}
else
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4408_; 
v_a_4397_ = lean_ctor_get(v_x_4386_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_x_4386_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4399_ = v_x_4386_;
v_isShared_4400_ = v_isSharedCheck_4408_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v_x_4386_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4408_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
if (lean_obj_tag(v_a_4397_) == 0)
{
lean_object* v___x_4401_; lean_object* v___x_4403_; 
lean_dec_ref(v___f_4385_);
v___x_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4384_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 0, v___x_4401_);
v___x_4403_ = v___x_4399_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4401_);
v___x_4403_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
lean_object* v___x_4404_; 
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
return v___x_4404_;
}
}
else
{
lean_object* v_val_4406_; lean_object* v___x_4407_; 
lean_del_object(v___x_4399_);
lean_dec_ref(v___x_4384_);
v_val_4406_ = lean_ctor_get(v_a_4397_, 0);
lean_inc(v_val_4406_);
lean_dec_ref_known(v_a_4397_, 1);
v___x_4407_ = lean_apply_2(v___f_4385_, v_val_4406_, lean_box(0));
return v___x_4407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4409_, lean_object* v___f_4410_, lean_object* v_x_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4409_, v___f_4410_, v_x_4411_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4414_, lean_object* v_responseBodyInstance_4415_, lean_object* v_handler_4416_, lean_object* v_config_4417_, lean_object* v_connectionContext_4418_, uint8_t v___x_4419_, lean_object* v___f_4420_, lean_object* v_inst_4421_, lean_object* v_socket_4422_, lean_object* v___f_4423_, lean_object* v___f_4424_, lean_object* v_x_4425_, lean_object* v_____s_4426_){
_start:
{
lean_object* v_machine_4428_; lean_object* v_reader_4429_; lean_object* v_requestStream_4430_; lean_object* v_keepAliveTimeout_4431_; lean_object* v_currentTimeout_4432_; lean_object* v_headerTimeout_4433_; lean_object* v_response_4434_; lean_object* v_respStream_4435_; uint8_t v_requiresData_4436_; lean_object* v_expectData_4437_; uint8_t v_handlerDispatched_4438_; lean_object* v_pendingHead_4439_; lean_object* v_writer_4440_; lean_object* v_state_4441_; uint8_t v___x_4442_; 
v_machine_4428_ = lean_ctor_get(v_____s_4426_, 0);
v_reader_4429_ = lean_ctor_get(v_machine_4428_, 0);
v_requestStream_4430_ = lean_ctor_get(v_____s_4426_, 1);
v_keepAliveTimeout_4431_ = lean_ctor_get(v_____s_4426_, 2);
v_currentTimeout_4432_ = lean_ctor_get(v_____s_4426_, 3);
v_headerTimeout_4433_ = lean_ctor_get(v_____s_4426_, 4);
v_response_4434_ = lean_ctor_get(v_____s_4426_, 5);
v_respStream_4435_ = lean_ctor_get(v_____s_4426_, 6);
v_requiresData_4436_ = lean_ctor_get_uint8(v_____s_4426_, sizeof(void*)*9);
v_expectData_4437_ = lean_ctor_get(v_____s_4426_, 7);
v_handlerDispatched_4438_ = lean_ctor_get_uint8(v_____s_4426_, sizeof(void*)*9 + 1);
v_pendingHead_4439_ = lean_ctor_get(v_____s_4426_, 8);
v_writer_4440_ = lean_ctor_get(v_machine_4428_, 1);
v_state_4441_ = lean_ctor_get(v_reader_4429_, 0);
v___x_4442_ = 0;
if (lean_obj_tag(v_state_4441_) == 6)
{
lean_object* v_state_4464_; 
v_state_4464_ = lean_ctor_get(v_writer_4440_, 2);
if (lean_obj_tag(v_state_4464_) == 7)
{
lean_object* v_outputData_4465_; lean_object* v_size_4466_; lean_object* v___x_4467_; uint8_t v___x_4468_; 
v_outputData_4465_ = lean_ctor_get(v_writer_4440_, 1);
v_size_4466_ = lean_ctor_get(v_outputData_4465_, 1);
v___x_4467_ = lean_unsigned_to_nat(0u);
v___x_4468_ = lean_nat_dec_eq(v_size_4466_, v___x_4467_);
if (v___x_4468_ == 0)
{
lean_inc(v_pendingHead_4439_);
lean_inc(v_expectData_4437_);
lean_inc(v_respStream_4435_);
lean_inc_ref(v_response_4434_);
lean_inc(v_headerTimeout_4433_);
lean_inc(v_currentTimeout_4432_);
lean_inc(v_keepAliveTimeout_4431_);
lean_inc_ref(v_requestStream_4430_);
lean_inc_ref(v_machine_4428_);
lean_dec_ref(v_____s_4426_);
goto v___jp_4443_;
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
lean_dec_ref(v___f_4424_);
lean_dec_ref(v___f_4423_);
lean_dec(v_socket_4422_);
lean_dec_ref(v_inst_4421_);
lean_dec_ref(v___f_4420_);
lean_dec_ref(v_connectionContext_4418_);
lean_dec_ref(v_config_4417_);
lean_dec(v_handler_4416_);
lean_dec_ref(v_responseBodyInstance_4415_);
lean_dec_ref(v_h_4414_);
v___x_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4469_, 0, v_____s_4426_);
v___x_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
v___x_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
return v___x_4471_;
}
}
else
{
lean_inc(v_pendingHead_4439_);
lean_inc(v_expectData_4437_);
lean_inc(v_respStream_4435_);
lean_inc_ref(v_response_4434_);
lean_inc(v_headerTimeout_4433_);
lean_inc(v_currentTimeout_4432_);
lean_inc(v_keepAliveTimeout_4431_);
lean_inc_ref(v_requestStream_4430_);
lean_inc_ref(v_machine_4428_);
lean_dec_ref(v_____s_4426_);
goto v___jp_4443_;
}
}
else
{
lean_inc(v_pendingHead_4439_);
lean_inc(v_expectData_4437_);
lean_inc(v_respStream_4435_);
lean_inc_ref(v_response_4434_);
lean_inc(v_headerTimeout_4433_);
lean_inc(v_currentTimeout_4432_);
lean_inc(v_keepAliveTimeout_4431_);
lean_inc_ref(v_requestStream_4430_);
lean_inc_ref(v_machine_4428_);
lean_dec_ref(v_____s_4426_);
goto v___jp_4443_;
}
v___jp_4443_:
{
lean_object* v___x_4444_; lean_object* v_snd_4445_; lean_object* v_output_4446_; lean_object* v_fst_4447_; lean_object* v_events_4448_; lean_object* v_data_4449_; lean_object* v_size_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___f_4453_; lean_object* v___x_4454_; uint8_t v___x_4455_; 
v___x_4444_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4442_, v_machine_4428_);
v_snd_4445_ = lean_ctor_get(v___x_4444_, 1);
lean_inc(v_snd_4445_);
v_output_4446_ = lean_ctor_get(v_snd_4445_, 1);
lean_inc_ref(v_output_4446_);
v_fst_4447_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_fst_4447_);
lean_dec_ref(v___x_4444_);
v_events_4448_ = lean_ctor_get(v_snd_4445_, 0);
lean_inc_ref_n(v_events_4448_, 2);
lean_dec(v_snd_4445_);
v_data_4449_ = lean_ctor_get(v_output_4446_, 0);
lean_inc_ref(v_data_4449_);
v_size_4450_ = lean_ctor_get(v_output_4446_, 1);
lean_inc(v_size_4450_);
lean_dec_ref(v_output_4446_);
v___x_4451_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4451_, 0, v_fst_4447_);
lean_ctor_set(v___x_4451_, 1, v_requestStream_4430_);
lean_ctor_set(v___x_4451_, 2, v_keepAliveTimeout_4431_);
lean_ctor_set(v___x_4451_, 3, v_currentTimeout_4432_);
lean_ctor_set(v___x_4451_, 4, v_headerTimeout_4433_);
lean_ctor_set(v___x_4451_, 5, v_response_4434_);
lean_ctor_set(v___x_4451_, 6, v_respStream_4435_);
lean_ctor_set(v___x_4451_, 7, v_expectData_4437_);
lean_ctor_set(v___x_4451_, 8, v_pendingHead_4439_);
lean_ctor_set_uint8(v___x_4451_, sizeof(void*)*9, v_requiresData_4436_);
lean_ctor_set_uint8(v___x_4451_, sizeof(void*)*9 + 1, v_handlerDispatched_4438_);
v___x_4452_ = lean_box(v___x_4419_);
lean_inc_ref(v___f_4420_);
lean_inc_ref(v___x_4451_);
lean_inc_ref(v_connectionContext_4418_);
lean_inc_ref(v_config_4417_);
lean_inc(v_handler_4416_);
lean_inc_ref(v_responseBodyInstance_4415_);
lean_inc_ref(v_h_4414_);
v___f_4453_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4453_, 0, v_h_4414_);
lean_closure_set(v___f_4453_, 1, v_responseBodyInstance_4415_);
lean_closure_set(v___f_4453_, 2, v_handler_4416_);
lean_closure_set(v___f_4453_, 3, v_config_4417_);
lean_closure_set(v___f_4453_, 4, v_connectionContext_4418_);
lean_closure_set(v___f_4453_, 5, v_events_4448_);
lean_closure_set(v___f_4453_, 6, v___x_4451_);
lean_closure_set(v___f_4453_, 7, v___x_4452_);
lean_closure_set(v___f_4453_, 8, v___f_4420_);
v___x_4454_ = lean_unsigned_to_nat(0u);
v___x_4455_ = lean_nat_dec_lt(v___x_4454_, v_size_4450_);
lean_dec(v_size_4450_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
lean_dec_ref(v___f_4453_);
lean_dec_ref(v_data_4449_);
lean_dec_ref(v___f_4424_);
lean_dec_ref(v___f_4423_);
lean_dec(v_socket_4422_);
lean_dec_ref(v_inst_4421_);
v___x_4456_ = lean_box(0);
v___x_4457_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4414_, v_responseBodyInstance_4415_, v_handler_4416_, v_config_4417_, v_connectionContext_4418_, v_events_4448_, v___x_4451_, v___x_4419_, v___f_4420_, v___x_4456_);
return v___x_4457_;
}
else
{
lean_object* v_sendAll_4458_; lean_object* v___f_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
lean_dec_ref(v_events_4448_);
lean_dec_ref(v___f_4420_);
lean_dec_ref(v_connectionContext_4418_);
lean_dec_ref(v_config_4417_);
lean_dec(v_handler_4416_);
lean_dec_ref(v_responseBodyInstance_4415_);
lean_dec_ref(v_h_4414_);
v_sendAll_4458_ = lean_ctor_get(v_inst_4421_, 1);
lean_inc_ref(v_sendAll_4458_);
lean_dec_ref(v_inst_4421_);
v___f_4459_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4459_, 0, v___x_4451_);
lean_closure_set(v___f_4459_, 1, v___f_4453_);
v___x_4460_ = lean_apply_3(v_sendAll_4458_, v_socket_4422_, v_data_4449_, lean_box(0));
v___x_4461_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4454_, v___x_4419_, v___x_4460_, v___f_4423_);
v___x_4462_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4454_, v___x_4419_, v___x_4461_, v___f_4424_);
v___x_4463_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4454_, v___x_4419_, v___x_4462_, v___f_4459_);
return v___x_4463_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4472_, lean_object* v_responseBodyInstance_4473_, lean_object* v_handler_4474_, lean_object* v_config_4475_, lean_object* v_connectionContext_4476_, lean_object* v___x_4477_, lean_object* v___f_4478_, lean_object* v_inst_4479_, lean_object* v_socket_4480_, lean_object* v___f_4481_, lean_object* v___f_4482_, lean_object* v_x_4483_, lean_object* v_____s_4484_, lean_object* v___y_4485_){
_start:
{
uint8_t v___x_5466__boxed_4486_; lean_object* v_res_4487_; 
v___x_5466__boxed_4486_ = lean_unbox(v___x_4477_);
v_res_4487_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4472_, v_responseBodyInstance_4473_, v_handler_4474_, v_config_4475_, v_connectionContext_4476_, v___x_5466__boxed_4486_, v___f_4478_, v_inst_4479_, v_socket_4480_, v___f_4481_, v___f_4482_, v_x_4483_, v_____s_4484_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4488_, lean_object* v_x_4489_){
_start:
{
if (lean_obj_tag(v_x_4489_) == 0)
{
lean_object* v_a_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4499_; 
v_a_4491_ = lean_ctor_get(v_x_4489_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v_x_4489_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4493_ = v_x_4489_;
v_isShared_4494_ = v_isSharedCheck_4499_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_a_4491_);
lean_dec(v_x_4489_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4499_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4496_; 
if (v_isShared_4494_ == 0)
{
v___x_4496_ = v___x_4493_;
goto v_reusejp_4495_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4491_);
v___x_4496_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4495_;
}
v_reusejp_4495_:
{
lean_object* v___x_4497_; 
v___x_4497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4496_);
return v___x_4497_;
}
}
}
else
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
lean_dec_ref_known(v_x_4489_, 1);
v___x_4500_ = l_IO_Promise_result_x21___redArg(v_a_4488_);
v___x_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
return v___x_4501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4502_, lean_object* v_x_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4502_, v_x_4503_);
lean_dec(v_a_4502_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4506_, lean_object* v___x_4507_, lean_object* v___x_4508_, uint8_t v___x_4509_, lean_object* v_x_4510_){
_start:
{
if (lean_obj_tag(v_x_4510_) == 0)
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4520_; 
lean_dec_ref(v___x_4508_);
lean_dec(v___x_4507_);
lean_dec_ref(v___f_4506_);
v_a_4512_ = lean_ctor_get(v_x_4510_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v_x_4510_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4514_ = v_x_4510_;
v_isShared_4515_ = v_isSharedCheck_4520_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v_x_4510_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4520_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
lean_object* v___x_4518_; 
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
return v___x_4518_;
}
}
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4532_; 
v_a_4521_ = lean_ctor_get(v_x_4510_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v_x_4510_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4523_ = v_x_4510_;
v_isShared_4524_ = v_isSharedCheck_4532_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v_x_4510_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4532_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___f_4525_; lean_object* v___x_4526_; lean_object* v___x_4528_; 
lean_inc(v_a_4521_);
v___f_4525_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4525_, 0, v_a_4521_);
lean_inc(v___x_4507_);
v___x_4526_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4506_, v___x_4507_, v_a_4521_, v___x_4508_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v___x_4526_);
v___x_4528_ = v___x_4523_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4526_);
v___x_4528_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4529_, 0, v___x_4528_);
v___x_4530_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4507_, v___x_4509_, v___x_4529_, v___f_4525_);
return v___x_4530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4533_, lean_object* v___x_4534_, lean_object* v___x_4535_, lean_object* v___x_4536_, lean_object* v_x_4537_, lean_object* v___y_4538_){
_start:
{
uint8_t v___x_5569__boxed_4539_; lean_object* v_res_4540_; 
v___x_5569__boxed_4539_ = lean_unbox(v___x_4536_);
v_res_4540_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4533_, v___x_4534_, v___x_4535_, v___x_5569__boxed_4539_, v_x_4537_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4541_, lean_object* v_h_4542_, lean_object* v_responseBodyInstance_4543_, lean_object* v_handler_4544_, lean_object* v___f_4545_, lean_object* v_inst_4546_, lean_object* v_socket_4547_, lean_object* v_connectionContext_4548_, lean_object* v_extensions_4549_, lean_object* v___f_4550_, lean_object* v___f_4551_, lean_object* v_machine_4552_, lean_object* v_a_4553_, lean_object* v___x_4554_, lean_object* v___f_4555_, lean_object* v_x_4556_){
_start:
{
if (lean_obj_tag(v_x_4556_) == 0)
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4566_; 
lean_dec_ref(v___f_4555_);
lean_dec(v___x_4554_);
lean_dec_ref(v_a_4553_);
lean_dec_ref(v_machine_4552_);
lean_dec_ref(v___f_4551_);
lean_dec_ref(v___f_4550_);
lean_dec(v_extensions_4549_);
lean_dec_ref(v_connectionContext_4548_);
lean_dec(v_socket_4547_);
lean_dec_ref(v_inst_4546_);
lean_dec_ref(v___f_4545_);
lean_dec(v_handler_4544_);
lean_dec_ref(v_responseBodyInstance_4543_);
lean_dec_ref(v_h_4542_);
lean_dec_ref(v_config_4541_);
v_a_4558_ = lean_ctor_get(v_x_4556_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v_x_4556_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4560_ = v_x_4556_;
v_isShared_4561_ = v_isSharedCheck_4566_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v_x_4556_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4566_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4563_; 
if (v_isShared_4561_ == 0)
{
v___x_4563_ = v___x_4560_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4558_);
v___x_4563_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
lean_object* v___x_4564_; 
v___x_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4563_);
return v___x_4564_;
}
}
}
else
{
lean_object* v_a_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4592_; 
v_a_4567_ = lean_ctor_get(v_x_4556_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v_x_4556_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4569_ = v_x_4556_;
v_isShared_4570_ = v_isSharedCheck_4592_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_a_4567_);
lean_dec(v_x_4556_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4592_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v_keepAliveTimeout_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; uint8_t v___x_4574_; lean_object* v___x_4575_; lean_object* v___f_4576_; lean_object* v___x_4577_; lean_object* v___f_4578_; lean_object* v___x_4579_; lean_object* v___f_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___f_4584_; lean_object* v___x_4585_; lean_object* v___x_4587_; 
v_keepAliveTimeout_4571_ = lean_ctor_get(v_config_4541_, 5);
lean_inc_n(v_keepAliveTimeout_4571_, 2);
v___x_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4572_, 0, v_keepAliveTimeout_4571_);
v___x_4573_ = lean_box(0);
v___x_4574_ = 0;
v___x_4575_ = lean_box(v___x_4574_);
lean_inc_ref_n(v_connectionContext_4548_, 2);
lean_inc(v_socket_4547_);
lean_inc_ref(v_inst_4546_);
lean_inc_ref(v_config_4541_);
lean_inc_n(v_handler_4544_, 2);
lean_inc_ref(v_responseBodyInstance_4543_);
lean_inc_ref_n(v_h_4542_, 2);
v___f_4576_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4576_, 0, v___x_4575_);
lean_closure_set(v___f_4576_, 1, v_h_4542_);
lean_closure_set(v___f_4576_, 2, v_responseBodyInstance_4543_);
lean_closure_set(v___f_4576_, 3, v_handler_4544_);
lean_closure_set(v___f_4576_, 4, v_config_4541_);
lean_closure_set(v___f_4576_, 5, v___f_4545_);
lean_closure_set(v___f_4576_, 6, v_inst_4546_);
lean_closure_set(v___f_4576_, 7, v_socket_4547_);
lean_closure_set(v___f_4576_, 8, v_connectionContext_4548_);
v___x_4577_ = lean_box(v___x_4574_);
v___f_4578_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4578_, 0, v_h_4542_);
lean_closure_set(v___f_4578_, 1, v_handler_4544_);
lean_closure_set(v___f_4578_, 2, v_extensions_4549_);
lean_closure_set(v___f_4578_, 3, v_connectionContext_4548_);
lean_closure_set(v___f_4578_, 4, v___x_4577_);
lean_closure_set(v___f_4578_, 5, v___f_4576_);
v___x_4579_ = lean_box(v___x_4574_);
v___f_4580_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4580_, 0, v_h_4542_);
lean_closure_set(v___f_4580_, 1, v_responseBodyInstance_4543_);
lean_closure_set(v___f_4580_, 2, v_handler_4544_);
lean_closure_set(v___f_4580_, 3, v_config_4541_);
lean_closure_set(v___f_4580_, 4, v_connectionContext_4548_);
lean_closure_set(v___f_4580_, 5, v___x_4579_);
lean_closure_set(v___f_4580_, 6, v___f_4578_);
lean_closure_set(v___f_4580_, 7, v_inst_4546_);
lean_closure_set(v___f_4580_, 8, v_socket_4547_);
lean_closure_set(v___f_4580_, 9, v___f_4550_);
lean_closure_set(v___f_4580_, 10, v___f_4551_);
v___x_4581_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4581_, 0, v_machine_4552_);
lean_ctor_set(v___x_4581_, 1, v_a_4553_);
lean_ctor_set(v___x_4581_, 2, v___x_4572_);
lean_ctor_set(v___x_4581_, 3, v_keepAliveTimeout_4571_);
lean_ctor_set(v___x_4581_, 4, v___x_4573_);
lean_ctor_set(v___x_4581_, 5, v_a_4567_);
lean_ctor_set(v___x_4581_, 6, v___x_4573_);
lean_ctor_set(v___x_4581_, 7, v___x_4554_);
lean_ctor_set(v___x_4581_, 8, v___x_4573_);
lean_ctor_set_uint8(v___x_4581_, sizeof(void*)*9, v___x_4574_);
lean_ctor_set_uint8(v___x_4581_, sizeof(void*)*9 + 1, v___x_4574_);
v___x_4582_ = lean_unsigned_to_nat(0u);
v___x_4583_ = lean_box(v___x_4574_);
v___f_4584_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4584_, 0, v___f_4580_);
lean_closure_set(v___f_4584_, 1, v___x_4582_);
lean_closure_set(v___f_4584_, 2, v___x_4581_);
lean_closure_set(v___f_4584_, 3, v___x_4583_);
v___x_4585_ = lean_io_promise_new();
if (v_isShared_4570_ == 0)
{
lean_ctor_set(v___x_4569_, 0, v___x_4585_);
v___x_4587_ = v___x_4569_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v___x_4585_);
v___x_4587_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
v___x_4589_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4582_, v___x_4574_, v___x_4588_, v___f_4584_);
v___x_4590_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4582_, v___x_4574_, v___x_4589_, v___f_4555_);
return v___x_4590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4593_ = _args[0];
lean_object* v_h_4594_ = _args[1];
lean_object* v_responseBodyInstance_4595_ = _args[2];
lean_object* v_handler_4596_ = _args[3];
lean_object* v___f_4597_ = _args[4];
lean_object* v_inst_4598_ = _args[5];
lean_object* v_socket_4599_ = _args[6];
lean_object* v_connectionContext_4600_ = _args[7];
lean_object* v_extensions_4601_ = _args[8];
lean_object* v___f_4602_ = _args[9];
lean_object* v___f_4603_ = _args[10];
lean_object* v_machine_4604_ = _args[11];
lean_object* v_a_4605_ = _args[12];
lean_object* v___x_4606_ = _args[13];
lean_object* v___f_4607_ = _args[14];
lean_object* v_x_4608_ = _args[15];
lean_object* v___y_4609_ = _args[16];
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4593_, v_h_4594_, v_responseBodyInstance_4595_, v_handler_4596_, v___f_4597_, v_inst_4598_, v_socket_4599_, v_connectionContext_4600_, v_extensions_4601_, v___f_4602_, v___f_4603_, v_machine_4604_, v_a_4605_, v___x_4606_, v___f_4607_, v_x_4608_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4611_, lean_object* v_h_4612_, lean_object* v_responseBodyInstance_4613_, lean_object* v_handler_4614_, lean_object* v___f_4615_, lean_object* v_inst_4616_, lean_object* v_socket_4617_, lean_object* v_connectionContext_4618_, lean_object* v_extensions_4619_, lean_object* v___f_4620_, lean_object* v___f_4621_, lean_object* v_machine_4622_, lean_object* v___f_4623_, lean_object* v_x_4624_){
_start:
{
if (lean_obj_tag(v_x_4624_) == 0)
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4634_; 
lean_dec_ref(v___f_4623_);
lean_dec_ref(v_machine_4622_);
lean_dec_ref(v___f_4621_);
lean_dec_ref(v___f_4620_);
lean_dec(v_extensions_4619_);
lean_dec_ref(v_connectionContext_4618_);
lean_dec(v_socket_4617_);
lean_dec_ref(v_inst_4616_);
lean_dec_ref(v___f_4615_);
lean_dec(v_handler_4614_);
lean_dec_ref(v_responseBodyInstance_4613_);
lean_dec_ref(v_h_4612_);
lean_dec_ref(v_config_4611_);
v_a_4626_ = lean_ctor_get(v_x_4624_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v_x_4624_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4628_ = v_x_4624_;
v_isShared_4629_ = v_isSharedCheck_4634_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v_x_4624_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4634_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4631_; 
if (v_isShared_4629_ == 0)
{
v___x_4631_ = v___x_4628_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4626_);
v___x_4631_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4632_; 
v___x_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4631_);
return v___x_4632_;
}
}
}
else
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4649_; 
v_a_4635_ = lean_ctor_get(v_x_4624_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v_x_4624_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4637_ = v_x_4624_;
v_isShared_4638_ = v_isSharedCheck_4649_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v_x_4624_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4649_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4639_; lean_object* v___f_4640_; lean_object* v___x_4641_; uint8_t v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4645_; 
v___x_4639_ = lean_box(0);
v___f_4640_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4640_, 0, v_config_4611_);
lean_closure_set(v___f_4640_, 1, v_h_4612_);
lean_closure_set(v___f_4640_, 2, v_responseBodyInstance_4613_);
lean_closure_set(v___f_4640_, 3, v_handler_4614_);
lean_closure_set(v___f_4640_, 4, v___f_4615_);
lean_closure_set(v___f_4640_, 5, v_inst_4616_);
lean_closure_set(v___f_4640_, 6, v_socket_4617_);
lean_closure_set(v___f_4640_, 7, v_connectionContext_4618_);
lean_closure_set(v___f_4640_, 8, v_extensions_4619_);
lean_closure_set(v___f_4640_, 9, v___f_4620_);
lean_closure_set(v___f_4640_, 10, v___f_4621_);
lean_closure_set(v___f_4640_, 11, v_machine_4622_);
lean_closure_set(v___f_4640_, 12, v_a_4635_);
lean_closure_set(v___f_4640_, 13, v___x_4639_);
lean_closure_set(v___f_4640_, 14, v___f_4623_);
v___x_4641_ = lean_unsigned_to_nat(0u);
v___x_4642_ = 0;
v___x_4643_ = l_Std_CloseableChannel_new___redArg(v___x_4639_);
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 0, v___x_4643_);
v___x_4645_ = v___x_4637_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4643_);
v___x_4645_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4645_);
v___x_4647_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4641_, v___x_4642_, v___x_4646_, v___f_4640_);
return v___x_4647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4650_, lean_object* v_h_4651_, lean_object* v_responseBodyInstance_4652_, lean_object* v_handler_4653_, lean_object* v___f_4654_, lean_object* v_inst_4655_, lean_object* v_socket_4656_, lean_object* v_connectionContext_4657_, lean_object* v_extensions_4658_, lean_object* v___f_4659_, lean_object* v___f_4660_, lean_object* v_machine_4661_, lean_object* v___f_4662_, lean_object* v_x_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v_res_4665_; 
v_res_4665_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4650_, v_h_4651_, v_responseBodyInstance_4652_, v_handler_4653_, v___f_4654_, v_inst_4655_, v_socket_4656_, v_connectionContext_4657_, v_extensions_4658_, v___f_4659_, v___f_4660_, v_machine_4661_, v___f_4662_, v_x_4663_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4669_, lean_object* v_h_4670_, lean_object* v_connection_4671_, lean_object* v_config_4672_, lean_object* v_connectionContext_4673_, lean_object* v_handler_4674_){
_start:
{
lean_object* v_responseBodyInstance_4676_; lean_object* v_onFailure_4677_; lean_object* v_socket_4678_; lean_object* v_machine_4679_; lean_object* v_extensions_4680_; lean_object* v___f_4681_; lean_object* v___f_4682_; lean_object* v___f_4683_; lean_object* v___f_4684_; lean_object* v___f_4685_; lean_object* v___f_4686_; lean_object* v___f_4687_; lean_object* v___f_4688_; lean_object* v___f_4689_; lean_object* v___x_4690_; uint8_t v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v_responseBodyInstance_4676_ = lean_ctor_get(v_h_4670_, 0);
lean_inc_ref_n(v_responseBodyInstance_4676_, 2);
v_onFailure_4677_ = lean_ctor_get(v_h_4670_, 2);
v_socket_4678_ = lean_ctor_get(v_connection_4671_, 0);
lean_inc_n(v_socket_4678_, 2);
v_machine_4679_ = lean_ctor_get(v_connection_4671_, 1);
lean_inc_ref(v_machine_4679_);
v_extensions_4680_ = lean_ctor_get(v_connection_4671_, 2);
lean_inc(v_extensions_4680_);
lean_dec_ref(v_connection_4671_);
v___f_4681_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4682_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4683_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
lean_inc(v_handler_4674_);
lean_inc_ref(v_onFailure_4677_);
v___f_4684_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4684_, 0, v_onFailure_4677_);
lean_closure_set(v___f_4684_, 1, v_handler_4674_);
lean_closure_set(v___f_4684_, 2, v___f_4683_);
v___f_4685_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc_ref(v_inst_4669_);
v___f_4686_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4686_, 0, v_inst_4669_);
lean_closure_set(v___f_4686_, 1, v_socket_4678_);
lean_inc_ref(v___f_4686_);
v___f_4687_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4687_, 0, v___f_4686_);
v___f_4688_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4688_, 0, v_responseBodyInstance_4676_);
lean_closure_set(v___f_4688_, 1, v___f_4687_);
lean_closure_set(v___f_4688_, 2, v___f_4686_);
lean_closure_set(v___f_4688_, 3, v___f_4681_);
v___f_4689_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4689_, 0, v_config_4672_);
lean_closure_set(v___f_4689_, 1, v_h_4670_);
lean_closure_set(v___f_4689_, 2, v_responseBodyInstance_4676_);
lean_closure_set(v___f_4689_, 3, v_handler_4674_);
lean_closure_set(v___f_4689_, 4, v___f_4685_);
lean_closure_set(v___f_4689_, 5, v_inst_4669_);
lean_closure_set(v___f_4689_, 6, v_socket_4678_);
lean_closure_set(v___f_4689_, 7, v_connectionContext_4673_);
lean_closure_set(v___f_4689_, 8, v_extensions_4680_);
lean_closure_set(v___f_4689_, 9, v___f_4682_);
lean_closure_set(v___f_4689_, 10, v___f_4684_);
lean_closure_set(v___f_4689_, 11, v_machine_4679_);
lean_closure_set(v___f_4689_, 12, v___f_4688_);
v___x_4690_ = lean_unsigned_to_nat(0u);
v___x_4691_ = 0;
v___x_4692_ = l_Std_Http_Body_mkStream();
v___x_4693_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4690_, v___x_4691_, v___x_4692_, v___f_4689_);
return v___x_4693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4694_, lean_object* v_h_4695_, lean_object* v_connection_4696_, lean_object* v_config_4697_, lean_object* v_connectionContext_4698_, lean_object* v_handler_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4694_, v_h_4695_, v_connection_4696_, v_config_4697_, v_connectionContext_4698_, v_handler_4699_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4702_, lean_object* v_00_u03c3_4703_, lean_object* v_inst_4704_, lean_object* v_h_4705_, lean_object* v_connection_4706_, lean_object* v_config_4707_, lean_object* v_connectionContext_4708_, lean_object* v_handler_4709_){
_start:
{
lean_object* v___x_4711_; 
v___x_4711_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4704_, v_h_4705_, v_connection_4706_, v_config_4707_, v_connectionContext_4708_, v_handler_4709_);
return v___x_4711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4712_, lean_object* v_00_u03c3_4713_, lean_object* v_inst_4714_, lean_object* v_h_4715_, lean_object* v_connection_4716_, lean_object* v_config_4717_, lean_object* v_connectionContext_4718_, lean_object* v_handler_4719_, lean_object* v_a_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4712_, v_00_u03c3_4713_, v_inst_4714_, v_h_4715_, v_connection_4716_, v_config_4717_, v_connectionContext_4718_, v_handler_4719_);
return v_res_4721_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4722_; lean_object* v___x_4723_; 
v___x_4722_ = 0;
v___x_4723_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4722_);
return v___x_4723_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4724_ = lean_unsigned_to_nat(4096u);
v___x_4725_ = lean_mk_empty_byte_array(v___x_4724_);
return v___x_4725_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4726_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4727_ = l_ByteArray_mkIterator(v___x_4726_);
return v___x_4727_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4728_ = 0;
v___x_4729_ = lean_unsigned_to_nat(0u);
v___x_4730_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4731_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4732_ = lean_box(0);
v___x_4733_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4733_, 0, v___x_4732_);
lean_ctor_set(v___x_4733_, 1, v___x_4731_);
lean_ctor_set(v___x_4733_, 2, v___x_4730_);
lean_ctor_set(v___x_4733_, 3, v___x_4729_);
lean_ctor_set(v___x_4733_, 4, v___x_4729_);
lean_ctor_set(v___x_4733_, 5, v___x_4729_);
lean_ctor_set_uint8(v___x_4733_, sizeof(void*)*6, v___x_4728_);
return v___x_4733_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4741_; lean_object* v___x_4742_; 
v___x_4741_ = 1;
v___x_4742_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4741_);
return v___x_4742_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4743_; uint8_t v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4743_ = lean_unsigned_to_nat(0u);
v___x_4744_ = 0;
v___x_4745_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4746_ = lean_box(0);
v___x_4747_ = lean_box(0);
v___x_4748_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4749_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4750_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
lean_ctor_set(v___x_4750_, 1, v___x_4748_);
lean_ctor_set(v___x_4750_, 2, v___x_4747_);
lean_ctor_set(v___x_4750_, 3, v___x_4746_);
lean_ctor_set(v___x_4750_, 4, v___x_4745_);
lean_ctor_set(v___x_4750_, 5, v___x_4743_);
lean_ctor_set_uint8(v___x_4750_, sizeof(void*)*6, v___x_4744_);
lean_ctor_set_uint8(v___x_4750_, sizeof(void*)*6 + 1, v___x_4744_);
lean_ctor_set_uint8(v___x_4750_, sizeof(void*)*6 + 2, v___x_4744_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4751_, lean_object* v_client_4752_, lean_object* v_extensions_4753_, lean_object* v_inst_4754_, lean_object* v_inst_4755_, lean_object* v_handler_4756_, lean_object* v_x_4757_){
_start:
{
if (lean_obj_tag(v_x_4757_) == 0)
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4767_; 
lean_dec(v_handler_4756_);
lean_dec_ref(v_inst_4755_);
lean_dec_ref(v_inst_4754_);
lean_dec(v_extensions_4753_);
lean_dec(v_client_4752_);
lean_dec_ref(v_config_4751_);
v_a_4759_ = lean_ctor_get(v_x_4757_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v_x_4757_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4761_ = v_x_4757_;
v_isShared_4762_ = v_isSharedCheck_4767_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v_x_4757_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4767_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4759_);
v___x_4764_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
lean_object* v___x_4765_; 
v___x_4765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4764_);
return v___x_4765_;
}
}
}
else
{
lean_object* v_a_4768_; uint8_t v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; uint8_t v_enableKeepAlive_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v_a_4768_ = lean_ctor_get(v_x_4757_, 0);
lean_inc(v_a_4768_);
lean_dec_ref_known(v_x_4757_, 1);
v___x_4769_ = 0;
v___x_4770_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4771_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4772_ = lean_box(0);
v___x_4773_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4774_ = l_Std_Http_Config_toH1Config(v_config_4751_);
v_enableKeepAlive_4775_ = lean_ctor_get_uint8(v___x_4774_, sizeof(void*)*18);
v___x_4776_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_4776_, 0, v___x_4770_);
lean_ctor_set(v___x_4776_, 1, v___x_4773_);
lean_ctor_set(v___x_4776_, 2, v___x_4774_);
lean_ctor_set(v___x_4776_, 3, v___x_4771_);
lean_ctor_set(v___x_4776_, 4, v___x_4772_);
lean_ctor_set(v___x_4776_, 5, v___x_4772_);
lean_ctor_set_uint8(v___x_4776_, sizeof(void*)*6, v_enableKeepAlive_4775_);
lean_ctor_set_uint8(v___x_4776_, sizeof(void*)*6 + 1, v___x_4769_);
v___x_4777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4777_, 0, v_client_4752_);
lean_ctor_set(v___x_4777_, 1, v___x_4776_);
lean_ctor_set(v___x_4777_, 2, v_extensions_4753_);
v___x_4778_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4754_, v_inst_4755_, v___x_4777_, v_config_4751_, v_a_4768_, v_handler_4756_);
return v___x_4778_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4779_, lean_object* v_client_4780_, lean_object* v_extensions_4781_, lean_object* v_inst_4782_, lean_object* v_inst_4783_, lean_object* v_handler_4784_, lean_object* v_x_4785_, lean_object* v___y_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4779_, v_client_4780_, v_extensions_4781_, v_inst_4782_, v_inst_4783_, v_handler_4784_, v_x_4785_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4788_, lean_object* v_inst_4789_, lean_object* v_client_4790_, lean_object* v_handler_4791_, lean_object* v_config_4792_, lean_object* v_extensions_4793_, lean_object* v_a_4794_){
_start:
{
lean_object* v___f_4796_; lean_object* v___x_4797_; uint8_t v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___f_4796_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4796_, 0, v_config_4792_);
lean_closure_set(v___f_4796_, 1, v_client_4790_);
lean_closure_set(v___f_4796_, 2, v_extensions_4793_);
lean_closure_set(v___f_4796_, 3, v_inst_4788_);
lean_closure_set(v___f_4796_, 4, v_inst_4789_);
lean_closure_set(v___f_4796_, 5, v_handler_4791_);
v___x_4797_ = lean_unsigned_to_nat(0u);
v___x_4798_ = 0;
lean_inc_ref(v_a_4794_);
v___x_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4799_, 0, v_a_4794_);
v___x_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4799_);
v___x_4801_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4797_, v___x_4798_, v___x_4800_, v___f_4796_);
return v___x_4801_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4802_, lean_object* v_inst_4803_, lean_object* v_client_4804_, lean_object* v_handler_4805_, lean_object* v_config_4806_, lean_object* v_extensions_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v_res_4810_; 
v_res_4810_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4802_, v_inst_4803_, v_client_4804_, v_handler_4805_, v_config_4806_, v_extensions_4807_, v_a_4808_);
lean_dec_ref(v_a_4808_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4811_, lean_object* v_00_u03c3_4812_, lean_object* v_inst_4813_, lean_object* v_inst_4814_, lean_object* v_client_4815_, lean_object* v_handler_4816_, lean_object* v_config_4817_, lean_object* v_extensions_4818_, lean_object* v_a_4819_){
_start:
{
lean_object* v___x_4821_; 
v___x_4821_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4813_, v_inst_4814_, v_client_4815_, v_handler_4816_, v_config_4817_, v_extensions_4818_, v_a_4819_);
return v___x_4821_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4822_, lean_object* v_00_u03c3_4823_, lean_object* v_inst_4824_, lean_object* v_inst_4825_, lean_object* v_client_4826_, lean_object* v_handler_4827_, lean_object* v_config_4828_, lean_object* v_extensions_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l_Std_Http_Server_serveConnection(v_t_4822_, v_00_u03c3_4823_, v_inst_4824_, v_inst_4825_, v_client_4826_, v_handler_4827_, v_config_4828_, v_extensions_4829_, v_a_4830_);
lean_dec_ref(v_a_4830_);
return v_res_4832_;
}
}
lean_object* runtime_initialize_Std_Async_TCP(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_ContextAsync(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Transport(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Handler(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Server_Connection(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_ContextAsync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Transport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Protocol_H1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server_Handler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Server_Connection(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Async_TCP(uint8_t builtin);
lean_object* initialize_Std_Async_ContextAsync(uint8_t builtin);
lean_object* initialize_Std_Http_Transport(uint8_t builtin);
lean_object* initialize_Std_Http_Protocol_H1(uint8_t builtin);
lean_object* initialize_Std_Http_Server_Config(uint8_t builtin);
lean_object* initialize_Std_Http_Server_Handler(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Server_Connection(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Async_TCP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_ContextAsync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Transport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Protocol_H1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Server_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Server_Handler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server_Connection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Server_Connection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Server_Connection(builtin);
}
#ifdef __cplusplus
}
#endif
