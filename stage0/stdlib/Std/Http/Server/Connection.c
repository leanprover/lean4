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
uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object*, lean_object*);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t, lean_object*, uint8_t);
uint16_t l_Std_Http_Status_toCode(lean_object*);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
uint8_t l_ByteArray_isEmpty(lean_object*);
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
lean_object* lean_uint16_to_nat(uint16_t);
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
v___x_407_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_402_, v___y_404_, v___x_406_, v___y_403_);
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
v___y_402_ = v___x_447_;
v___y_403_ = v___f_446_;
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
v___y_402_ = v___x_447_;
v___y_403_ = v___f_446_;
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
lean_object* v___y_1080_; uint8_t v_omitBody_1081_; lean_object* v___y_1094_; lean_object* v_reader_1098_; lean_object* v_writer_1099_; lean_object* v_config_1100_; lean_object* v_events_1101_; lean_object* v_error_1102_; lean_object* v_instant_1103_; uint8_t v_keepAlive_1104_; uint8_t v_forcedFlush_1105_; uint8_t v_pullBodyStalled_1106_; uint8_t v___y_1126_; uint8_t v___y_1127_; lean_object* v___y_1128_; 
if (lean_obj_tag(v_x_1077_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v___f_1076_);
lean_dec_ref(v_isClosed_1075_);
lean_dec_ref(v_close_1074_);
lean_dec(v_body_1073_);
lean_dec_ref(v___y_1072_);
v_a_1138_ = lean_ctor_get(v_x_1077_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_x_1077_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1140_ = v_x_1077_;
v_isShared_1141_ = v_isSharedCheck_1146_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v_x_1077_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1146_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
}
else
{
lean_object* v_writer_1147_; lean_object* v_a_1148_; lean_object* v_reader_1149_; lean_object* v_config_1150_; lean_object* v_events_1151_; lean_object* v_error_1152_; lean_object* v_instant_1153_; uint8_t v_keepAlive_1154_; uint8_t v_forcedFlush_1155_; uint8_t v_pullBodyStalled_1156_; lean_object* v_userData_1157_; lean_object* v_outputData_1158_; lean_object* v_state_1159_; lean_object* v_knownSize_1160_; lean_object* v_messageHead_1161_; uint8_t v_sentMessage_1162_; uint8_t v_userClosedBody_1163_; uint8_t v_omitBody_1164_; lean_object* v_userDataBytes_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1288_; 
v_writer_1147_ = lean_ctor_get(v___y_1072_, 1);
lean_inc_ref(v_writer_1147_);
v_a_1148_ = lean_ctor_get(v_x_1077_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v_x_1077_, 1);
v_reader_1149_ = lean_ctor_get(v___y_1072_, 0);
v_config_1150_ = lean_ctor_get(v___y_1072_, 2);
v_events_1151_ = lean_ctor_get(v___y_1072_, 3);
v_error_1152_ = lean_ctor_get(v___y_1072_, 4);
v_instant_1153_ = lean_ctor_get(v___y_1072_, 5);
v_keepAlive_1154_ = lean_ctor_get_uint8(v___y_1072_, sizeof(void*)*6);
v_forcedFlush_1155_ = lean_ctor_get_uint8(v___y_1072_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1156_ = lean_ctor_get_uint8(v___y_1072_, sizeof(void*)*6 + 2);
v_userData_1157_ = lean_ctor_get(v_writer_1147_, 0);
v_outputData_1158_ = lean_ctor_get(v_writer_1147_, 1);
v_state_1159_ = lean_ctor_get(v_writer_1147_, 2);
v_knownSize_1160_ = lean_ctor_get(v_writer_1147_, 3);
v_messageHead_1161_ = lean_ctor_get(v_writer_1147_, 4);
v_sentMessage_1162_ = lean_ctor_get_uint8(v_writer_1147_, sizeof(void*)*6);
v_userClosedBody_1163_ = lean_ctor_get_uint8(v_writer_1147_, sizeof(void*)*6 + 1);
v_omitBody_1164_ = lean_ctor_get_uint8(v_writer_1147_, sizeof(void*)*6 + 2);
v_userDataBytes_1165_ = lean_ctor_get(v_writer_1147_, 5);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_writer_1147_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1167_ = v_writer_1147_;
v_isShared_1168_ = v_isSharedCheck_1288_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_userDataBytes_1165_);
lean_inc(v_messageHead_1161_);
lean_inc(v_knownSize_1160_);
lean_inc(v_state_1159_);
lean_inc(v_outputData_1158_);
lean_inc(v_userData_1157_);
lean_dec(v_writer_1147_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1288_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___y_1170_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = lean_box(1);
v___x_1176_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1159_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_del_object(v___x_1167_);
lean_dec(v_userDataBytes_1165_);
lean_dec(v_messageHead_1161_);
lean_dec(v_knownSize_1160_);
lean_dec(v_state_1159_);
lean_dec_ref(v_outputData_1158_);
lean_dec_ref(v_userData_1157_);
lean_dec(v_a_1148_);
lean_dec_ref(v___f_1076_);
v___y_1080_ = v___y_1072_;
v_omitBody_1081_ = v_omitBody_1164_;
goto v___jp_1079_;
}
else
{
if (v_sentMessage_1162_ == 0)
{
lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1281_; 
lean_inc(v_instant_1153_);
lean_inc(v_error_1152_);
lean_inc_ref(v_events_1151_);
lean_inc_ref(v_config_1150_);
lean_inc_ref(v_reader_1149_);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___y_1072_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; lean_object* v_unused_1283_; lean_object* v_unused_1284_; lean_object* v_unused_1285_; lean_object* v_unused_1286_; lean_object* v_unused_1287_; 
v_unused_1282_ = lean_ctor_get(v___y_1072_, 5);
lean_dec(v_unused_1282_);
v_unused_1283_ = lean_ctor_get(v___y_1072_, 4);
lean_dec(v_unused_1283_);
v_unused_1284_ = lean_ctor_get(v___y_1072_, 3);
lean_dec(v_unused_1284_);
v_unused_1285_ = lean_ctor_get(v___y_1072_, 2);
lean_dec(v_unused_1285_);
v_unused_1286_ = lean_ctor_get(v___y_1072_, 1);
lean_dec(v_unused_1286_);
v_unused_1287_ = lean_ctor_get(v___y_1072_, 0);
lean_dec(v_unused_1287_);
v___x_1178_ = v___y_1072_;
v_isShared_1179_ = v_isSharedCheck_1281_;
goto v_resetjp_1177_;
}
else
{
lean_dec(v___y_1072_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1281_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_status_1180_; uint8_t v___x_1181_; uint8_t v___y_1183_; uint8_t v___y_1184_; uint8_t v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; uint8_t v___y_1201_; uint8_t v___y_1202_; lean_object* v___y_1203_; uint8_t v___y_1204_; uint8_t v___y_1207_; uint8_t v___y_1208_; uint8_t v___y_1227_; uint16_t v___x_1229_; uint16_t v___x_1230_; uint8_t v___x_1231_; 
v_status_1180_ = lean_ctor_get(v_a_1148_, 0);
v___x_1181_ = 0;
v___x_1229_ = 100;
v___x_1230_ = l_Std_Http_Status_toCode(v_status_1180_);
v___x_1231_ = lean_uint16_dec_le(v___x_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_del_object(v___x_1167_);
lean_dec(v_messageHead_1161_);
v___y_1227_ = v___x_1231_;
goto v___jp_1226_;
}
else
{
uint16_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = 200;
v___x_1233_ = lean_uint16_dec_lt(v___x_1230_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_del_object(v___x_1167_);
lean_dec(v_messageHead_1161_);
v___y_1227_ = v___x_1233_;
goto v___jp_1226_;
}
else
{
uint8_t v___x_1234_; lean_object* v___y_1236_; lean_object* v___y_1255_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
lean_del_object(v___x_1178_);
lean_dec_ref(v___f_1076_);
v___x_1234_ = 1;
v___x_1268_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1234_, v_a_1148_);
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_array_get_size(v___x_1268_);
v___x_1271_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1272_ = lean_nat_dec_lt(v___x_1269_, v___x_1270_);
if (v___x_1272_ == 0)
{
v___y_1255_ = v___x_1268_;
goto v___jp_1254_;
}
else
{
lean_object* v___f_1273_; size_t v___x_1274_; size_t v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___f_1273_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13);
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = lean_usize_of_nat(v___x_1270_);
lean_inc_ref(v___x_1268_);
v___x_1276_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1271_, v___f_1273_, v___x_1268_, v___x_1274_, v___x_1275_);
v___x_1277_ = lean_unbox(v___x_1276_);
lean_dec(v___x_1276_);
if (v___x_1277_ == 0)
{
v___y_1255_ = v___x_1268_;
goto v___jp_1254_;
}
else
{
lean_object* v___f_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___f_1278_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14);
v___x_1279_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___x_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1271_, v___f_1278_, v___x_1268_, v___x_1274_, v___x_1275_, v___x_1279_);
v___y_1255_ = v___x_1280_;
goto v___jp_1254_;
}
}
v___jp_1235_:
{
lean_object* v_message_1237_; lean_object* v___x_1238_; lean_object* v___x_2247__overap_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_message_1237_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___x_1234_, v_a_1148_, v___y_1236_);
v___x_1238_ = l_ByteArray_empty;
v___x_2247__overap_1239_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___x_1234_);
v___x_1240_ = lean_apply_2(v___x_2247__overap_1239_, v___x_1238_, v_message_1237_);
v___x_1241_ = l_ByteArray_isEmpty(v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v_data_1242_; lean_object* v_size_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1253_; 
v_data_1242_ = lean_ctor_get(v_outputData_1158_, 0);
v_size_1243_ = lean_ctor_get(v_outputData_1158_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_outputData_1158_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1245_ = v_outputData_1158_;
v_isShared_1246_ = v_isSharedCheck_1253_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_size_1243_);
lean_inc(v_data_1242_);
lean_dec(v_outputData_1158_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1253_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
lean_inc_ref(v___x_1240_);
v___x_1247_ = lean_array_push(v_data_1242_, v___x_1240_);
v___x_1248_ = lean_byte_array_size(v___x_1240_);
lean_dec_ref(v___x_1240_);
v___x_1249_ = lean_nat_add(v_size_1243_, v___x_1248_);
lean_dec(v_size_1243_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1249_);
lean_ctor_set(v___x_1245_, 0, v___x_1247_);
v___x_1251_ = v___x_1245_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
v___y_1170_ = v___x_1251_;
goto v___jp_1169_;
}
}
}
else
{
lean_dec_ref(v___x_1240_);
v___y_1170_ = v_outputData_1158_;
goto v___jp_1169_;
}
}
v___jp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_array_get_size(v___y_1255_);
v___x_1258_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1259_ = lean_nat_dec_lt(v___x_1256_, v___x_1257_);
if (v___x_1259_ == 0)
{
v___y_1236_ = v___y_1255_;
goto v___jp_1235_;
}
else
{
lean_object* v___f_1260_; size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___f_1260_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10);
v___x_1261_ = ((size_t)0ULL);
v___x_1262_ = lean_usize_of_nat(v___x_1257_);
lean_inc_ref(v___y_1255_);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1258_, v___f_1260_, v___y_1255_, v___x_1261_, v___x_1262_);
v___x_1264_ = lean_unbox(v___x_1263_);
lean_dec(v___x_1263_);
if (v___x_1264_ == 0)
{
v___y_1236_ = v___y_1255_;
goto v___jp_1235_;
}
else
{
lean_object* v___f_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___f_1265_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11);
v___x_1266_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___x_1267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1258_, v___f_1265_, v___y_1255_, v___x_1261_, v___x_1262_, v___x_1266_);
v___y_1236_ = v___x_1267_;
goto v___jp_1235_;
}
}
}
}
}
v___jp_1182_:
{
lean_object* v_machine_1188_; lean_object* v_machine_1189_; lean_object* v_reader_1190_; lean_object* v_state_1191_; 
v_machine_1188_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___x_1181_, v___y_1186_, v___y_1187_, v___y_1183_);
v_machine_1189_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___x_1181_, v_machine_1188_, v_a_1148_);
lean_dec(v_a_1148_);
v_reader_1190_ = lean_ctor_get(v_machine_1189_, 0);
v_state_1191_ = lean_ctor_get(v_reader_1190_, 0);
if (lean_obj_tag(v_state_1191_) == 7)
{
v___y_1126_ = v___y_1184_;
v___y_1127_ = v___y_1185_;
v___y_1128_ = v_machine_1189_;
goto v___jp_1125_;
}
else
{
if (v___y_1184_ == 0)
{
lean_object* v_writer_1192_; lean_object* v_config_1193_; lean_object* v_events_1194_; lean_object* v_error_1195_; lean_object* v_instant_1196_; uint8_t v_keepAlive_1197_; uint8_t v_forcedFlush_1198_; uint8_t v_pullBodyStalled_1199_; 
lean_inc_ref(v_reader_1190_);
v_writer_1192_ = lean_ctor_get(v_machine_1189_, 1);
lean_inc_ref(v_writer_1192_);
v_config_1193_ = lean_ctor_get(v_machine_1189_, 2);
lean_inc_ref(v_config_1193_);
v_events_1194_ = lean_ctor_get(v_machine_1189_, 3);
lean_inc_ref(v_events_1194_);
v_error_1195_ = lean_ctor_get(v_machine_1189_, 4);
lean_inc(v_error_1195_);
v_instant_1196_ = lean_ctor_get(v_machine_1189_, 5);
lean_inc(v_instant_1196_);
v_keepAlive_1197_ = lean_ctor_get_uint8(v_machine_1189_, sizeof(void*)*6);
v_forcedFlush_1198_ = lean_ctor_get_uint8(v_machine_1189_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1199_ = lean_ctor_get_uint8(v_machine_1189_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_1189_);
v_reader_1098_ = v_reader_1190_;
v_writer_1099_ = v_writer_1192_;
v_config_1100_ = v_config_1193_;
v_events_1101_ = v_events_1194_;
v_error_1102_ = v_error_1195_;
v_instant_1103_ = v_instant_1196_;
v_keepAlive_1104_ = v_keepAlive_1197_;
v_forcedFlush_1105_ = v_forcedFlush_1198_;
v_pullBodyStalled_1106_ = v_pullBodyStalled_1199_;
goto v___jp_1097_;
}
else
{
v___y_1126_ = v___y_1184_;
v___y_1127_ = v___y_1185_;
v___y_1128_ = v_machine_1189_;
goto v___jp_1125_;
}
}
}
v___jp_1200_:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_box(0);
v___y_1183_ = v___y_1204_;
v___y_1184_ = v___y_1201_;
v___y_1185_ = v___y_1202_;
v___y_1186_ = v___y_1203_;
v___y_1187_ = v___x_1205_;
goto v___jp_1182_;
}
v___jp_1206_:
{
lean_object* v___x_1209_; lean_object* v_machine_1211_; 
lean_inc(v_a_1148_);
v___x_1209_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1209_, 0, v_userData_1157_);
lean_ctor_set(v___x_1209_, 1, v_outputData_1158_);
lean_ctor_set(v___x_1209_, 2, v_state_1159_);
lean_ctor_set(v___x_1209_, 3, v_knownSize_1160_);
lean_ctor_set(v___x_1209_, 4, v_a_1148_);
lean_ctor_set(v___x_1209_, 5, v_userDataBytes_1165_);
lean_ctor_set_uint8(v___x_1209_, sizeof(void*)*6, v___x_1176_);
lean_ctor_set_uint8(v___x_1209_, sizeof(void*)*6 + 1, v_userClosedBody_1163_);
lean_ctor_set_uint8(v___x_1209_, sizeof(void*)*6 + 2, v_omitBody_1164_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1209_);
v_machine_1211_ = v___x_1178_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_reader_1149_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_config_1150_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_events_1151_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_error_1152_);
lean_ctor_set(v_reuseFailAlloc_1225_, 5, v_instant_1153_);
lean_ctor_set_uint8(v_reuseFailAlloc_1225_, sizeof(void*)*6, v_keepAlive_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1225_, sizeof(void*)*6 + 1, v_forcedFlush_1155_);
lean_ctor_set_uint8(v_reuseFailAlloc_1225_, sizeof(void*)*6 + 2, v_pullBodyStalled_1156_);
v_machine_1211_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1212_ = 1;
v___x_1213_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1212_, v_a_1148_);
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = lean_array_get_size(v___x_1213_);
v___x_1216_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1217_ = lean_nat_dec_lt(v___x_1214_, v___x_1215_);
if (v___x_1217_ == 0)
{
lean_dec_ref(v___x_1213_);
lean_dec_ref(v___f_1076_);
v___y_1201_ = v___y_1207_;
v___y_1202_ = v___y_1208_;
v___y_1203_ = v_machine_1211_;
v___y_1204_ = v___x_1217_;
goto v___jp_1200_;
}
else
{
size_t v___x_1218_; size_t v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1218_ = ((size_t)0ULL);
v___x_1219_ = lean_usize_of_nat(v___x_1215_);
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1216_, v___f_1076_, v___x_1213_, v___x_1218_, v___x_1219_);
v___x_1221_ = lean_unbox(v___x_1220_);
if (v___x_1221_ == 0)
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_unbox(v___x_1220_);
lean_dec(v___x_1220_);
v___y_1201_ = v___y_1207_;
v___y_1202_ = v___y_1208_;
v___y_1203_ = v_machine_1211_;
v___y_1204_ = v___x_1222_;
goto v___jp_1200_;
}
else
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_1212_, v_a_1148_, v___y_1207_);
v___x_1224_ = lean_unbox(v___x_1220_);
lean_dec(v___x_1220_);
v___y_1183_ = v___x_1224_;
v___y_1184_ = v___y_1207_;
v___y_1185_ = v___y_1208_;
v___y_1186_ = v_machine_1211_;
v___y_1187_ = v___x_1223_;
goto v___jp_1182_;
}
}
}
}
v___jp_1226_:
{
lean_object* v_state_1228_; 
v_state_1228_ = lean_ctor_get(v_reader_1149_, 0);
if (lean_obj_tag(v_state_1228_) == 7)
{
v___y_1207_ = v___y_1227_;
v___y_1208_ = v___x_1176_;
goto v___jp_1206_;
}
else
{
v___y_1207_ = v___y_1227_;
v___y_1208_ = v___y_1227_;
goto v___jp_1206_;
}
}
}
}
else
{
lean_del_object(v___x_1167_);
lean_dec(v_userDataBytes_1165_);
lean_dec(v_messageHead_1161_);
lean_dec(v_knownSize_1160_);
lean_dec(v_state_1159_);
lean_dec_ref(v_outputData_1158_);
lean_dec_ref(v_userData_1157_);
lean_dec(v_a_1148_);
lean_dec_ref(v___f_1076_);
v___y_1080_ = v___y_1072_;
v_omitBody_1081_ = v_omitBody_1164_;
goto v___jp_1079_;
}
}
v___jp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___y_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_userData_1157_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___y_1170_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_state_1159_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_knownSize_1160_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v_messageHead_1161_);
lean_ctor_set(v_reuseFailAlloc_1174_, 5, v_userDataBytes_1165_);
lean_ctor_set_uint8(v_reuseFailAlloc_1174_, sizeof(void*)*6, v_sentMessage_1162_);
lean_ctor_set_uint8(v_reuseFailAlloc_1174_, sizeof(void*)*6 + 1, v_userClosedBody_1163_);
lean_ctor_set_uint8(v_reuseFailAlloc_1174_, sizeof(void*)*6 + 2, v_omitBody_1164_);
v___x_1172_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1173_, 0, v_reader_1149_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
lean_ctor_set(v___x_1173_, 2, v_config_1150_);
lean_ctor_set(v___x_1173_, 3, v_events_1151_);
lean_ctor_set(v___x_1173_, 4, v_error_1152_);
lean_ctor_set(v___x_1173_, 5, v_instant_1153_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*6, v_keepAlive_1154_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*6 + 1, v_forcedFlush_1155_);
lean_ctor_set_uint8(v___x_1173_, sizeof(void*)*6 + 2, v_pullBodyStalled_1156_);
v___y_1080_ = v___x_1173_;
v_omitBody_1081_ = v_omitBody_1164_;
goto v___jp_1079_;
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
v___jp_1093_:
{
lean_object* v_writer_1095_; uint8_t v_omitBody_1096_; 
v_writer_1095_ = lean_ctor_get(v___y_1094_, 1);
v_omitBody_1096_ = lean_ctor_get_uint8(v_writer_1095_, sizeof(void*)*6 + 2);
v___y_1080_ = v___y_1094_;
v_omitBody_1081_ = v_omitBody_1096_;
goto v___jp_1079_;
}
v___jp_1097_:
{
lean_object* v_userData_1107_; lean_object* v_outputData_1108_; lean_object* v_knownSize_1109_; lean_object* v_messageHead_1110_; uint8_t v_sentMessage_1111_; uint8_t v_userClosedBody_1112_; uint8_t v_omitBody_1113_; lean_object* v_userDataBytes_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1123_; 
v_userData_1107_ = lean_ctor_get(v_writer_1099_, 0);
v_outputData_1108_ = lean_ctor_get(v_writer_1099_, 1);
v_knownSize_1109_ = lean_ctor_get(v_writer_1099_, 3);
v_messageHead_1110_ = lean_ctor_get(v_writer_1099_, 4);
v_sentMessage_1111_ = lean_ctor_get_uint8(v_writer_1099_, sizeof(void*)*6);
v_userClosedBody_1112_ = lean_ctor_get_uint8(v_writer_1099_, sizeof(void*)*6 + 1);
v_omitBody_1113_ = lean_ctor_get_uint8(v_writer_1099_, sizeof(void*)*6 + 2);
v_userDataBytes_1114_ = lean_ctor_get(v_writer_1099_, 5);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_writer_1099_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_writer_1099_, 2);
lean_dec(v_unused_1124_);
v___x_1116_ = v_writer_1099_;
v_isShared_1117_ = v_isSharedCheck_1123_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_userDataBytes_1114_);
lean_inc(v_messageHead_1110_);
lean_inc(v_knownSize_1109_);
lean_inc(v_outputData_1108_);
lean_inc(v_userData_1107_);
lean_dec(v_writer_1099_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1123_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1118_ = lean_box(2);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 2, v___x_1118_);
v___x_1120_ = v___x_1116_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_userData_1107_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_outputData_1108_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_knownSize_1109_);
lean_ctor_set(v_reuseFailAlloc_1122_, 4, v_messageHead_1110_);
lean_ctor_set(v_reuseFailAlloc_1122_, 5, v_userDataBytes_1114_);
lean_ctor_set_uint8(v_reuseFailAlloc_1122_, sizeof(void*)*6, v_sentMessage_1111_);
lean_ctor_set_uint8(v_reuseFailAlloc_1122_, sizeof(void*)*6 + 1, v_userClosedBody_1112_);
lean_ctor_set_uint8(v_reuseFailAlloc_1122_, sizeof(void*)*6 + 2, v_omitBody_1113_);
v___x_1120_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1121_, 0, v_reader_1098_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
lean_ctor_set(v___x_1121_, 2, v_config_1100_);
lean_ctor_set(v___x_1121_, 3, v_events_1101_);
lean_ctor_set(v___x_1121_, 4, v_error_1102_);
lean_ctor_set(v___x_1121_, 5, v_instant_1103_);
lean_ctor_set_uint8(v___x_1121_, sizeof(void*)*6, v_keepAlive_1104_);
lean_ctor_set_uint8(v___x_1121_, sizeof(void*)*6 + 1, v_forcedFlush_1105_);
lean_ctor_set_uint8(v___x_1121_, sizeof(void*)*6 + 2, v_pullBodyStalled_1106_);
v___y_1080_ = v___x_1121_;
v_omitBody_1081_ = v_omitBody_1113_;
goto v___jp_1079_;
}
}
}
v___jp_1125_:
{
if (v___y_1127_ == 0)
{
v___y_1094_ = v___y_1128_;
goto v___jp_1093_;
}
else
{
if (v___y_1126_ == 0)
{
lean_object* v_reader_1129_; lean_object* v_writer_1130_; lean_object* v_config_1131_; lean_object* v_events_1132_; lean_object* v_error_1133_; lean_object* v_instant_1134_; uint8_t v_keepAlive_1135_; uint8_t v_forcedFlush_1136_; uint8_t v_pullBodyStalled_1137_; 
v_reader_1129_ = lean_ctor_get(v___y_1128_, 0);
lean_inc_ref(v_reader_1129_);
v_writer_1130_ = lean_ctor_get(v___y_1128_, 1);
lean_inc_ref(v_writer_1130_);
v_config_1131_ = lean_ctor_get(v___y_1128_, 2);
lean_inc_ref(v_config_1131_);
v_events_1132_ = lean_ctor_get(v___y_1128_, 3);
lean_inc_ref(v_events_1132_);
v_error_1133_ = lean_ctor_get(v___y_1128_, 4);
lean_inc(v_error_1133_);
v_instant_1134_ = lean_ctor_get(v___y_1128_, 5);
lean_inc(v_instant_1134_);
v_keepAlive_1135_ = lean_ctor_get_uint8(v___y_1128_, sizeof(void*)*6);
v_forcedFlush_1136_ = lean_ctor_get_uint8(v___y_1128_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1137_ = lean_ctor_get_uint8(v___y_1128_, sizeof(void*)*6 + 2);
lean_dec_ref(v___y_1128_);
v_reader_1098_ = v_reader_1129_;
v_writer_1099_ = v_writer_1130_;
v_config_1100_ = v_config_1131_;
v_events_1101_ = v_events_1132_;
v_error_1102_ = v_error_1133_;
v_instant_1103_ = v_instant_1134_;
v_keepAlive_1104_ = v_keepAlive_1135_;
v_forcedFlush_1105_ = v_forcedFlush_1136_;
v_pullBodyStalled_1106_ = v_pullBodyStalled_1137_;
goto v___jp_1097_;
}
else
{
v___y_1094_ = v___y_1128_;
goto v___jp_1093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object* v___y_1289_, lean_object* v_body_1290_, lean_object* v_close_1291_, lean_object* v_isClosed_1292_, lean_object* v___f_1293_, lean_object* v_x_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(v___y_1289_, v_body_1290_, v_close_1291_, v_isClosed_1292_, v___f_1293_, v_x_1294_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(lean_object* v_body_1297_, lean_object* v_close_1298_, lean_object* v_isClosed_1299_, lean_object* v___f_1300_, lean_object* v_config_1301_, lean_object* v_line_1302_, lean_object* v_machine_1303_, lean_object* v_x_1304_){
_start:
{
lean_object* v___y_1307_; 
if (lean_obj_tag(v_x_1304_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v_machine_1303_);
lean_dec_ref(v_line_1302_);
lean_dec_ref(v___f_1300_);
lean_dec_ref(v_isClosed_1299_);
lean_dec_ref(v_close_1298_);
lean_dec(v_body_1297_);
v_a_1313_ = lean_ctor_get(v_x_1304_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_x_1304_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1315_ = v_x_1304_;
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v_x_1304_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1321_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
}
}
else
{
lean_object* v_a_1322_; 
v_a_1322_ = lean_ctor_get(v_x_1304_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v_x_1304_, 1);
if (lean_obj_tag(v_a_1322_) == 1)
{
lean_object* v_writer_1323_; lean_object* v_reader_1324_; lean_object* v_config_1325_; lean_object* v_events_1326_; lean_object* v_error_1327_; lean_object* v_instant_1328_; uint8_t v_keepAlive_1329_; uint8_t v_forcedFlush_1330_; uint8_t v_pullBodyStalled_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1354_; 
v_writer_1323_ = lean_ctor_get(v_machine_1303_, 1);
v_reader_1324_ = lean_ctor_get(v_machine_1303_, 0);
v_config_1325_ = lean_ctor_get(v_machine_1303_, 2);
v_events_1326_ = lean_ctor_get(v_machine_1303_, 3);
v_error_1327_ = lean_ctor_get(v_machine_1303_, 4);
v_instant_1328_ = lean_ctor_get(v_machine_1303_, 5);
v_keepAlive_1329_ = lean_ctor_get_uint8(v_machine_1303_, sizeof(void*)*6);
v_forcedFlush_1330_ = lean_ctor_get_uint8(v_machine_1303_, sizeof(void*)*6 + 1);
v_pullBodyStalled_1331_ = lean_ctor_get_uint8(v_machine_1303_, sizeof(void*)*6 + 2);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_machine_1303_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1333_ = v_machine_1303_;
v_isShared_1334_ = v_isSharedCheck_1354_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_instant_1328_);
lean_inc(v_error_1327_);
lean_inc(v_events_1326_);
lean_inc(v_config_1325_);
lean_inc(v_writer_1323_);
lean_inc(v_reader_1324_);
lean_dec(v_machine_1303_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1354_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_userData_1335_; lean_object* v_outputData_1336_; lean_object* v_state_1337_; lean_object* v_messageHead_1338_; uint8_t v_sentMessage_1339_; uint8_t v_userClosedBody_1340_; uint8_t v_omitBody_1341_; lean_object* v_userDataBytes_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1352_; 
v_userData_1335_ = lean_ctor_get(v_writer_1323_, 0);
v_outputData_1336_ = lean_ctor_get(v_writer_1323_, 1);
v_state_1337_ = lean_ctor_get(v_writer_1323_, 2);
v_messageHead_1338_ = lean_ctor_get(v_writer_1323_, 4);
v_sentMessage_1339_ = lean_ctor_get_uint8(v_writer_1323_, sizeof(void*)*6);
v_userClosedBody_1340_ = lean_ctor_get_uint8(v_writer_1323_, sizeof(void*)*6 + 1);
v_omitBody_1341_ = lean_ctor_get_uint8(v_writer_1323_, sizeof(void*)*6 + 2);
v_userDataBytes_1342_ = lean_ctor_get(v_writer_1323_, 5);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_writer_1323_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v_writer_1323_, 3);
lean_dec(v_unused_1353_);
v___x_1344_ = v_writer_1323_;
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_userDataBytes_1342_);
lean_inc(v_messageHead_1338_);
lean_inc(v_state_1337_);
lean_inc(v_outputData_1336_);
lean_inc(v_userData_1335_);
lean_dec(v_writer_1323_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1352_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 3, v_a_1322_);
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_userData_1335_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_outputData_1336_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_state_1337_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_a_1322_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v_messageHead_1338_);
lean_ctor_set(v_reuseFailAlloc_1351_, 5, v_userDataBytes_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*6, v_sentMessage_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*6 + 1, v_userClosedBody_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*6 + 2, v_omitBody_1341_);
v___x_1347_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1349_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 1, v___x_1347_);
v___x_1349_ = v___x_1333_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_reader_1324_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_config_1325_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_events_1326_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_error_1327_);
lean_ctor_set(v_reuseFailAlloc_1350_, 5, v_instant_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1350_, sizeof(void*)*6, v_keepAlive_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1350_, sizeof(void*)*6 + 1, v_forcedFlush_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1350_, sizeof(void*)*6 + 2, v_pullBodyStalled_1331_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
v___y_1307_ = v___x_1349_;
goto v___jp_1306_;
}
}
}
}
}
else
{
lean_dec(v_a_1322_);
v___y_1307_ = v_machine_1303_;
goto v___jp_1306_;
}
}
v___jp_1306_:
{
lean_object* v___f_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___f_1308_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_1308_, 0, v___y_1307_);
lean_closure_set(v___f_1308_, 1, v_body_1297_);
lean_closure_set(v___f_1308_, 2, v_close_1298_);
lean_closure_set(v___f_1308_, 3, v_isClosed_1299_);
lean_closure_set(v___f_1308_, 4, v___f_1300_);
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = 0;
v___x_1311_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_prepareResponseHead(v_config_1301_, v_line_1302_);
v___x_1312_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1309_, v___x_1310_, v___x_1311_, v___f_1308_);
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed(lean_object* v_body_1355_, lean_object* v_close_1356_, lean_object* v_isClosed_1357_, lean_object* v___f_1358_, lean_object* v_config_1359_, lean_object* v_line_1360_, lean_object* v_machine_1361_, lean_object* v_x_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6(v_body_1355_, v_close_1356_, v_isClosed_1357_, v___f_1358_, v_config_1359_, v_line_1360_, v_machine_1361_, v_x_1362_);
lean_dec_ref(v_config_1359_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1366_, lean_object* v_config_1367_, lean_object* v_machine_1368_, lean_object* v_res_1369_){
_start:
{
lean_object* v_close_1371_; lean_object* v_isClosed_1372_; lean_object* v_getKnownSize_1373_; lean_object* v_line_1374_; lean_object* v_body_1375_; lean_object* v___f_1376_; lean_object* v___f_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_close_1371_ = lean_ctor_get(v_inst_1366_, 1);
lean_inc_ref(v_close_1371_);
v_isClosed_1372_ = lean_ctor_get(v_inst_1366_, 2);
lean_inc_ref(v_isClosed_1372_);
v_getKnownSize_1373_ = lean_ctor_get(v_inst_1366_, 5);
lean_inc_ref(v_getKnownSize_1373_);
lean_dec_ref(v_inst_1366_);
v_line_1374_ = lean_ctor_get(v_res_1369_, 0);
lean_inc_ref(v_line_1374_);
v_body_1375_ = lean_ctor_get(v_res_1369_, 1);
lean_inc_n(v_body_1375_, 2);
lean_dec_ref(v_res_1369_);
v___f_1376_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___closed__0));
v___f_1377_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__6___boxed), 9, 7);
lean_closure_set(v___f_1377_, 0, v_body_1375_);
lean_closure_set(v___f_1377_, 1, v_close_1371_);
lean_closure_set(v___f_1377_, 2, v_isClosed_1372_);
lean_closure_set(v___f_1377_, 3, v___f_1376_);
lean_closure_set(v___f_1377_, 4, v_config_1367_);
lean_closure_set(v___f_1377_, 5, v_line_1374_);
lean_closure_set(v___f_1377_, 6, v_machine_1368_);
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = 0;
v___x_1380_ = lean_apply_2(v_getKnownSize_1373_, v_body_1375_, lean_box(0));
v___x_1381_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1378_, v___x_1379_, v___x_1380_, v___f_1377_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1382_, lean_object* v_config_1383_, lean_object* v_machine_1384_, lean_object* v_res_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1382_, v_config_1383_, v_machine_1384_, v_res_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1388_, lean_object* v_inst_1389_, lean_object* v_config_1390_, lean_object* v_machine_1391_, lean_object* v_res_1392_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1389_, v_config_1390_, v_machine_1391_, v_res_1392_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1395_, lean_object* v_inst_1396_, lean_object* v_config_1397_, lean_object* v_machine_1398_, lean_object* v_res_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1395_, v_inst_1396_, v_config_1397_, v_machine_1398_, v_res_1399_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v_____do__lift_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v_closed_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_closed_1405_ = lean_ctor_get_uint8(v_____do__lift_1402_, sizeof(void*)*6);
v___x_1406_ = lean_box(v_closed_1405_);
v___x_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
v___x_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v_____do__lift_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v_____do__lift_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v_____do__lift_1409_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___x_1413_, lean_object* v_x_1414_){
_start:
{
if (lean_obj_tag(v_x_1414_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v___x_1413_);
v_a_1416_ = lean_ctor_get(v_x_1414_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_x_1414_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v_x_1414_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v_x_1414_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
}
else
{
lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1433_; 
v_isSharedCheck_1433_ = !lean_is_exclusive(v_x_1414_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v_x_1414_, 0);
lean_dec(v_unused_1434_);
v___x_1426_ = v_x_1414_;
v_isShared_1427_ = v_isSharedCheck_1433_;
goto v_resetjp_1425_;
}
else
{
lean_dec(v_x_1414_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1433_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1413_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1428_);
v___x_1430_ = v___x_1426_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
return v___x_1431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___x_1435_, lean_object* v_x_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___x_1435_, v_x_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; lean_object* v_pendingProducer_1447_; lean_object* v_pendingConsumer_1448_; lean_object* v_interestWaiter_1449_; uint8_t v_closed_1450_; lean_object* v_pendingIncompleteChunk_1451_; lean_object* v_closeError_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1461_; 
v___x_1446_ = lean_st_ref_take(v___y_1444_);
v_pendingProducer_1447_ = lean_ctor_get(v___x_1446_, 0);
v_pendingConsumer_1448_ = lean_ctor_get(v___x_1446_, 1);
v_interestWaiter_1449_ = lean_ctor_get(v___x_1446_, 2);
v_closed_1450_ = lean_ctor_get_uint8(v___x_1446_, sizeof(void*)*6);
v_pendingIncompleteChunk_1451_ = lean_ctor_get(v___x_1446_, 4);
v_closeError_1452_ = lean_ctor_get(v___x_1446_, 5);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v___x_1446_, 3);
lean_dec(v_unused_1462_);
v___x_1454_ = v___x_1446_;
v_isShared_1455_ = v_isSharedCheck_1461_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_closeError_1452_);
lean_inc(v_pendingIncompleteChunk_1451_);
lean_inc(v_interestWaiter_1449_);
lean_inc(v_pendingConsumer_1448_);
lean_inc(v_pendingProducer_1447_);
lean_dec(v___x_1446_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1461_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 3, v___x_1443_);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_pendingProducer_1447_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_pendingConsumer_1448_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_interestWaiter_1449_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v_pendingIncompleteChunk_1451_);
lean_ctor_set(v_reuseFailAlloc_1460_, 5, v_closeError_1452_);
lean_ctor_set_uint8(v_reuseFailAlloc_1460_, sizeof(void*)*6, v_closed_1450_);
v___x_1457_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_st_ref_put(v___y_1444_, v___x_1457_);
v___x_1459_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___closed__1));
return v___x_1459_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_1463_, v___y_1464_);
lean_dec(v___y_1464_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_1467_, lean_object* v_requestStream_1468_, lean_object* v_keepAliveTimeout_1469_, lean_object* v_currentTimeout_1470_, lean_object* v_headerTimeout_1471_, lean_object* v_response_1472_, lean_object* v_respStream_1473_, lean_object* v_expectData_1474_, uint8_t v_handlerDispatched_1475_, lean_object* v_____r_1476_){
_start:
{
uint8_t v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1478_ = 0;
v___x_1479_ = lean_box(0);
v___x_1480_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1480_, 0, v_machine_1467_);
lean_ctor_set(v___x_1480_, 1, v_requestStream_1468_);
lean_ctor_set(v___x_1480_, 2, v_keepAliveTimeout_1469_);
lean_ctor_set(v___x_1480_, 3, v_currentTimeout_1470_);
lean_ctor_set(v___x_1480_, 4, v_headerTimeout_1471_);
lean_ctor_set(v___x_1480_, 5, v_response_1472_);
lean_ctor_set(v___x_1480_, 6, v_respStream_1473_);
lean_ctor_set(v___x_1480_, 7, v_expectData_1474_);
lean_ctor_set(v___x_1480_, 8, v___x_1479_);
lean_ctor_set_uint8(v___x_1480_, sizeof(void*)*9, v___x_1478_);
lean_ctor_set_uint8(v___x_1480_, sizeof(void*)*9 + 1, v_handlerDispatched_1475_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
v___x_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_1484_, lean_object* v_requestStream_1485_, lean_object* v_keepAliveTimeout_1486_, lean_object* v_currentTimeout_1487_, lean_object* v_headerTimeout_1488_, lean_object* v_response_1489_, lean_object* v_respStream_1490_, lean_object* v_expectData_1491_, lean_object* v_handlerDispatched_1492_, lean_object* v_____r_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v_handlerDispatched_boxed_1495_; lean_object* v_res_1496_; 
v_handlerDispatched_boxed_1495_ = lean_unbox(v_handlerDispatched_1492_);
v_res_1496_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_1484_, v_requestStream_1485_, v_keepAliveTimeout_1486_, v_currentTimeout_1487_, v_headerTimeout_1488_, v_response_1489_, v_respStream_1490_, v_expectData_1491_, v_handlerDispatched_boxed_1495_, v_____r_1493_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_1497_, lean_object* v_x_1498_){
_start:
{
if (lean_obj_tag(v_x_1498_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1508_; 
lean_dec_ref(v___f_1497_);
v_a_1500_ = lean_ctor_get(v_x_1498_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_x_1498_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1502_ = v_x_1498_;
v_isShared_1503_ = v_isSharedCheck_1508_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v_x_1498_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1508_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1506_; 
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1510_; 
v_a_1509_ = lean_ctor_get(v_x_1498_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v_x_1498_, 1);
v___x_1510_ = lean_apply_2(v___f_1497_, v_a_1509_, lean_box(0));
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_1511_, lean_object* v_x_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_1511_, v_x_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v_requestStream_1515_, lean_object* v___f_1516_, lean_object* v___f_1517_, lean_object* v_x_1518_){
_start:
{
if (lean_obj_tag(v_x_1518_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v___f_1517_);
lean_dec_ref(v___f_1516_);
lean_dec_ref(v_requestStream_1515_);
v_a_1520_ = lean_ctor_get(v_x_1518_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_x_1518_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1522_ = v_x_1518_;
v_isShared_1523_ = v_isSharedCheck_1528_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v_x_1518_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1528_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
}
}
else
{
lean_object* v_a_1529_; uint8_t v___x_1530_; 
v_a_1529_ = lean_ctor_get(v_x_1518_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v_x_1518_, 1);
v___x_1530_ = lean_unbox(v_a_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; lean_object* v___x_1534_; 
lean_dec_ref(v___f_1517_);
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = l_Std_Http_Body_Stream_close(v_requestStream_1515_);
v___x_1533_ = lean_unbox(v_a_1529_);
lean_dec(v_a_1529_);
v___x_1534_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1531_, v___x_1533_, v___x_1532_, v___f_1516_);
return v___x_1534_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_a_1529_);
lean_dec_ref(v___f_1516_);
lean_dec_ref(v_requestStream_1515_);
v___x_1535_ = lean_box(0);
v___x_1536_ = lean_apply_2(v___f_1517_, v___x_1535_, lean_box(0));
return v___x_1536_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v_requestStream_1537_, lean_object* v___f_1538_, lean_object* v___f_1539_, lean_object* v_x_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v_requestStream_1537_, v___f_1538_, v___f_1539_, v_x_1540_);
return v_res_1542_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_1543_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_1544_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___f_1551_; lean_object* v___f_1552_; 
v___x_1550_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1551_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__4));
v___f_1552_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1552_, 0, v___f_1551_);
lean_closure_set(v___f_1552_, 1, v___x_1550_);
return v___f_1552_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___f_1562_; lean_object* v___f_1563_; 
v___x_1561_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__1);
v___f_1562_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__9));
v___f_1563_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1563_, 0, v___f_1562_);
lean_closure_set(v___f_1563_, 1, v___x_1561_);
return v___f_1563_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___f_1564_; lean_object* v___x_1565_; 
v___f_1564_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__10);
v___x_1565_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_1565_, 0, lean_box(0));
lean_closure_set(v___x_1565_, 1, lean_box(0));
lean_closure_set(v___x_1565_, 2, lean_box(0));
lean_closure_set(v___x_1565_, 3, v___f_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_1566_, lean_object* v___f_1567_, lean_object* v_x_1568_){
_start:
{
if (lean_obj_tag(v_x_1568_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref(v___f_1567_);
lean_dec_ref(v___y_1566_);
v_a_1570_ = lean_ctor_get(v_x_1568_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_x_1568_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1572_ = v_x_1568_;
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v_x_1568_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
}
else
{
lean_object* v_machine_1579_; lean_object* v_requestStream_1580_; lean_object* v_keepAliveTimeout_1581_; lean_object* v_currentTimeout_1582_; lean_object* v_headerTimeout_1583_; lean_object* v_response_1584_; lean_object* v_respStream_1585_; lean_object* v_expectData_1586_; uint8_t v_handlerDispatched_1587_; lean_object* v___x_1588_; lean_object* v___f_1589_; lean_object* v___f_1590_; lean_object* v___f_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___f_1595_; lean_object* v___f_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_4870__overap_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec_ref_known(v_x_1568_, 1);
v_machine_1579_ = lean_ctor_get(v___y_1566_, 0);
lean_inc_ref(v_machine_1579_);
v_requestStream_1580_ = lean_ctor_get(v___y_1566_, 1);
lean_inc_ref_n(v_requestStream_1580_, 3);
v_keepAliveTimeout_1581_ = lean_ctor_get(v___y_1566_, 2);
lean_inc(v_keepAliveTimeout_1581_);
v_currentTimeout_1582_ = lean_ctor_get(v___y_1566_, 3);
lean_inc(v_currentTimeout_1582_);
v_headerTimeout_1583_ = lean_ctor_get(v___y_1566_, 4);
lean_inc(v_headerTimeout_1583_);
v_response_1584_ = lean_ctor_get(v___y_1566_, 5);
lean_inc_ref(v_response_1584_);
v_respStream_1585_ = lean_ctor_get(v___y_1566_, 6);
lean_inc(v_respStream_1585_);
v_expectData_1586_ = lean_ctor_get(v___y_1566_, 7);
lean_inc(v_expectData_1586_);
v_handlerDispatched_1587_ = lean_ctor_get_uint8(v___y_1566_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1566_);
v___x_1588_ = lean_box(v_handlerDispatched_1587_);
v___f_1589_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_1589_, 0, v_machine_1579_);
lean_closure_set(v___f_1589_, 1, v_requestStream_1580_);
lean_closure_set(v___f_1589_, 2, v_keepAliveTimeout_1581_);
lean_closure_set(v___f_1589_, 3, v_currentTimeout_1582_);
lean_closure_set(v___f_1589_, 4, v_headerTimeout_1583_);
lean_closure_set(v___f_1589_, 5, v_response_1584_);
lean_closure_set(v___f_1589_, 6, v_respStream_1585_);
lean_closure_set(v___f_1589_, 7, v_expectData_1586_);
lean_closure_set(v___f_1589_, 8, v___x_1588_);
lean_inc_ref(v___f_1589_);
v___f_1590_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1590_, 0, v___f_1589_);
v___f_1591_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_1591_, 0, v_requestStream_1580_);
lean_closure_set(v___f_1591_, 1, v___f_1590_);
lean_closure_set(v___f_1591_, 2, v___f_1589_);
v___x_1592_ = lean_unsigned_to_nat(0u);
v___x_1593_ = 0;
v___x_1594_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1595_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1596_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_1597_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_1598_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_1598_, 0, lean_box(0));
lean_closure_set(v___x_1598_, 1, lean_box(0));
lean_closure_set(v___x_1598_, 2, v___x_1594_);
lean_closure_set(v___x_1598_, 3, lean_box(0));
lean_closure_set(v___x_1598_, 4, lean_box(0));
lean_closure_set(v___x_1598_, 5, v___x_1597_);
lean_closure_set(v___x_1598_, 6, v___f_1567_);
v___x_4870__overap_1599_ = l_Std_Mutex_atomically___redArg(v___x_1594_, v___f_1595_, v___f_1596_, v_requestStream_1580_, v___x_1598_);
v___x_1600_ = lean_apply_1(v___x_4870__overap_1599_, lean_box(0));
v___x_1601_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1592_, v___x_1593_, v___x_1600_, v___f_1591_);
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_1602_, lean_object* v___f_1603_, lean_object* v_x_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_1602_, v___f_1603_, v_x_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___y_1607_, lean_object* v_x_1608_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v___y_1607_);
v_a_1610_ = lean_ctor_get(v_x_1608_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1612_ = v_x_1608_;
v_isShared_1613_ = v_isSharedCheck_1618_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v_x_1608_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1618_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
return v___x_1616_;
}
}
}
else
{
lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1627_; 
v_isSharedCheck_1627_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v_x_1608_, 0);
lean_dec(v_unused_1628_);
v___x_1620_ = v_x_1608_;
v_isShared_1621_ = v_isSharedCheck_1627_;
goto v_resetjp_1619_;
}
else
{
lean_dec(v_x_1608_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1627_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___y_1607_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1622_);
v___x_1624_ = v___x_1620_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___y_1629_, lean_object* v_x_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___y_1629_, v_x_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v_requestStream_1633_, lean_object* v___f_1634_, lean_object* v___y_1635_, lean_object* v_x_1636_){
_start:
{
if (lean_obj_tag(v_x_1636_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1646_; 
lean_dec_ref(v___y_1635_);
lean_dec_ref(v___f_1634_);
lean_dec_ref(v_requestStream_1633_);
v_a_1638_ = lean_ctor_get(v_x_1636_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_x_1636_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1640_ = v_x_1636_;
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v_x_1636_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
return v___x_1644_;
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1661_; 
v_a_1647_ = lean_ctor_get(v_x_1636_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_x_1636_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1649_ = v_x_1636_;
v_isShared_1650_ = v_isSharedCheck_1661_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v_x_1636_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1661_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
uint8_t v___x_1651_; 
v___x_1651_ = lean_unbox(v_a_1647_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; lean_object* v___x_1655_; 
lean_del_object(v___x_1649_);
lean_dec_ref(v___y_1635_);
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = l_Std_Http_Body_Stream_close(v_requestStream_1633_);
v___x_1654_ = lean_unbox(v_a_1647_);
lean_dec(v_a_1647_);
v___x_1655_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1652_, v___x_1654_, v___x_1653_, v___f_1634_);
return v___x_1655_;
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
lean_dec(v_a_1647_);
lean_dec_ref(v___f_1634_);
lean_dec_ref(v_requestStream_1633_);
v___x_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___y_1635_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1656_);
v___x_1658_ = v___x_1649_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v_requestStream_1662_, lean_object* v___f_1663_, lean_object* v___y_1664_, lean_object* v_x_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v_requestStream_1662_, v___f_1663_, v___y_1664_, v_x_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_config_1668_, lean_object* v_machine_1669_, lean_object* v_a_1670_, uint8_t v_requiresData_1671_, lean_object* v_expectData_1672_, lean_object* v_pendingHead_1673_, lean_object* v_x_1674_){
_start:
{
if (lean_obj_tag(v_x_1674_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1684_; 
lean_dec(v_pendingHead_1673_);
lean_dec(v_expectData_1672_);
lean_dec_ref(v_a_1670_);
lean_dec_ref(v_machine_1669_);
v_a_1676_ = lean_ctor_get(v_x_1674_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_x_1674_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1678_ = v_x_1674_;
v_isShared_1679_ = v_isSharedCheck_1684_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v_x_1674_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1684_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
return v___x_1682_;
}
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1699_; 
v_a_1685_ = lean_ctor_get(v_x_1674_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_x_1674_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1687_ = v_x_1674_;
v_isShared_1688_ = v_isSharedCheck_1699_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v_x_1674_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1699_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v_keepAliveTimeout_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1696_; 
v_keepAliveTimeout_1689_ = lean_ctor_get(v_config_1668_, 5);
lean_inc_n(v_keepAliveTimeout_1689_, 2);
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_keepAliveTimeout_1689_);
v___x_1691_ = lean_box(0);
v___x_1692_ = 0;
v___x_1693_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1693_, 0, v_machine_1669_);
lean_ctor_set(v___x_1693_, 1, v_a_1670_);
lean_ctor_set(v___x_1693_, 2, v___x_1690_);
lean_ctor_set(v___x_1693_, 3, v_keepAliveTimeout_1689_);
lean_ctor_set(v___x_1693_, 4, v___x_1691_);
lean_ctor_set(v___x_1693_, 5, v_a_1685_);
lean_ctor_set(v___x_1693_, 6, v___x_1691_);
lean_ctor_set(v___x_1693_, 7, v_expectData_1672_);
lean_ctor_set(v___x_1693_, 8, v_pendingHead_1673_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*9, v_requiresData_1671_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*9 + 1, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1694_);
v___x_1696_ = v___x_1687_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
return v___x_1697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_config_1700_, lean_object* v_machine_1701_, lean_object* v_a_1702_, lean_object* v_requiresData_1703_, lean_object* v_expectData_1704_, lean_object* v_pendingHead_1705_, lean_object* v_x_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v_requiresData_boxed_1708_; lean_object* v_res_1709_; 
v_requiresData_boxed_1708_ = lean_unbox(v_requiresData_1703_);
v_res_1709_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_config_1700_, v_machine_1701_, v_a_1702_, v_requiresData_boxed_1708_, v_expectData_1704_, v_pendingHead_1705_, v_x_1706_);
lean_dec_ref(v_config_1700_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_1710_, lean_object* v_machine_1711_, uint8_t v_requiresData_1712_, lean_object* v_expectData_1713_, lean_object* v_pendingHead_1714_, lean_object* v_x_1715_){
_start:
{
if (lean_obj_tag(v_x_1715_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_pendingHead_1714_);
lean_dec(v_expectData_1713_);
lean_dec_ref(v_machine_1711_);
lean_dec_ref(v_config_1710_);
v_a_1717_ = lean_ctor_get(v_x_1715_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_x_1715_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1719_ = v_x_1715_;
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v_x_1715_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1725_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1741_; 
v_a_1726_ = lean_ctor_get(v_x_1715_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_x_1715_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1728_ = v_x_1715_;
v_isShared_1729_ = v_isSharedCheck_1741_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v_x_1715_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1741_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___f_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1730_ = lean_box(v_requiresData_1712_);
v___f_1731_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 8, 6);
lean_closure_set(v___f_1731_, 0, v_config_1710_);
lean_closure_set(v___f_1731_, 1, v_machine_1711_);
lean_closure_set(v___f_1731_, 2, v_a_1726_);
lean_closure_set(v___f_1731_, 3, v___x_1730_);
lean_closure_set(v___f_1731_, 4, v_expectData_1713_);
lean_closure_set(v___f_1731_, 5, v_pendingHead_1714_);
v___x_1732_ = lean_box(0);
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = 0;
v___x_1735_ = l_Std_CloseableChannel_new___redArg(v___x_1732_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1735_);
v___x_1737_ = v___x_1728_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
v___x_1739_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1733_, v___x_1734_, v___x_1738_, v___f_1731_);
return v___x_1739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_1742_, lean_object* v_machine_1743_, lean_object* v_requiresData_1744_, lean_object* v_expectData_1745_, lean_object* v_pendingHead_1746_, lean_object* v_x_1747_, lean_object* v___y_1748_){
_start:
{
uint8_t v_requiresData_boxed_1749_; lean_object* v_res_1750_; 
v_requiresData_boxed_1749_ = lean_unbox(v_requiresData_1744_);
v_res_1750_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_1742_, v_machine_1743_, v_requiresData_boxed_1749_, v_expectData_1745_, v_pendingHead_1746_, v_x_1747_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_1751_, lean_object* v_____r_1752_){
_start:
{
lean_object* v___x_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = 0;
v___x_1756_ = l_Std_Http_Body_mkStream();
v___x_1757_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1754_, v___x_1755_, v___x_1756_, v___f_1751_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_1758_, lean_object* v_____r_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_1758_, v_____r_1759_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_1762_, lean_object* v_val_1763_, lean_object* v___f_1764_, lean_object* v___f_1765_, lean_object* v_x_1766_){
_start:
{
if (lean_obj_tag(v_x_1766_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v___f_1765_);
lean_dec_ref(v___f_1764_);
lean_dec(v_val_1763_);
lean_dec_ref(v_close_1762_);
v_a_1768_ = lean_ctor_get(v_x_1766_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_x_1766_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1770_ = v_x_1766_;
v_isShared_1771_ = v_isSharedCheck_1776_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v_x_1766_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1776_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
return v___x_1774_;
}
}
}
else
{
lean_object* v_a_1777_; uint8_t v___x_1778_; 
v_a_1777_ = lean_ctor_get(v_x_1766_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v_x_1766_, 1);
v___x_1778_ = lean_unbox(v_a_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; 
lean_dec_ref(v___f_1765_);
v___x_1779_ = lean_unsigned_to_nat(0u);
v___x_1780_ = lean_apply_2(v_close_1762_, v_val_1763_, lean_box(0));
v___x_1781_ = lean_unbox(v_a_1777_);
lean_dec(v_a_1777_);
v___x_1782_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1779_, v___x_1781_, v___x_1780_, v___f_1764_);
return v___x_1782_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_dec(v_a_1777_);
lean_dec_ref(v___f_1764_);
lean_dec(v_val_1763_);
lean_dec_ref(v_close_1762_);
v___x_1783_ = lean_box(0);
v___x_1784_ = lean_apply_2(v___f_1765_, v___x_1783_, lean_box(0));
return v___x_1784_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_1785_, lean_object* v_val_1786_, lean_object* v___f_1787_, lean_object* v___f_1788_, lean_object* v_x_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_1785_, v_val_1786_, v___f_1787_, v___f_1788_, v_x_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_respStream_1792_, lean_object* v_inst_1793_, lean_object* v___f_1794_, lean_object* v___f_1795_, lean_object* v_____r_1796_){
_start:
{
if (lean_obj_tag(v_respStream_1792_) == 1)
{
lean_object* v_val_1798_; lean_object* v_close_1799_; lean_object* v_isClosed_1800_; lean_object* v___f_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_val_1798_ = lean_ctor_get(v_respStream_1792_, 0);
lean_inc_n(v_val_1798_, 2);
lean_dec_ref_known(v_respStream_1792_, 1);
v_close_1799_ = lean_ctor_get(v_inst_1793_, 1);
lean_inc_ref(v_close_1799_);
v_isClosed_1800_ = lean_ctor_get(v_inst_1793_, 2);
lean_inc_ref(v_isClosed_1800_);
lean_dec_ref(v_inst_1793_);
v___f_1801_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_1801_, 0, v_close_1799_);
lean_closure_set(v___f_1801_, 1, v_val_1798_);
lean_closure_set(v___f_1801_, 2, v___f_1794_);
lean_closure_set(v___f_1801_, 3, v___f_1795_);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = 0;
v___x_1804_ = lean_apply_2(v_isClosed_1800_, v_val_1798_, lean_box(0));
v___x_1805_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1802_, v___x_1803_, v___x_1804_, v___f_1801_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
lean_dec_ref(v___f_1794_);
lean_dec_ref(v_inst_1793_);
lean_dec(v_respStream_1792_);
v___x_1806_ = lean_box(0);
v___x_1807_ = lean_apply_2(v___f_1795_, v___x_1806_, lean_box(0));
return v___x_1807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_respStream_1808_, lean_object* v_inst_1809_, lean_object* v___f_1810_, lean_object* v___f_1811_, lean_object* v_____r_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_respStream_1808_, v_inst_1809_, v___f_1810_, v___f_1811_, v_____r_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_requestStream_1815_, lean_object* v_keepAliveTimeout_1816_, lean_object* v_currentTimeout_1817_, lean_object* v_headerTimeout_1818_, lean_object* v_response_1819_, lean_object* v_respStream_1820_, uint8_t v_requiresData_1821_, lean_object* v_expectData_1822_, uint8_t v_handlerDispatched_1823_, lean_object* v_pendingHead_1824_, lean_object* v_x_1825_){
_start:
{
if (lean_obj_tag(v_x_1825_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v_pendingHead_1824_);
lean_dec(v_expectData_1822_);
lean_dec(v_respStream_1820_);
lean_dec_ref(v_response_1819_);
lean_dec(v_headerTimeout_1818_);
lean_dec(v_currentTimeout_1817_);
lean_dec(v_keepAliveTimeout_1816_);
lean_dec_ref(v_requestStream_1815_);
v_a_1827_ = lean_ctor_get(v_x_1825_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_x_1825_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1829_ = v_x_1825_;
v_isShared_1830_ = v_isSharedCheck_1835_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v_x_1825_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1835_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1857_; 
v_a_1836_ = lean_ctor_get(v_x_1825_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_x_1825_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1838_ = v_x_1825_;
v_isShared_1839_ = v_isSharedCheck_1857_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v_x_1825_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1857_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v_snd_1840_; uint8_t v___x_1841_; 
v_snd_1840_ = lean_ctor_get(v_a_1836_, 1);
v___x_1841_ = lean_unbox(v_snd_1840_);
if (v___x_1841_ == 0)
{
lean_object* v_fst_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v_fst_1842_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_fst_1842_);
lean_dec(v_a_1836_);
v___x_1843_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1843_, 0, v_fst_1842_);
lean_ctor_set(v___x_1843_, 1, v_requestStream_1815_);
lean_ctor_set(v___x_1843_, 2, v_keepAliveTimeout_1816_);
lean_ctor_set(v___x_1843_, 3, v_currentTimeout_1817_);
lean_ctor_set(v___x_1843_, 4, v_headerTimeout_1818_);
lean_ctor_set(v___x_1843_, 5, v_response_1819_);
lean_ctor_set(v___x_1843_, 6, v_respStream_1820_);
lean_ctor_set(v___x_1843_, 7, v_expectData_1822_);
lean_ctor_set(v___x_1843_, 8, v_pendingHead_1824_);
lean_ctor_set_uint8(v___x_1843_, sizeof(void*)*9, v_requiresData_1821_);
lean_ctor_set_uint8(v___x_1843_, sizeof(void*)*9 + 1, v_handlerDispatched_1823_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1844_);
v___x_1846_ = v___x_1838_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
else
{
lean_object* v_fst_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
lean_dec(v_pendingHead_1824_);
v_fst_1849_ = lean_ctor_get(v_a_1836_, 0);
lean_inc(v_fst_1849_);
lean_dec(v_a_1836_);
v___x_1850_ = lean_box(0);
v___x_1851_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_1851_, 0, v_fst_1849_);
lean_ctor_set(v___x_1851_, 1, v_requestStream_1815_);
lean_ctor_set(v___x_1851_, 2, v_keepAliveTimeout_1816_);
lean_ctor_set(v___x_1851_, 3, v_currentTimeout_1817_);
lean_ctor_set(v___x_1851_, 4, v_headerTimeout_1818_);
lean_ctor_set(v___x_1851_, 5, v_response_1819_);
lean_ctor_set(v___x_1851_, 6, v_respStream_1820_);
lean_ctor_set(v___x_1851_, 7, v_expectData_1822_);
lean_ctor_set(v___x_1851_, 8, v___x_1850_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*9, v_requiresData_1821_);
lean_ctor_set_uint8(v___x_1851_, sizeof(void*)*9 + 1, v_handlerDispatched_1823_);
v___x_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1852_);
v___x_1854_ = v___x_1838_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_requestStream_1858_, lean_object* v_keepAliveTimeout_1859_, lean_object* v_currentTimeout_1860_, lean_object* v_headerTimeout_1861_, lean_object* v_response_1862_, lean_object* v_respStream_1863_, lean_object* v_requiresData_1864_, lean_object* v_expectData_1865_, lean_object* v_handlerDispatched_1866_, lean_object* v_pendingHead_1867_, lean_object* v_x_1868_, lean_object* v___y_1869_){
_start:
{
uint8_t v_requiresData_boxed_1870_; uint8_t v_handlerDispatched_boxed_1871_; lean_object* v_res_1872_; 
v_requiresData_boxed_1870_ = lean_unbox(v_requiresData_1864_);
v_handlerDispatched_boxed_1871_ = lean_unbox(v_handlerDispatched_1866_);
v_res_1872_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_requestStream_1858_, v_keepAliveTimeout_1859_, v_currentTimeout_1860_, v_headerTimeout_1861_, v_response_1862_, v_respStream_1863_, v_requiresData_boxed_1870_, v_expectData_1865_, v_handlerDispatched_boxed_1871_, v_pendingHead_1867_, v_x_1868_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_config_1885_, lean_object* v_inst_1886_, lean_object* v___f_1887_, lean_object* v_handler_1888_, lean_object* v___f_1889_, lean_object* v_inst_1890_, lean_object* v___f_1891_, lean_object* v_connectionContext_1892_, lean_object* v_a_1893_, lean_object* v_x_1894_, lean_object* v___y_1895_){
_start:
{
switch(lean_obj_tag(v_a_1893_))
{
case 0:
{
lean_object* v_head_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1940_; 
lean_dec_ref(v_connectionContext_1892_);
lean_dec_ref(v___f_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v___f_1889_);
lean_dec(v_handler_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_inst_1886_);
v_head_1897_ = lean_ctor_get(v_a_1893_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_a_1893_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1899_ = v_a_1893_;
v_isShared_1900_ = v_isSharedCheck_1940_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_head_1897_);
lean_dec(v_a_1893_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1940_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_machine_1901_; lean_object* v_requestStream_1902_; lean_object* v_response_1903_; lean_object* v_respStream_1904_; uint8_t v_requiresData_1905_; lean_object* v_expectData_1906_; uint8_t v_handlerDispatched_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1935_; 
v_machine_1901_ = lean_ctor_get(v___y_1895_, 0);
v_requestStream_1902_ = lean_ctor_get(v___y_1895_, 1);
v_response_1903_ = lean_ctor_get(v___y_1895_, 5);
v_respStream_1904_ = lean_ctor_get(v___y_1895_, 6);
v_requiresData_1905_ = lean_ctor_get_uint8(v___y_1895_, sizeof(void*)*9);
v_expectData_1906_ = lean_ctor_get(v___y_1895_, 7);
v_handlerDispatched_1907_ = lean_ctor_get_uint8(v___y_1895_, sizeof(void*)*9 + 1);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___y_1895_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; lean_object* v_unused_1937_; lean_object* v_unused_1938_; lean_object* v_unused_1939_; 
v_unused_1936_ = lean_ctor_get(v___y_1895_, 8);
lean_dec(v_unused_1936_);
v_unused_1937_ = lean_ctor_get(v___y_1895_, 4);
lean_dec(v_unused_1937_);
v_unused_1938_ = lean_ctor_get(v___y_1895_, 3);
lean_dec(v_unused_1938_);
v_unused_1939_ = lean_ctor_get(v___y_1895_, 2);
lean_dec(v_unused_1939_);
v___x_1909_ = v___y_1895_;
v_isShared_1910_ = v_isSharedCheck_1935_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_expectData_1906_);
lean_inc(v_respStream_1904_);
lean_inc(v_response_1903_);
lean_inc(v_requestStream_1902_);
lean_inc(v_machine_1901_);
lean_dec(v___y_1895_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1935_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_lingeringTimeout_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v_lingeringTimeout_1911_ = lean_ctor_get(v_config_1885_, 4);
lean_inc(v_lingeringTimeout_1911_);
lean_dec_ref(v_config_1885_);
v___x_1912_ = lean_box(0);
lean_inc(v_head_1897_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set_tag(v___x_1899_, 1);
v___x_1914_ = v___x_1899_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_head_1897_);
v___x_1914_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
lean_inc_ref(v_requestStream_1902_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 8, v___x_1914_);
lean_ctor_set(v___x_1909_, 4, v___x_1912_);
lean_ctor_set(v___x_1909_, 3, v_lingeringTimeout_1911_);
lean_ctor_set(v___x_1909_, 2, v___x_1912_);
v___x_1916_ = v___x_1909_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_machine_1901_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_requestStream_1902_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1933_, 3, v_lingeringTimeout_1911_);
lean_ctor_set(v_reuseFailAlloc_1933_, 4, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1933_, 5, v_response_1903_);
lean_ctor_set(v_reuseFailAlloc_1933_, 6, v_respStream_1904_);
lean_ctor_set(v_reuseFailAlloc_1933_, 7, v_expectData_1906_);
lean_ctor_set(v_reuseFailAlloc_1933_, 8, v___x_1914_);
lean_ctor_set_uint8(v_reuseFailAlloc_1933_, sizeof(void*)*9, v_requiresData_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1933_, sizeof(void*)*9 + 1, v_handlerDispatched_1907_);
v___x_1916_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
uint8_t v___x_1917_; uint8_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = 0;
v___x_1918_ = 1;
v___x_1919_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_1917_, v_head_1897_, v___x_1918_);
lean_dec(v_head_1897_);
if (lean_obj_tag(v___x_1919_) == 1)
{
lean_object* v___f_1920_; lean_object* v___f_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___f_1925_; lean_object* v___f_1926_; lean_object* v___x_5061__overap_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___f_1920_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1920_, 0, v___x_1916_);
v___f_1921_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1921_, 0, v___x_1919_);
v___x_1922_ = lean_unsigned_to_nat(0u);
v___x_1923_ = 0;
v___x_1924_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1925_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_1926_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_5061__overap_1927_ = l_Std_Mutex_atomically___redArg(v___x_1924_, v___f_1925_, v___f_1926_, v_requestStream_1902_, v___f_1921_);
v___x_1928_ = lean_apply_1(v___x_5061__overap_1927_, lean_box(0));
v___x_1929_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1922_, v___x_1923_, v___x_1928_, v___f_1920_);
return v___x_1929_;
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec(v___x_1919_);
lean_dec_ref(v_requestStream_1902_);
v___x_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1916_);
v___x_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v_connectionContext_1892_);
lean_dec_ref(v___f_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v___f_1889_);
lean_dec(v_handler_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_inst_1886_);
lean_dec_ref(v_config_1885_);
v_size_1941_ = lean_ctor_get(v_a_1893_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_a_1893_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1943_ = v_a_1893_;
v_isShared_1944_ = v_isSharedCheck_1968_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_size_1941_);
lean_dec(v_a_1893_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1968_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v_machine_1945_; lean_object* v_requestStream_1946_; lean_object* v_keepAliveTimeout_1947_; lean_object* v_currentTimeout_1948_; lean_object* v_headerTimeout_1949_; lean_object* v_response_1950_; lean_object* v_respStream_1951_; uint8_t v_handlerDispatched_1952_; lean_object* v_pendingHead_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1966_; 
v_machine_1945_ = lean_ctor_get(v___y_1895_, 0);
v_requestStream_1946_ = lean_ctor_get(v___y_1895_, 1);
v_keepAliveTimeout_1947_ = lean_ctor_get(v___y_1895_, 2);
v_currentTimeout_1948_ = lean_ctor_get(v___y_1895_, 3);
v_headerTimeout_1949_ = lean_ctor_get(v___y_1895_, 4);
v_response_1950_ = lean_ctor_get(v___y_1895_, 5);
v_respStream_1951_ = lean_ctor_get(v___y_1895_, 6);
v_handlerDispatched_1952_ = lean_ctor_get_uint8(v___y_1895_, sizeof(void*)*9 + 1);
v_pendingHead_1953_ = lean_ctor_get(v___y_1895_, 8);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___y_1895_);
if (v_isSharedCheck_1966_ == 0)
{
lean_object* v_unused_1967_; 
v_unused_1967_ = lean_ctor_get(v___y_1895_, 7);
lean_dec(v_unused_1967_);
v___x_1955_ = v___y_1895_;
v_isShared_1956_ = v_isSharedCheck_1966_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_pendingHead_1953_);
lean_inc(v_respStream_1951_);
lean_inc(v_response_1950_);
lean_inc(v_headerTimeout_1949_);
lean_inc(v_currentTimeout_1948_);
lean_inc(v_keepAliveTimeout_1947_);
lean_inc(v_requestStream_1946_);
lean_inc(v_machine_1945_);
lean_dec(v___y_1895_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1966_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
uint8_t v___x_1957_; lean_object* v___x_1959_; 
v___x_1957_ = 1;
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 7, v_size_1941_);
v___x_1959_ = v___x_1955_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_machine_1945_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_requestStream_1946_);
lean_ctor_set(v_reuseFailAlloc_1965_, 2, v_keepAliveTimeout_1947_);
lean_ctor_set(v_reuseFailAlloc_1965_, 3, v_currentTimeout_1948_);
lean_ctor_set(v_reuseFailAlloc_1965_, 4, v_headerTimeout_1949_);
lean_ctor_set(v_reuseFailAlloc_1965_, 5, v_response_1950_);
lean_ctor_set(v_reuseFailAlloc_1965_, 6, v_respStream_1951_);
lean_ctor_set(v_reuseFailAlloc_1965_, 7, v_size_1941_);
lean_ctor_set(v_reuseFailAlloc_1965_, 8, v_pendingHead_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_1965_, sizeof(void*)*9 + 1, v_handlerDispatched_1952_);
v___x_1959_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1961_; 
lean_ctor_set_uint8(v___x_1959_, sizeof(void*)*9, v___x_1957_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1959_);
v___x_1961_ = v___x_1943_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
v___x_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
return v___x_1963_;
}
}
}
}
}
case 2:
{
lean_object* v_err_1969_; lean_object* v_onFailure_1970_; lean_object* v___f_1971_; lean_object* v___y_1973_; 
lean_dec_ref(v_connectionContext_1892_);
lean_dec_ref(v___f_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v___f_1889_);
lean_dec_ref(v_config_1885_);
v_err_1969_ = lean_ctor_get(v_a_1893_, 0);
lean_inc(v_err_1969_);
lean_dec_ref_known(v_a_1893_, 1);
v_onFailure_1970_ = lean_ctor_get(v_inst_1886_, 2);
lean_inc_ref(v_onFailure_1970_);
lean_dec_ref(v_inst_1886_);
v___f_1971_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_1971_, 0, v___y_1895_);
lean_closure_set(v___f_1971_, 1, v___f_1887_);
switch(lean_obj_tag(v_err_1969_))
{
case 0:
{
lean_object* v___x_1979_; 
v___x_1979_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__0));
v___y_1973_ = v___x_1979_;
goto v___jp_1972_;
}
case 1:
{
lean_object* v___x_1980_; 
v___x_1980_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__1));
v___y_1973_ = v___x_1980_;
goto v___jp_1972_;
}
case 2:
{
lean_object* v___x_1981_; 
v___x_1981_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__2));
v___y_1973_ = v___x_1981_;
goto v___jp_1972_;
}
case 3:
{
lean_object* v___x_1982_; 
v___x_1982_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__3));
v___y_1973_ = v___x_1982_;
goto v___jp_1972_;
}
case 4:
{
lean_object* v___x_1983_; 
v___x_1983_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__4));
v___y_1973_ = v___x_1983_;
goto v___jp_1972_;
}
case 5:
{
lean_object* v___x_1984_; 
v___x_1984_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__5));
v___y_1973_ = v___x_1984_;
goto v___jp_1972_;
}
case 6:
{
lean_object* v___x_1985_; 
v___x_1985_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__6));
v___y_1973_ = v___x_1985_;
goto v___jp_1972_;
}
case 7:
{
lean_object* v___x_1986_; 
v___x_1986_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__7));
v___y_1973_ = v___x_1986_;
goto v___jp_1972_;
}
case 8:
{
lean_object* v___x_1987_; 
v___x_1987_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__8));
v___y_1973_ = v___x_1987_;
goto v___jp_1972_;
}
case 9:
{
lean_object* v___x_1988_; 
v___x_1988_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__9));
v___y_1973_ = v___x_1988_;
goto v___jp_1972_;
}
case 10:
{
lean_object* v___x_1989_; 
v___x_1989_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__10));
v___y_1973_ = v___x_1989_;
goto v___jp_1972_;
}
default: 
{
lean_object* v_message_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_message_1990_ = lean_ctor_get(v_err_1969_, 0);
lean_inc_ref(v_message_1990_);
lean_dec_ref_known(v_err_1969_, 1);
v___x_1991_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___closed__11));
v___x_1992_ = lean_string_append(v___x_1991_, v_message_1990_);
lean_dec_ref(v_message_1990_);
v___y_1973_ = v___x_1992_;
goto v___jp_1972_;
}
}
v___jp_1972_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1974_ = lean_mk_io_user_error(v___y_1973_);
v___x_1975_ = lean_unsigned_to_nat(0u);
v___x_1976_ = 0;
v___x_1977_ = lean_apply_3(v_onFailure_1970_, v_handler_1888_, v___x_1974_, lean_box(0));
v___x_1978_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1975_, v___x_1976_, v___x_1977_, v___f_1971_);
return v___x_1978_;
}
}
case 4:
{
lean_object* v_requestStream_1993_; lean_object* v___f_1994_; lean_object* v___f_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; lean_object* v___x_1998_; lean_object* v___f_1999_; lean_object* v___f_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_5118__overap_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
lean_dec_ref(v_connectionContext_1892_);
lean_dec_ref(v___f_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec(v_handler_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_inst_1886_);
lean_dec_ref(v_config_1885_);
v_requestStream_1993_ = lean_ctor_get(v___y_1895_, 1);
lean_inc_ref_n(v_requestStream_1993_, 2);
lean_inc_ref(v___y_1895_);
v___f_1994_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_1994_, 0, v___y_1895_);
v___f_1995_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_1995_, 0, v_requestStream_1993_);
lean_closure_set(v___f_1995_, 1, v___f_1994_);
lean_closure_set(v___f_1995_, 2, v___y_1895_);
v___x_1996_ = lean_unsigned_to_nat(0u);
v___x_1997_ = 0;
v___x_1998_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_1999_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2000_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2001_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2002_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2002_, 0, lean_box(0));
lean_closure_set(v___x_2002_, 1, lean_box(0));
lean_closure_set(v___x_2002_, 2, v___x_1998_);
lean_closure_set(v___x_2002_, 3, lean_box(0));
lean_closure_set(v___x_2002_, 4, lean_box(0));
lean_closure_set(v___x_2002_, 5, v___x_2001_);
lean_closure_set(v___x_2002_, 6, v___f_1889_);
v___x_5118__overap_2003_ = l_Std_Mutex_atomically___redArg(v___x_1998_, v___f_1999_, v___f_2000_, v_requestStream_1993_, v___x_2002_);
v___x_2004_ = lean_apply_1(v___x_5118__overap_2003_, lean_box(0));
v___x_2005_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1996_, v___x_1997_, v___x_2004_, v___f_1995_);
return v___x_2005_;
}
case 6:
{
lean_object* v_machine_2006_; lean_object* v_requestStream_2007_; lean_object* v_respStream_2008_; uint8_t v_requiresData_2009_; lean_object* v_expectData_2010_; lean_object* v_pendingHead_2011_; lean_object* v___x_2012_; lean_object* v___f_2013_; lean_object* v___f_2014_; lean_object* v___f_2015_; lean_object* v___f_2016_; lean_object* v___f_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___f_2022_; lean_object* v___f_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_5143__overap_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_dec_ref(v_connectionContext_1892_);
lean_dec_ref(v___f_1889_);
lean_dec(v_handler_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_inst_1886_);
v_machine_2006_ = lean_ctor_get(v___y_1895_, 0);
lean_inc_ref(v_machine_2006_);
v_requestStream_2007_ = lean_ctor_get(v___y_1895_, 1);
lean_inc_ref_n(v_requestStream_2007_, 2);
v_respStream_2008_ = lean_ctor_get(v___y_1895_, 6);
lean_inc(v_respStream_2008_);
v_requiresData_2009_ = lean_ctor_get_uint8(v___y_1895_, sizeof(void*)*9);
v_expectData_2010_ = lean_ctor_get(v___y_1895_, 7);
lean_inc(v_expectData_2010_);
v_pendingHead_2011_ = lean_ctor_get(v___y_1895_, 8);
lean_inc(v_pendingHead_2011_);
lean_dec_ref(v___y_1895_);
v___x_2012_ = lean_box(v_requiresData_2009_);
v___f_2013_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 7, 5);
lean_closure_set(v___f_2013_, 0, v_config_1885_);
lean_closure_set(v___f_2013_, 1, v_machine_2006_);
lean_closure_set(v___f_2013_, 2, v___x_2012_);
lean_closure_set(v___f_2013_, 3, v_expectData_2010_);
lean_closure_set(v___f_2013_, 4, v_pendingHead_2011_);
v___f_2014_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2014_, 0, v___f_2013_);
lean_inc_ref(v___f_2014_);
v___f_2015_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2015_, 0, v___f_2014_);
v___f_2016_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2016_, 0, v_respStream_2008_);
lean_closure_set(v___f_2016_, 1, v_inst_1890_);
lean_closure_set(v___f_2016_, 2, v___f_2015_);
lean_closure_set(v___f_2016_, 3, v___f_2014_);
lean_inc_ref(v___f_2016_);
v___f_2017_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2017_, 0, v___f_2016_);
v___f_2018_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2018_, 0, v_requestStream_2007_);
lean_closure_set(v___f_2018_, 1, v___f_2017_);
lean_closure_set(v___f_2018_, 2, v___f_2016_);
v___x_2019_ = lean_unsigned_to_nat(0u);
v___x_2020_ = 0;
v___x_2021_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2022_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2023_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2024_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2025_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2025_, 0, lean_box(0));
lean_closure_set(v___x_2025_, 1, lean_box(0));
lean_closure_set(v___x_2025_, 2, v___x_2021_);
lean_closure_set(v___x_2025_, 3, lean_box(0));
lean_closure_set(v___x_2025_, 4, lean_box(0));
lean_closure_set(v___x_2025_, 5, v___x_2024_);
lean_closure_set(v___x_2025_, 6, v___f_1891_);
v___x_5143__overap_2026_ = l_Std_Mutex_atomically___redArg(v___x_2021_, v___f_2022_, v___f_2023_, v_requestStream_2007_, v___x_2025_);
v___x_2027_ = lean_apply_1(v___x_5143__overap_2026_, lean_box(0));
v___x_2028_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2019_, v___x_2020_, v___x_2027_, v___f_2018_);
return v___x_2028_;
}
case 7:
{
lean_object* v_pendingHead_2029_; 
lean_dec_ref(v___f_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v___f_1889_);
lean_dec_ref(v___f_1887_);
v_pendingHead_2029_ = lean_ctor_get(v___y_1895_, 8);
if (lean_obj_tag(v_pendingHead_2029_) == 1)
{
lean_object* v_machine_2030_; lean_object* v_requestStream_2031_; lean_object* v_keepAliveTimeout_2032_; lean_object* v_currentTimeout_2033_; lean_object* v_headerTimeout_2034_; lean_object* v_response_2035_; lean_object* v_respStream_2036_; uint8_t v_requiresData_2037_; lean_object* v_expectData_2038_; uint8_t v_handlerDispatched_2039_; lean_object* v_val_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___f_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_inc_ref(v_pendingHead_2029_);
v_machine_2030_ = lean_ctor_get(v___y_1895_, 0);
lean_inc_ref(v_machine_2030_);
v_requestStream_2031_ = lean_ctor_get(v___y_1895_, 1);
lean_inc_ref(v_requestStream_2031_);
v_keepAliveTimeout_2032_ = lean_ctor_get(v___y_1895_, 2);
lean_inc(v_keepAliveTimeout_2032_);
v_currentTimeout_2033_ = lean_ctor_get(v___y_1895_, 3);
lean_inc(v_currentTimeout_2033_);
v_headerTimeout_2034_ = lean_ctor_get(v___y_1895_, 4);
lean_inc(v_headerTimeout_2034_);
v_response_2035_ = lean_ctor_get(v___y_1895_, 5);
lean_inc_ref(v_response_2035_);
v_respStream_2036_ = lean_ctor_get(v___y_1895_, 6);
lean_inc(v_respStream_2036_);
v_requiresData_2037_ = lean_ctor_get_uint8(v___y_1895_, sizeof(void*)*9);
v_expectData_2038_ = lean_ctor_get(v___y_1895_, 7);
lean_inc(v_expectData_2038_);
v_handlerDispatched_2039_ = lean_ctor_get_uint8(v___y_1895_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_1895_);
v_val_2040_ = lean_ctor_get(v_pendingHead_2029_, 0);
lean_inc(v_val_2040_);
v___x_2041_ = lean_box(v_requiresData_2037_);
v___x_2042_ = lean_box(v_handlerDispatched_2039_);
v___f_2043_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed), 12, 10);
lean_closure_set(v___f_2043_, 0, v_requestStream_2031_);
lean_closure_set(v___f_2043_, 1, v_keepAliveTimeout_2032_);
lean_closure_set(v___f_2043_, 2, v_currentTimeout_2033_);
lean_closure_set(v___f_2043_, 3, v_headerTimeout_2034_);
lean_closure_set(v___f_2043_, 4, v_response_2035_);
lean_closure_set(v___f_2043_, 5, v_respStream_2036_);
lean_closure_set(v___f_2043_, 6, v___x_2041_);
lean_closure_set(v___f_2043_, 7, v_expectData_2038_);
lean_closure_set(v___f_2043_, 8, v___x_2042_);
lean_closure_set(v___f_2043_, 9, v_pendingHead_2029_);
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = 0;
v___x_2046_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_1886_, v_handler_1888_, v_machine_2030_, v_val_2040_, v_config_1885_, v_connectionContext_1892_);
v___x_2047_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2044_, v___x_2045_, v___x_2046_, v___f_2043_);
return v___x_2047_;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_dec_ref(v_connectionContext_1892_);
lean_dec(v_handler_1888_);
lean_dec_ref(v_inst_1886_);
lean_dec_ref(v_config_1885_);
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___y_1895_);
v___x_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
return v___x_2050_;
}
}
default: 
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec(v_a_1893_);
lean_dec_ref(v_connectionContext_1892_);
lean_dec_ref(v___f_1891_);
lean_dec_ref(v_inst_1890_);
lean_dec_ref(v___f_1889_);
lean_dec(v_handler_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_inst_1886_);
lean_dec_ref(v_config_1885_);
v___x_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___y_1895_);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_config_2054_, lean_object* v_inst_2055_, lean_object* v___f_2056_, lean_object* v_handler_2057_, lean_object* v___f_2058_, lean_object* v_inst_2059_, lean_object* v___f_2060_, lean_object* v_connectionContext_2061_, lean_object* v_a_2062_, lean_object* v_x_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_config_2054_, v_inst_2055_, v___f_2056_, v_handler_2057_, v___f_2058_, v_inst_2059_, v___f_2060_, v_connectionContext_2061_, v_a_2062_, v_x_2063_, v___y_2064_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_x_2067_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v_x_2067_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_x_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_x_2070_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_handler_2077_, lean_object* v_config_2078_, lean_object* v_connectionContext_2079_, lean_object* v_events_2080_, lean_object* v_state_2081_){
_start:
{
lean_object* v___f_2083_; lean_object* v___f_2084_; lean_object* v___f_2085_; lean_object* v___x_2086_; size_t v_sz_2087_; size_t v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_4072__overap_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___f_2083_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_2084_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 8);
lean_closure_set(v___f_2084_, 0, v_config_2078_);
lean_closure_set(v___f_2084_, 1, v_inst_2075_);
lean_closure_set(v___f_2084_, 2, v___f_2083_);
lean_closure_set(v___f_2084_, 3, v_handler_2077_);
lean_closure_set(v___f_2084_, 4, v___f_2083_);
lean_closure_set(v___f_2084_, 5, v_inst_2076_);
lean_closure_set(v___f_2084_, 6, v___f_2083_);
lean_closure_set(v___f_2084_, 7, v_connectionContext_2079_);
v___f_2085_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__1));
v___x_2086_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v_sz_2087_ = lean_array_size(v_events_2080_);
v___x_2088_ = ((size_t)0ULL);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = 0;
v___x_4072__overap_2091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2086_, v_events_2080_, v___f_2084_, v_sz_2087_, v___x_2088_, v_state_2081_);
v___x_2092_ = lean_apply_1(v___x_4072__overap_2091_, lean_box(0));
v___x_2093_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2089_, v___x_2090_, v___x_2092_, v___f_2085_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2094_, lean_object* v_inst_2095_, lean_object* v_handler_2096_, lean_object* v_config_2097_, lean_object* v_connectionContext_2098_, lean_object* v_events_2099_, lean_object* v_state_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2094_, v_inst_2095_, v_handler_2096_, v_config_2097_, v_connectionContext_2098_, v_events_2099_, v_state_2100_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2103_, lean_object* v_00_u03b2_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_handler_2107_, lean_object* v_config_2108_, lean_object* v_connectionContext_2109_, lean_object* v_events_2110_, lean_object* v_state_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2105_, v_inst_2106_, v_handler_2107_, v_config_2108_, v_connectionContext_2109_, v_events_2110_, v_state_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2114_, lean_object* v_00_u03b2_2115_, lean_object* v_inst_2116_, lean_object* v_inst_2117_, lean_object* v_handler_2118_, lean_object* v_config_2119_, lean_object* v_connectionContext_2120_, lean_object* v_events_2121_, lean_object* v_state_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2114_, v_00_u03b2_2115_, v_inst_2116_, v_inst_2117_, v_handler_2118_, v_config_2119_, v_connectionContext_2120_, v_events_2121_, v_state_2122_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2125_){
_start:
{
if (lean_obj_tag(v_x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2127_; 
v_a_2126_ = lean_ctor_get(v_x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v_x_2125_, 1);
v___x_2127_ = lean_task_pure(v_a_2126_);
return v___x_2127_;
}
else
{
lean_object* v_a_2128_; 
v_a_2128_ = lean_ctor_get(v_x_2125_, 0);
lean_inc_ref(v_a_2128_);
lean_dec_ref_known(v_x_2125_, 1);
return v_a_2128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_machine_2129_, lean_object* v_requestStream_2130_, lean_object* v_keepAliveTimeout_2131_, lean_object* v_currentTimeout_2132_, lean_object* v_headerTimeout_2133_, lean_object* v_response_2134_, lean_object* v_respStream_2135_, uint8_t v_requiresData_2136_, lean_object* v_expectData_2137_, lean_object* v_x_2138_){
_start:
{
if (lean_obj_tag(v_x_2138_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2148_; 
lean_dec(v_expectData_2137_);
lean_dec(v_respStream_2135_);
lean_dec_ref(v_response_2134_);
lean_dec(v_headerTimeout_2133_);
lean_dec(v_currentTimeout_2132_);
lean_dec(v_keepAliveTimeout_2131_);
lean_dec_ref(v_requestStream_2130_);
lean_dec_ref(v_machine_2129_);
v_a_2140_ = lean_ctor_get(v_x_2138_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_x_2138_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2142_ = v_x_2138_;
v_isShared_2143_ = v_isSharedCheck_2148_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v_x_2138_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2148_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
}
}
else
{
lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2159_; 
v_isSharedCheck_2159_ = !lean_is_exclusive(v_x_2138_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; 
v_unused_2160_ = lean_ctor_get(v_x_2138_, 0);
lean_dec(v_unused_2160_);
v___x_2150_ = v_x_2138_;
v_isShared_2151_ = v_isSharedCheck_2159_;
goto v_resetjp_2149_;
}
else
{
lean_dec(v_x_2138_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2159_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
uint8_t v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2152_ = 1;
v___x_2153_ = lean_box(0);
v___x_2154_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2154_, 0, v_machine_2129_);
lean_ctor_set(v___x_2154_, 1, v_requestStream_2130_);
lean_ctor_set(v___x_2154_, 2, v_keepAliveTimeout_2131_);
lean_ctor_set(v___x_2154_, 3, v_currentTimeout_2132_);
lean_ctor_set(v___x_2154_, 4, v_headerTimeout_2133_);
lean_ctor_set(v___x_2154_, 5, v_response_2134_);
lean_ctor_set(v___x_2154_, 6, v_respStream_2135_);
lean_ctor_set(v___x_2154_, 7, v_expectData_2137_);
lean_ctor_set(v___x_2154_, 8, v___x_2153_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*9, v_requiresData_2136_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*9 + 1, v___x_2152_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2154_);
v___x_2156_ = v___x_2150_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_machine_2161_, lean_object* v_requestStream_2162_, lean_object* v_keepAliveTimeout_2163_, lean_object* v_currentTimeout_2164_, lean_object* v_headerTimeout_2165_, lean_object* v_response_2166_, lean_object* v_respStream_2167_, lean_object* v_requiresData_2168_, lean_object* v_expectData_2169_, lean_object* v_x_2170_, lean_object* v___y_2171_){
_start:
{
uint8_t v_requiresData_boxed_2172_; lean_object* v_res_2173_; 
v_requiresData_boxed_2172_ = lean_unbox(v_requiresData_2168_);
v_res_2173_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_machine_2161_, v_requestStream_2162_, v_keepAliveTimeout_2163_, v_currentTimeout_2164_, v_headerTimeout_2165_, v_response_2166_, v_respStream_2167_, v_requiresData_boxed_2172_, v_expectData_2169_, v_x_2170_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_toFunctor_2174_, lean_object* v_response_2175_, lean_object* v___x_2176_, lean_object* v___f_2177_, lean_object* v_x_2178_){
_start:
{
if (lean_obj_tag(v_x_2178_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v___f_2177_);
lean_dec(v___x_2176_);
lean_dec_ref(v_response_2175_);
lean_dec_ref(v_toFunctor_2174_);
v_a_2180_ = lean_ctor_get(v_x_2178_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_x_2178_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2182_ = v_x_2178_;
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v_x_2178_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
return v___x_2186_;
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2203_; 
v_a_2189_ = lean_ctor_get(v_x_2178_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_x_2178_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2191_ = v_x_2178_;
v_isShared_2192_ = v_isSharedCheck_2203_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v_x_2178_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2203_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2193_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2193_, 0, lean_box(0));
lean_closure_set(v___x_2193_, 1, lean_box(0));
lean_closure_set(v___x_2193_, 2, v_toFunctor_2174_);
v___x_2194_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2194_, 0, lean_box(0));
lean_closure_set(v___x_2194_, 1, v_response_2175_);
v___x_2195_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2195_, 0, lean_box(0));
lean_closure_set(v___x_2195_, 1, lean_box(0));
lean_closure_set(v___x_2195_, 2, lean_box(0));
lean_closure_set(v___x_2195_, 3, v___x_2193_);
lean_closure_set(v___x_2195_, 4, v___x_2194_);
v___x_2196_ = 0;
lean_inc(v___x_2176_);
v___x_2197_ = l_BaseIO_chainTask___redArg(v_a_2189_, v___x_2195_, v___x_2176_, v___x_2196_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2197_);
v___x_2199_ = v___x_2191_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
v___x_2201_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2176_, v___x_2196_, v___x_2200_, v___f_2177_);
return v___x_2201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_toFunctor_2204_, lean_object* v_response_2205_, lean_object* v___x_2206_, lean_object* v___f_2207_, lean_object* v_x_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_toFunctor_2204_, v_response_2205_, v___x_2206_, v___f_2207_, v_x_2208_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2212_, lean_object* v_handler_2213_, lean_object* v_extensions_2214_, lean_object* v_connectionContext_2215_, lean_object* v_state_2216_){
_start:
{
lean_object* v___x_2218_; lean_object* v_toApplicative_2219_; lean_object* v_pendingHead_2220_; 
v___x_2218_ = l_instMonadBaseIO;
v_toApplicative_2219_ = lean_ctor_get(v___x_2218_, 0);
v_pendingHead_2220_ = lean_ctor_get(v_state_2216_, 8);
lean_inc(v_pendingHead_2220_);
if (lean_obj_tag(v_pendingHead_2220_) == 1)
{
lean_object* v_toFunctor_2221_; lean_object* v_machine_2222_; lean_object* v_requestStream_2223_; lean_object* v_keepAliveTimeout_2224_; lean_object* v_currentTimeout_2225_; lean_object* v_headerTimeout_2226_; lean_object* v_response_2227_; lean_object* v_respStream_2228_; uint8_t v_requiresData_2229_; lean_object* v_expectData_2230_; lean_object* v_val_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2253_; 
v_toFunctor_2221_ = lean_ctor_get(v_toApplicative_2219_, 0);
v_machine_2222_ = lean_ctor_get(v_state_2216_, 0);
lean_inc_ref(v_machine_2222_);
v_requestStream_2223_ = lean_ctor_get(v_state_2216_, 1);
lean_inc_ref(v_requestStream_2223_);
v_keepAliveTimeout_2224_ = lean_ctor_get(v_state_2216_, 2);
lean_inc(v_keepAliveTimeout_2224_);
v_currentTimeout_2225_ = lean_ctor_get(v_state_2216_, 3);
lean_inc(v_currentTimeout_2225_);
v_headerTimeout_2226_ = lean_ctor_get(v_state_2216_, 4);
lean_inc(v_headerTimeout_2226_);
v_response_2227_ = lean_ctor_get(v_state_2216_, 5);
lean_inc_ref(v_response_2227_);
v_respStream_2228_ = lean_ctor_get(v_state_2216_, 6);
lean_inc(v_respStream_2228_);
v_requiresData_2229_ = lean_ctor_get_uint8(v_state_2216_, sizeof(void*)*9);
v_expectData_2230_ = lean_ctor_get(v_state_2216_, 7);
lean_inc(v_expectData_2230_);
lean_dec_ref(v_state_2216_);
v_val_2231_ = lean_ctor_get(v_pendingHead_2220_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_pendingHead_2220_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2233_ = v_pendingHead_2220_;
v_isShared_2234_ = v_isSharedCheck_2253_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_val_2231_);
lean_dec(v_pendingHead_2220_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2253_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v_onRequest_2235_; lean_object* v___f_2236_; lean_object* v___x_2237_; lean_object* v___f_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___f_2242_; uint8_t v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
v_onRequest_2235_ = lean_ctor_get(v_inst_2212_, 1);
lean_inc_ref(v_onRequest_2235_);
lean_dec_ref(v_inst_2212_);
v___f_2236_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
v___x_2237_ = lean_box(v_requiresData_2229_);
lean_inc_ref(v_response_2227_);
lean_inc_ref(v_requestStream_2223_);
v___f_2238_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2238_, 0, v_machine_2222_);
lean_closure_set(v___f_2238_, 1, v_requestStream_2223_);
lean_closure_set(v___f_2238_, 2, v_keepAliveTimeout_2224_);
lean_closure_set(v___f_2238_, 3, v_currentTimeout_2225_);
lean_closure_set(v___f_2238_, 4, v_headerTimeout_2226_);
lean_closure_set(v___f_2238_, 5, v_response_2227_);
lean_closure_set(v___f_2238_, 6, v_respStream_2228_);
lean_closure_set(v___f_2238_, 7, v___x_2237_);
lean_closure_set(v___f_2238_, 8, v_expectData_2230_);
v___x_2239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2239_, 0, v_val_2231_);
lean_ctor_set(v___x_2239_, 1, v_requestStream_2223_);
lean_ctor_set(v___x_2239_, 2, v_extensions_2214_);
v___x_2240_ = lean_apply_3(v_onRequest_2235_, v_handler_2213_, v___x_2239_, v_connectionContext_2215_);
v___x_2241_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_toFunctor_2221_);
v___f_2242_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_2242_, 0, v_toFunctor_2221_);
lean_closure_set(v___f_2242_, 1, v_response_2227_);
lean_closure_set(v___f_2242_, 2, v___x_2241_);
lean_closure_set(v___f_2242_, 3, v___f_2238_);
v___x_2243_ = 0;
v___x_2244_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2244_, 0, lean_box(0));
lean_closure_set(v___x_2244_, 1, v___x_2240_);
v___x_2245_ = lean_io_as_task(v___x_2244_, v___x_2241_);
v___x_2246_ = 1;
v___x_2247_ = lean_task_bind(v___x_2245_, v___f_2236_, v___x_2241_, v___x_2246_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2247_);
v___x_2249_ = v___x_2233_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
v___x_2251_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2241_, v___x_2243_, v___x_2250_, v___f_2242_);
return v___x_2251_;
}
}
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_dec(v_pendingHead_2220_);
lean_dec_ref(v_connectionContext_2215_);
lean_dec(v_extensions_2214_);
lean_dec(v_handler_2213_);
lean_dec_ref(v_inst_2212_);
v___x_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2254_, 0, v_state_2216_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2256_, lean_object* v_handler_2257_, lean_object* v_extensions_2258_, lean_object* v_connectionContext_2259_, lean_object* v_state_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2256_, v_handler_2257_, v_extensions_2258_, v_connectionContext_2259_, v_state_2260_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2263_, lean_object* v_inst_2264_, lean_object* v_handler_2265_, lean_object* v_extensions_2266_, lean_object* v_connectionContext_2267_, lean_object* v_state_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2264_, v_handler_2265_, v_extensions_2266_, v_connectionContext_2267_, v_state_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2271_, lean_object* v_inst_2272_, lean_object* v_handler_2273_, lean_object* v_extensions_2274_, lean_object* v_connectionContext_2275_, lean_object* v_state_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2271_, v_inst_2272_, v_handler_2273_, v_extensions_2274_, v_connectionContext_2275_, v_state_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2279_, lean_object* v_____r_2280_){
_start:
{
lean_object* v_writer_2282_; lean_object* v_reader_2283_; lean_object* v_config_2284_; lean_object* v_events_2285_; lean_object* v_error_2286_; lean_object* v_instant_2287_; uint8_t v_keepAlive_2288_; uint8_t v_forcedFlush_2289_; uint8_t v_pullBodyStalled_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2317_; 
v_writer_2282_ = lean_ctor_get(v_machine_2279_, 1);
v_reader_2283_ = lean_ctor_get(v_machine_2279_, 0);
v_config_2284_ = lean_ctor_get(v_machine_2279_, 2);
v_events_2285_ = lean_ctor_get(v_machine_2279_, 3);
v_error_2286_ = lean_ctor_get(v_machine_2279_, 4);
v_instant_2287_ = lean_ctor_get(v_machine_2279_, 5);
v_keepAlive_2288_ = lean_ctor_get_uint8(v_machine_2279_, sizeof(void*)*6);
v_forcedFlush_2289_ = lean_ctor_get_uint8(v_machine_2279_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2290_ = lean_ctor_get_uint8(v_machine_2279_, sizeof(void*)*6 + 2);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_machine_2279_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2292_ = v_machine_2279_;
v_isShared_2293_ = v_isSharedCheck_2317_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_instant_2287_);
lean_inc(v_error_2286_);
lean_inc(v_events_2285_);
lean_inc(v_config_2284_);
lean_inc(v_writer_2282_);
lean_inc(v_reader_2283_);
lean_dec(v_machine_2279_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2317_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_userData_2294_; lean_object* v_outputData_2295_; lean_object* v_state_2296_; lean_object* v_knownSize_2297_; lean_object* v_messageHead_2298_; uint8_t v_sentMessage_2299_; uint8_t v_omitBody_2300_; lean_object* v_userDataBytes_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2316_; 
v_userData_2294_ = lean_ctor_get(v_writer_2282_, 0);
v_outputData_2295_ = lean_ctor_get(v_writer_2282_, 1);
v_state_2296_ = lean_ctor_get(v_writer_2282_, 2);
v_knownSize_2297_ = lean_ctor_get(v_writer_2282_, 3);
v_messageHead_2298_ = lean_ctor_get(v_writer_2282_, 4);
v_sentMessage_2299_ = lean_ctor_get_uint8(v_writer_2282_, sizeof(void*)*6);
v_omitBody_2300_ = lean_ctor_get_uint8(v_writer_2282_, sizeof(void*)*6 + 2);
v_userDataBytes_2301_ = lean_ctor_get(v_writer_2282_, 5);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_writer_2282_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2303_ = v_writer_2282_;
v_isShared_2304_ = v_isSharedCheck_2316_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_userDataBytes_2301_);
lean_inc(v_messageHead_2298_);
lean_inc(v_knownSize_2297_);
lean_inc(v_state_2296_);
lean_inc(v_outputData_2295_);
lean_inc(v_userData_2294_);
lean_dec(v_writer_2282_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2316_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
uint8_t v___x_2305_; lean_object* v___x_2307_; 
v___x_2305_ = 1;
if (v_isShared_2304_ == 0)
{
v___x_2307_ = v___x_2303_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_userData_2294_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_outputData_2295_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v_state_2296_);
lean_ctor_set(v_reuseFailAlloc_2315_, 3, v_knownSize_2297_);
lean_ctor_set(v_reuseFailAlloc_2315_, 4, v_messageHead_2298_);
lean_ctor_set(v_reuseFailAlloc_2315_, 5, v_userDataBytes_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2315_, sizeof(void*)*6, v_sentMessage_2299_);
lean_ctor_set_uint8(v_reuseFailAlloc_2315_, sizeof(void*)*6 + 2, v_omitBody_2300_);
v___x_2307_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2309_; 
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*6 + 1, v___x_2305_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 1, v___x_2307_);
v___x_2309_ = v___x_2292_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_reader_2283_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_config_2284_);
lean_ctor_set(v_reuseFailAlloc_2314_, 3, v_events_2285_);
lean_ctor_set(v_reuseFailAlloc_2314_, 4, v_error_2286_);
lean_ctor_set(v_reuseFailAlloc_2314_, 5, v_instant_2287_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*6, v_keepAlive_2288_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*6 + 1, v_forcedFlush_2289_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*6 + 2, v_pullBodyStalled_2290_);
v___x_2309_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2310_ = lean_box(0);
v___x_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
return v___x_2313_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2318_, lean_object* v_____r_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2318_, v_____r_2319_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2322_, lean_object* v_x2_2323_){
_start:
{
lean_object* v_data_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_data_2324_ = lean_ctor_get(v_x2_2323_, 0);
v___x_2325_ = lean_byte_array_size(v_data_2324_);
v___x_2326_ = lean_nat_add(v_x1_2322_, v___x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2327_, lean_object* v_x2_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2327_, v_x2_2328_);
lean_dec_ref(v_x2_2328_);
lean_dec(v_x1_2327_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2330_, lean_object* v_machine_2331_, lean_object* v_isClosed_2332_, lean_object* v___f_2333_, lean_object* v___f_2334_, lean_object* v_x_2335_){
_start:
{
lean_object* v___y_2338_; 
if (lean_obj_tag(v_x_2335_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2351_; 
lean_dec_ref(v___f_2334_);
lean_dec_ref(v___f_2333_);
lean_dec_ref(v_isClosed_2332_);
lean_dec_ref(v_machine_2331_);
lean_dec(v_body_2330_);
v_a_2343_ = lean_ctor_get(v_x_2335_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_x_2335_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2345_ = v_x_2335_;
v_isShared_2346_ = v_isSharedCheck_2351_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v_x_2335_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2351_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; 
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2415_; 
v_a_2352_ = lean_ctor_get(v_x_2335_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_x_2335_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2354_ = v_x_2335_;
v_isShared_2355_ = v_isSharedCheck_2415_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v_x_2335_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2415_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
if (lean_obj_tag(v_a_2352_) == 0)
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
lean_dec_ref(v___f_2334_);
lean_dec_ref(v___f_2333_);
lean_dec_ref(v_isClosed_2332_);
v___x_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2356_, 0, v_body_2330_);
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v_machine_2331_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2357_);
v___x_2359_ = v___x_2354_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
return v___x_2360_;
}
}
else
{
lean_object* v_val_2362_; 
lean_del_object(v___x_2354_);
v_val_2362_ = lean_ctor_get(v_a_2352_, 0);
lean_inc(v_val_2362_);
lean_dec_ref_known(v_a_2352_, 1);
if (lean_obj_tag(v_val_2362_) == 0)
{
lean_object* v___x_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec_ref(v___f_2334_);
lean_dec_ref(v_machine_2331_);
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = 0;
v___x_2365_ = lean_apply_2(v_isClosed_2332_, v_body_2330_, lean_box(0));
v___x_2366_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2363_, v___x_2364_, v___x_2365_, v___f_2333_);
return v___x_2366_;
}
else
{
lean_object* v_val_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
lean_dec_ref(v___f_2333_);
lean_dec_ref(v_isClosed_2332_);
v_val_2367_ = lean_ctor_get(v_val_2362_, 0);
lean_inc(v_val_2367_);
lean_dec_ref_known(v_val_2362_, 1);
v___x_2368_ = lean_unsigned_to_nat(1u);
v___x_2369_ = lean_mk_empty_array_with_capacity(v___x_2368_);
v___x_2370_ = lean_array_push(v___x_2369_, v_val_2367_);
v___x_2371_ = lean_array_get_size(v___x_2370_);
v___x_2372_ = lean_unsigned_to_nat(0u);
v___x_2373_ = lean_nat_dec_eq(v___x_2371_, v___x_2372_);
if (v___x_2373_ == 0)
{
lean_object* v_reader_2374_; lean_object* v_writer_2375_; lean_object* v_config_2376_; lean_object* v_events_2377_; lean_object* v_error_2378_; lean_object* v_instant_2379_; uint8_t v_keepAlive_2380_; uint8_t v_forcedFlush_2381_; uint8_t v_pullBodyStalled_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2414_; 
v_reader_2374_ = lean_ctor_get(v_machine_2331_, 0);
v_writer_2375_ = lean_ctor_get(v_machine_2331_, 1);
v_config_2376_ = lean_ctor_get(v_machine_2331_, 2);
v_events_2377_ = lean_ctor_get(v_machine_2331_, 3);
v_error_2378_ = lean_ctor_get(v_machine_2331_, 4);
v_instant_2379_ = lean_ctor_get(v_machine_2331_, 5);
v_keepAlive_2380_ = lean_ctor_get_uint8(v_machine_2331_, sizeof(void*)*6);
v_forcedFlush_2381_ = lean_ctor_get_uint8(v_machine_2331_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2382_ = lean_ctor_get_uint8(v_machine_2331_, sizeof(void*)*6 + 2);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_machine_2331_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2384_ = v_machine_2331_;
v_isShared_2385_ = v_isSharedCheck_2414_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_instant_2379_);
lean_inc(v_error_2378_);
lean_inc(v_events_2377_);
lean_inc(v_config_2376_);
lean_inc(v_writer_2375_);
lean_inc(v_reader_2374_);
lean_dec(v_machine_2331_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2414_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___y_2387_; lean_object* v___x_2409_; uint8_t v___x_2410_; 
v___x_2409_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_2410_ = lean_nat_dec_lt(v___x_2372_, v___x_2371_);
if (v___x_2410_ == 0)
{
lean_dec_ref(v___f_2334_);
v___y_2387_ = v___x_2372_;
goto v___jp_2386_;
}
else
{
size_t v___x_2411_; size_t v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = ((size_t)0ULL);
v___x_2412_ = lean_usize_of_nat(v___x_2371_);
lean_inc_ref(v___x_2370_);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2409_, v___f_2334_, v___x_2370_, v___x_2411_, v___x_2412_, v___x_2372_);
v___y_2387_ = v___x_2413_;
goto v___jp_2386_;
}
v___jp_2386_:
{
lean_object* v_userData_2388_; lean_object* v_outputData_2389_; lean_object* v_state_2390_; lean_object* v_knownSize_2391_; lean_object* v_messageHead_2392_; uint8_t v_sentMessage_2393_; uint8_t v_userClosedBody_2394_; uint8_t v_omitBody_2395_; lean_object* v_userDataBytes_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2408_; 
v_userData_2388_ = lean_ctor_get(v_writer_2375_, 0);
v_outputData_2389_ = lean_ctor_get(v_writer_2375_, 1);
v_state_2390_ = lean_ctor_get(v_writer_2375_, 2);
v_knownSize_2391_ = lean_ctor_get(v_writer_2375_, 3);
v_messageHead_2392_ = lean_ctor_get(v_writer_2375_, 4);
v_sentMessage_2393_ = lean_ctor_get_uint8(v_writer_2375_, sizeof(void*)*6);
v_userClosedBody_2394_ = lean_ctor_get_uint8(v_writer_2375_, sizeof(void*)*6 + 1);
v_omitBody_2395_ = lean_ctor_get_uint8(v_writer_2375_, sizeof(void*)*6 + 2);
v_userDataBytes_2396_ = lean_ctor_get(v_writer_2375_, 5);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_writer_2375_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2398_ = v_writer_2375_;
v_isShared_2399_ = v_isSharedCheck_2408_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_userDataBytes_2396_);
lean_inc(v_messageHead_2392_);
lean_inc(v_knownSize_2391_);
lean_inc(v_state_2390_);
lean_inc(v_outputData_2389_);
lean_inc(v_userData_2388_);
lean_dec(v_writer_2375_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2408_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2400_ = l_Array_append___redArg(v_userData_2388_, v___x_2370_);
lean_dec_ref(v___x_2370_);
v___x_2401_ = lean_nat_add(v_userDataBytes_2396_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec(v_userDataBytes_2396_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 5, v___x_2401_);
lean_ctor_set(v___x_2398_, 0, v___x_2400_);
v___x_2403_ = v___x_2398_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_outputData_2389_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_state_2390_);
lean_ctor_set(v_reuseFailAlloc_2407_, 3, v_knownSize_2391_);
lean_ctor_set(v_reuseFailAlloc_2407_, 4, v_messageHead_2392_);
lean_ctor_set(v_reuseFailAlloc_2407_, 5, v___x_2401_);
lean_ctor_set_uint8(v_reuseFailAlloc_2407_, sizeof(void*)*6, v_sentMessage_2393_);
lean_ctor_set_uint8(v_reuseFailAlloc_2407_, sizeof(void*)*6 + 1, v_userClosedBody_2394_);
lean_ctor_set_uint8(v_reuseFailAlloc_2407_, sizeof(void*)*6 + 2, v_omitBody_2395_);
v___x_2403_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2405_; 
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 1, v___x_2403_);
v___x_2405_ = v___x_2384_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_reader_2374_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2406_, 2, v_config_2376_);
lean_ctor_set(v_reuseFailAlloc_2406_, 3, v_events_2377_);
lean_ctor_set(v_reuseFailAlloc_2406_, 4, v_error_2378_);
lean_ctor_set(v_reuseFailAlloc_2406_, 5, v_instant_2379_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, sizeof(void*)*6, v_keepAlive_2380_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, sizeof(void*)*6 + 1, v_forcedFlush_2381_);
lean_ctor_set_uint8(v_reuseFailAlloc_2406_, sizeof(void*)*6 + 2, v_pullBodyStalled_2382_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
v___y_2338_ = v___x_2405_;
goto v___jp_2337_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2370_);
lean_dec_ref(v___f_2334_);
v___y_2338_ = v_machine_2331_;
goto v___jp_2337_;
}
}
}
}
}
v___jp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2339_, 0, v_body_2330_);
v___x_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___y_2338_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
v___x_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
return v___x_2342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_2416_, lean_object* v_machine_2417_, lean_object* v_isClosed_2418_, lean_object* v___f_2419_, lean_object* v___f_2420_, lean_object* v_x_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_2416_, v_machine_2417_, v_isClosed_2418_, v___f_2419_, v___f_2420_, v_x_2421_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_2425_, lean_object* v_machine_2426_, lean_object* v_body_2427_){
_start:
{
lean_object* v_close_2429_; lean_object* v_isClosed_2430_; lean_object* v_tryRecv_2431_; lean_object* v___f_2432_; lean_object* v___f_2433_; lean_object* v___f_2434_; lean_object* v___f_2435_; lean_object* v___f_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_close_2429_ = lean_ctor_get(v_inst_2425_, 1);
lean_inc_ref(v_close_2429_);
v_isClosed_2430_ = lean_ctor_get(v_inst_2425_, 2);
lean_inc_ref(v_isClosed_2430_);
v_tryRecv_2431_ = lean_ctor_get(v_inst_2425_, 4);
lean_inc_ref(v_tryRecv_2431_);
lean_dec_ref(v_inst_2425_);
lean_inc_ref(v_machine_2426_);
v___f_2432_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2432_, 0, v_machine_2426_);
lean_inc_ref(v___f_2432_);
v___f_2433_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2433_, 0, v___f_2432_);
lean_inc_n(v_body_2427_, 2);
v___f_2434_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_2434_, 0, v_close_2429_);
lean_closure_set(v___f_2434_, 1, v_body_2427_);
lean_closure_set(v___f_2434_, 2, v___f_2433_);
lean_closure_set(v___f_2434_, 3, v___f_2432_);
v___f_2435_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_2436_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_2436_, 0, v_body_2427_);
lean_closure_set(v___f_2436_, 1, v_machine_2426_);
lean_closure_set(v___f_2436_, 2, v_isClosed_2430_);
lean_closure_set(v___f_2436_, 3, v___f_2434_);
lean_closure_set(v___f_2436_, 4, v___f_2435_);
v___x_2437_ = lean_unsigned_to_nat(0u);
v___x_2438_ = 0;
v___x_2439_ = lean_apply_2(v_tryRecv_2431_, v_body_2427_, lean_box(0));
v___x_2440_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2437_, v___x_2438_, v___x_2439_, v___f_2436_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_2441_, lean_object* v_machine_2442_, lean_object* v_body_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2441_, v_machine_2442_, v_body_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_2446_, lean_object* v_inst_2447_, lean_object* v_machine_2448_, lean_object* v_body_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_2447_, v_machine_2448_, v_body_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_2452_, lean_object* v_inst_2453_, lean_object* v_machine_2454_, lean_object* v_body_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_2452_, v_inst_2453_, v_machine_2454_, v_body_2455_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_2464_, lean_object* v_____r_2465_, lean_object* v_st_2466_){
_start:
{
lean_object* v_machine_2468_; lean_object* v_requestStream_2469_; lean_object* v_keepAliveTimeout_2470_; lean_object* v_currentTimeout_2471_; lean_object* v_headerTimeout_2472_; lean_object* v_response_2473_; lean_object* v_respStream_2474_; uint8_t v_requiresData_2475_; lean_object* v_expectData_2476_; uint8_t v_handlerDispatched_2477_; lean_object* v_pendingHead_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2560_; 
v_machine_2468_ = lean_ctor_get(v_st_2466_, 0);
v_requestStream_2469_ = lean_ctor_get(v_st_2466_, 1);
v_keepAliveTimeout_2470_ = lean_ctor_get(v_st_2466_, 2);
v_currentTimeout_2471_ = lean_ctor_get(v_st_2466_, 3);
v_headerTimeout_2472_ = lean_ctor_get(v_st_2466_, 4);
v_response_2473_ = lean_ctor_get(v_st_2466_, 5);
v_respStream_2474_ = lean_ctor_get(v_st_2466_, 6);
v_requiresData_2475_ = lean_ctor_get_uint8(v_st_2466_, sizeof(void*)*9);
v_expectData_2476_ = lean_ctor_get(v_st_2466_, 7);
v_handlerDispatched_2477_ = lean_ctor_get_uint8(v_st_2466_, sizeof(void*)*9 + 1);
v_pendingHead_2478_ = lean_ctor_get(v_st_2466_, 8);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_st_2466_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2480_ = v_st_2466_;
v_isShared_2481_ = v_isSharedCheck_2560_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_pendingHead_2478_);
lean_inc(v_expectData_2476_);
lean_inc(v_respStream_2474_);
lean_inc(v_response_2473_);
lean_inc(v_headerTimeout_2472_);
lean_inc(v_currentTimeout_2471_);
lean_inc(v_keepAliveTimeout_2470_);
lean_inc(v_requestStream_2469_);
lean_inc(v_machine_2468_);
lean_dec(v_st_2466_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2560_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___y_2483_; lean_object* v_reader_2492_; lean_object* v_state_2493_; 
v_reader_2492_ = lean_ctor_get(v_machine_2468_, 0);
lean_inc_ref(v_reader_2492_);
v_state_2493_ = lean_ctor_get(v_reader_2492_, 0);
lean_inc(v_state_2493_);
if (lean_obj_tag(v_state_2493_) == 6)
{
lean_dec_ref(v_reader_2492_);
lean_dec_ref(v_val_2464_);
v___y_2483_ = v_machine_2468_;
goto v___jp_2482_;
}
else
{
if (lean_obj_tag(v_state_2493_) == 7)
{
lean_dec_ref_known(v_state_2493_, 1);
lean_dec_ref(v_reader_2492_);
lean_dec_ref(v_val_2464_);
v___y_2483_ = v_machine_2468_;
goto v___jp_2482_;
}
else
{
lean_object* v_input_2494_; lean_object* v_writer_2495_; lean_object* v_config_2496_; lean_object* v_events_2497_; lean_object* v_error_2498_; lean_object* v_instant_2499_; uint8_t v_keepAlive_2500_; uint8_t v_forcedFlush_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2558_; 
v_input_2494_ = lean_ctor_get(v_reader_2492_, 1);
lean_inc_ref(v_input_2494_);
v_writer_2495_ = lean_ctor_get(v_machine_2468_, 1);
v_config_2496_ = lean_ctor_get(v_machine_2468_, 2);
v_events_2497_ = lean_ctor_get(v_machine_2468_, 3);
v_error_2498_ = lean_ctor_get(v_machine_2468_, 4);
v_instant_2499_ = lean_ctor_get(v_machine_2468_, 5);
v_keepAlive_2500_ = lean_ctor_get_uint8(v_machine_2468_, sizeof(void*)*6);
v_forcedFlush_2501_ = lean_ctor_get_uint8(v_machine_2468_, sizeof(void*)*6 + 1);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_machine_2468_);
if (v_isSharedCheck_2558_ == 0)
{
lean_object* v_unused_2559_; 
v_unused_2559_ = lean_ctor_get(v_machine_2468_, 0);
lean_dec(v_unused_2559_);
v___x_2503_ = v_machine_2468_;
v_isShared_2504_ = v_isSharedCheck_2558_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_instant_2499_);
lean_inc(v_error_2498_);
lean_inc(v_events_2497_);
lean_inc(v_config_2496_);
lean_inc(v_writer_2495_);
lean_dec(v_machine_2468_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2558_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v_messageHead_2505_; lean_object* v_messageCount_2506_; lean_object* v_bodyBytesRead_2507_; lean_object* v_headerBytesRead_2508_; uint8_t v_noMoreInput_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2555_; 
v_messageHead_2505_ = lean_ctor_get(v_reader_2492_, 2);
v_messageCount_2506_ = lean_ctor_get(v_reader_2492_, 3);
v_bodyBytesRead_2507_ = lean_ctor_get(v_reader_2492_, 4);
v_headerBytesRead_2508_ = lean_ctor_get(v_reader_2492_, 5);
v_noMoreInput_2509_ = lean_ctor_get_uint8(v_reader_2492_, sizeof(void*)*6);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_reader_2492_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; lean_object* v_unused_2557_; 
v_unused_2556_ = lean_ctor_get(v_reader_2492_, 1);
lean_dec(v_unused_2556_);
v_unused_2557_ = lean_ctor_get(v_reader_2492_, 0);
lean_dec(v_unused_2557_);
v___x_2511_ = v_reader_2492_;
v_isShared_2512_ = v_isSharedCheck_2555_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_headerBytesRead_2508_);
lean_inc(v_bodyBytesRead_2507_);
lean_inc(v_messageCount_2506_);
lean_inc(v_messageHead_2505_);
lean_dec(v_reader_2492_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2555_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v_array_2513_; lean_object* v_idx_2514_; uint8_t v___x_2515_; lean_object* v___y_2517_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v_array_2513_ = lean_ctor_get(v_input_2494_, 0);
lean_inc_ref(v_array_2513_);
v_idx_2514_ = lean_ctor_get(v_input_2494_, 1);
lean_inc(v_idx_2514_);
lean_dec_ref(v_input_2494_);
v___x_2515_ = 0;
v___x_2546_ = lean_byte_array_size(v_array_2513_);
v___x_2547_ = lean_nat_dec_le(v___x_2546_, v_idx_2514_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2548_ = l_ByteArray_extract(v_array_2513_, v_idx_2514_, v___x_2546_);
lean_dec_ref(v_array_2513_);
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = lean_byte_array_size(v___x_2548_);
v___x_2551_ = lean_byte_array_size(v_val_2464_);
v___x_2552_ = lean_byte_array_copy_slice(v_val_2464_, v___x_2549_, v___x_2548_, v___x_2550_, v___x_2551_, v___x_2547_);
lean_dec_ref(v_val_2464_);
v___x_2553_ = l_ByteArray_mkIterator(v___x_2552_);
v___y_2517_ = v___x_2553_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2554_; 
lean_dec(v_idx_2514_);
lean_dec_ref(v_array_2513_);
v___x_2554_ = l_ByteArray_mkIterator(v_val_2464_);
v___y_2517_ = v___x_2554_;
goto v___jp_2516_;
}
v___jp_2516_:
{
lean_object* v_maxHeaderBytes_2518_; lean_object* v_maxStartLineLength_2519_; lean_object* v_maxChunkLineLength_2520_; lean_object* v_maxBodySize_2521_; lean_object* v_array_2522_; lean_object* v_idx_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v_maxHeaderBytes_2518_ = lean_ctor_get(v_config_2496_, 2);
v_maxStartLineLength_2519_ = lean_ctor_get(v_config_2496_, 5);
v_maxChunkLineLength_2520_ = lean_ctor_get(v_config_2496_, 13);
v_maxBodySize_2521_ = lean_ctor_get(v_config_2496_, 15);
v_array_2522_ = lean_ctor_get(v___y_2517_, 0);
v_idx_2523_ = lean_ctor_get(v___y_2517_, 1);
v___x_2524_ = lean_nat_add(v_maxBodySize_2521_, v_maxHeaderBytes_2518_);
v___x_2525_ = lean_nat_add(v___x_2524_, v_maxStartLineLength_2519_);
lean_dec(v___x_2524_);
v___x_2526_ = lean_nat_add(v___x_2525_, v_maxChunkLineLength_2520_);
lean_dec(v___x_2525_);
v___x_2527_ = lean_byte_array_size(v_array_2522_);
v___x_2528_ = lean_nat_sub(v___x_2527_, v_idx_2523_);
v___x_2529_ = lean_nat_dec_lt(v___x_2526_, v___x_2528_);
lean_dec(v___x_2528_);
lean_dec(v___x_2526_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2531_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 1, v___y_2517_);
v___x_2531_ = v___x_2511_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_state_2493_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v___y_2517_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_messageHead_2505_);
lean_ctor_set(v_reuseFailAlloc_2535_, 3, v_messageCount_2506_);
lean_ctor_set(v_reuseFailAlloc_2535_, 4, v_bodyBytesRead_2507_);
lean_ctor_set(v_reuseFailAlloc_2535_, 5, v_headerBytesRead_2508_);
lean_ctor_set_uint8(v_reuseFailAlloc_2535_, sizeof(void*)*6, v_noMoreInput_2509_);
v___x_2531_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v_machine_2533_; 
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 0, v___x_2531_);
v_machine_2533_ = v___x_2503_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_writer_2495_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v_config_2496_);
lean_ctor_set(v_reuseFailAlloc_2534_, 3, v_events_2497_);
lean_ctor_set(v_reuseFailAlloc_2534_, 4, v_error_2498_);
lean_ctor_set(v_reuseFailAlloc_2534_, 5, v_instant_2499_);
lean_ctor_set_uint8(v_reuseFailAlloc_2534_, sizeof(void*)*6, v_keepAlive_2500_);
lean_ctor_set_uint8(v_reuseFailAlloc_2534_, sizeof(void*)*6 + 1, v_forcedFlush_2501_);
v_machine_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_ctor_set_uint8(v_machine_2533_, sizeof(void*)*6 + 2, v___x_2515_);
v___y_2483_ = v_machine_2533_;
goto v___jp_2482_;
}
}
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
lean_dec(v_error_2498_);
lean_dec(v_state_2493_);
v___x_2536_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_2537_ = lean_array_push(v_events_2497_, v___x_2536_);
v___x_2538_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 1, v___y_2517_);
lean_ctor_set(v___x_2511_, 0, v___x_2538_);
v___x_2540_ = v___x_2511_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v___y_2517_);
lean_ctor_set(v_reuseFailAlloc_2545_, 2, v_messageHead_2505_);
lean_ctor_set(v_reuseFailAlloc_2545_, 3, v_messageCount_2506_);
lean_ctor_set(v_reuseFailAlloc_2545_, 4, v_bodyBytesRead_2507_);
lean_ctor_set(v_reuseFailAlloc_2545_, 5, v_headerBytesRead_2508_);
lean_ctor_set_uint8(v_reuseFailAlloc_2545_, sizeof(void*)*6, v_noMoreInput_2509_);
v___x_2540_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
v___x_2541_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 4, v___x_2541_);
lean_ctor_set(v___x_2503_, 3, v___x_2537_);
lean_ctor_set(v___x_2503_, 0, v___x_2540_);
v___x_2543_ = v___x_2503_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v_writer_2495_);
lean_ctor_set(v_reuseFailAlloc_2544_, 2, v_config_2496_);
lean_ctor_set(v_reuseFailAlloc_2544_, 3, v___x_2537_);
lean_ctor_set(v_reuseFailAlloc_2544_, 4, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2544_, 5, v_instant_2499_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*6, v_keepAlive_2500_);
lean_ctor_set_uint8(v_reuseFailAlloc_2544_, sizeof(void*)*6 + 1, v_forcedFlush_2501_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_ctor_set_uint8(v___x_2543_, sizeof(void*)*6 + 2, v___x_2515_);
v___y_2483_ = v___x_2543_;
goto v___jp_2482_;
}
}
}
}
}
}
}
}
v___jp_2482_:
{
lean_object* v___x_2485_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___y_2483_);
v___x_2485_ = v___x_2480_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___y_2483_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_requestStream_2469_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_keepAliveTimeout_2470_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_currentTimeout_2471_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_headerTimeout_2472_);
lean_ctor_set(v_reuseFailAlloc_2491_, 5, v_response_2473_);
lean_ctor_set(v_reuseFailAlloc_2491_, 6, v_respStream_2474_);
lean_ctor_set(v_reuseFailAlloc_2491_, 7, v_expectData_2476_);
lean_ctor_set(v_reuseFailAlloc_2491_, 8, v_pendingHead_2478_);
lean_ctor_set_uint8(v_reuseFailAlloc_2491_, sizeof(void*)*9, v_requiresData_2475_);
lean_ctor_set_uint8(v_reuseFailAlloc_2491_, sizeof(void*)*9 + 1, v_handlerDispatched_2477_);
v___x_2485_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
uint8_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2486_ = 0;
v___x_2487_ = lean_box(v___x_2486_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2485_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
return v___x_2490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_2561_, lean_object* v_____r_2562_, lean_object* v_st_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_2561_, v_____r_2562_, v_st_2563_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_2566_, lean_object* v_machine_2567_, lean_object* v_requestStream_2568_, lean_object* v_currentTimeout_2569_, lean_object* v_response_2570_, lean_object* v_respStream_2571_, uint8_t v_requiresData_2572_, lean_object* v_expectData_2573_, uint8_t v_handlerDispatched_2574_, lean_object* v_pendingHead_2575_, lean_object* v___f_2576_, lean_object* v_x_2577_){
_start:
{
if (lean_obj_tag(v_x_2577_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2587_; 
lean_dec_ref(v___f_2576_);
lean_dec(v_pendingHead_2575_);
lean_dec(v_expectData_2573_);
lean_dec(v_respStream_2571_);
lean_dec_ref(v_response_2570_);
lean_dec(v_currentTimeout_2569_);
lean_dec_ref(v_requestStream_2568_);
lean_dec_ref(v_machine_2567_);
v_a_2579_ = lean_ctor_get(v_x_2577_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_x_2577_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2581_ = v_x_2577_;
v_isShared_2582_ = v_isSharedCheck_2587_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v_x_2577_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2587_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
return v___x_2585_;
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v_headerTimeout_2589_; lean_object* v_second_2590_; lean_object* v_nano_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v_second_2595_; lean_object* v_nano_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v_nanos_2600_; lean_object* v___x_2601_; lean_object* v_nanos_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v_a_2588_ = lean_ctor_get(v_x_2577_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v_x_2577_, 1);
v_headerTimeout_2589_ = lean_ctor_get(v_config_2566_, 6);
v_second_2590_ = lean_ctor_get(v_a_2588_, 0);
lean_inc(v_second_2590_);
v_nano_2591_ = lean_ctor_get(v_a_2588_, 1);
lean_inc(v_nano_2591_);
lean_dec(v_a_2588_);
v___x_2592_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_2593_ = lean_int_mul(v_headerTimeout_2589_, v___x_2592_);
v___x_2594_ = l_Std_Time_Duration_ofNanoseconds(v___x_2593_);
lean_dec(v___x_2593_);
v_second_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_second_2595_);
v_nano_2596_ = lean_ctor_get(v___x_2594_, 1);
lean_inc(v_nano_2596_);
lean_dec_ref(v___x_2594_);
v___x_2597_ = lean_box(0);
v___x_2598_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_2599_ = lean_int_mul(v_second_2590_, v___x_2598_);
lean_dec(v_second_2590_);
v_nanos_2600_ = lean_int_add(v___x_2599_, v_nano_2591_);
lean_dec(v_nano_2591_);
lean_dec(v___x_2599_);
v___x_2601_ = lean_int_mul(v_second_2595_, v___x_2598_);
lean_dec(v_second_2595_);
v_nanos_2602_ = lean_int_add(v___x_2601_, v_nano_2596_);
lean_dec(v_nano_2596_);
lean_dec(v___x_2601_);
v___x_2603_ = lean_int_add(v_nanos_2600_, v_nanos_2602_);
lean_dec(v_nanos_2602_);
lean_dec(v_nanos_2600_);
v___x_2604_ = l_Std_Time_Duration_ofNanoseconds(v___x_2603_);
lean_dec(v___x_2603_);
v___x_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2604_);
v___x_2606_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2606_, 0, v_machine_2567_);
lean_ctor_set(v___x_2606_, 1, v_requestStream_2568_);
lean_ctor_set(v___x_2606_, 2, v___x_2597_);
lean_ctor_set(v___x_2606_, 3, v_currentTimeout_2569_);
lean_ctor_set(v___x_2606_, 4, v___x_2605_);
lean_ctor_set(v___x_2606_, 5, v_response_2570_);
lean_ctor_set(v___x_2606_, 6, v_respStream_2571_);
lean_ctor_set(v___x_2606_, 7, v_expectData_2573_);
lean_ctor_set(v___x_2606_, 8, v_pendingHead_2575_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*9, v_requiresData_2572_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*9 + 1, v_handlerDispatched_2574_);
v___x_2607_ = lean_box(0);
v___x_2608_ = lean_apply_3(v___f_2576_, v___x_2607_, v___x_2606_, lean_box(0));
return v___x_2608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_2609_, lean_object* v_machine_2610_, lean_object* v_requestStream_2611_, lean_object* v_currentTimeout_2612_, lean_object* v_response_2613_, lean_object* v_respStream_2614_, lean_object* v_requiresData_2615_, lean_object* v_expectData_2616_, lean_object* v_handlerDispatched_2617_, lean_object* v_pendingHead_2618_, lean_object* v___f_2619_, lean_object* v_x_2620_, lean_object* v___y_2621_){
_start:
{
uint8_t v_requiresData_boxed_2622_; uint8_t v_handlerDispatched_boxed_2623_; lean_object* v_res_2624_; 
v_requiresData_boxed_2622_ = lean_unbox(v_requiresData_2615_);
v_handlerDispatched_boxed_2623_ = lean_unbox(v_handlerDispatched_2617_);
v_res_2624_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_2609_, v_machine_2610_, v_requestStream_2611_, v_currentTimeout_2612_, v_response_2613_, v_respStream_2614_, v_requiresData_boxed_2622_, v_expectData_2616_, v_handlerDispatched_boxed_2623_, v_pendingHead_2618_, v___f_2619_, v_x_2620_);
lean_dec_ref(v_config_2609_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_2625_, lean_object* v_requestStream_2626_, lean_object* v_keepAliveTimeout_2627_, lean_object* v_currentTimeout_2628_, lean_object* v_headerTimeout_2629_, lean_object* v_response_2630_, uint8_t v_requiresData_2631_, lean_object* v_expectData_2632_, uint8_t v_handlerDispatched_2633_, lean_object* v_pendingHead_2634_, lean_object* v_____r_2635_){
_start:
{
lean_object* v_writer_2637_; lean_object* v_reader_2638_; lean_object* v_config_2639_; lean_object* v_events_2640_; lean_object* v_error_2641_; lean_object* v_instant_2642_; uint8_t v_keepAlive_2643_; uint8_t v_forcedFlush_2644_; uint8_t v_pullBodyStalled_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2675_; 
v_writer_2637_ = lean_ctor_get(v_machine_2625_, 1);
v_reader_2638_ = lean_ctor_get(v_machine_2625_, 0);
v_config_2639_ = lean_ctor_get(v_machine_2625_, 2);
v_events_2640_ = lean_ctor_get(v_machine_2625_, 3);
v_error_2641_ = lean_ctor_get(v_machine_2625_, 4);
v_instant_2642_ = lean_ctor_get(v_machine_2625_, 5);
v_keepAlive_2643_ = lean_ctor_get_uint8(v_machine_2625_, sizeof(void*)*6);
v_forcedFlush_2644_ = lean_ctor_get_uint8(v_machine_2625_, sizeof(void*)*6 + 1);
v_pullBodyStalled_2645_ = lean_ctor_get_uint8(v_machine_2625_, sizeof(void*)*6 + 2);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_machine_2625_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2647_ = v_machine_2625_;
v_isShared_2648_ = v_isSharedCheck_2675_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_instant_2642_);
lean_inc(v_error_2641_);
lean_inc(v_events_2640_);
lean_inc(v_config_2639_);
lean_inc(v_writer_2637_);
lean_inc(v_reader_2638_);
lean_dec(v_machine_2625_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2675_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v_userData_2649_; lean_object* v_outputData_2650_; lean_object* v_state_2651_; lean_object* v_knownSize_2652_; lean_object* v_messageHead_2653_; uint8_t v_sentMessage_2654_; uint8_t v_omitBody_2655_; lean_object* v_userDataBytes_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2674_; 
v_userData_2649_ = lean_ctor_get(v_writer_2637_, 0);
v_outputData_2650_ = lean_ctor_get(v_writer_2637_, 1);
v_state_2651_ = lean_ctor_get(v_writer_2637_, 2);
v_knownSize_2652_ = lean_ctor_get(v_writer_2637_, 3);
v_messageHead_2653_ = lean_ctor_get(v_writer_2637_, 4);
v_sentMessage_2654_ = lean_ctor_get_uint8(v_writer_2637_, sizeof(void*)*6);
v_omitBody_2655_ = lean_ctor_get_uint8(v_writer_2637_, sizeof(void*)*6 + 2);
v_userDataBytes_2656_ = lean_ctor_get(v_writer_2637_, 5);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_writer_2637_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2658_ = v_writer_2637_;
v_isShared_2659_ = v_isSharedCheck_2674_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_userDataBytes_2656_);
lean_inc(v_messageHead_2653_);
lean_inc(v_knownSize_2652_);
lean_inc(v_state_2651_);
lean_inc(v_outputData_2650_);
lean_inc(v_userData_2649_);
lean_dec(v_writer_2637_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2674_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
uint8_t v___x_2660_; lean_object* v___x_2662_; 
v___x_2660_ = 1;
if (v_isShared_2659_ == 0)
{
v___x_2662_ = v___x_2658_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_userData_2649_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_outputData_2650_);
lean_ctor_set(v_reuseFailAlloc_2673_, 2, v_state_2651_);
lean_ctor_set(v_reuseFailAlloc_2673_, 3, v_knownSize_2652_);
lean_ctor_set(v_reuseFailAlloc_2673_, 4, v_messageHead_2653_);
lean_ctor_set(v_reuseFailAlloc_2673_, 5, v_userDataBytes_2656_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, sizeof(void*)*6, v_sentMessage_2654_);
lean_ctor_set_uint8(v_reuseFailAlloc_2673_, sizeof(void*)*6 + 2, v_omitBody_2655_);
v___x_2662_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
lean_object* v___x_2664_; 
lean_ctor_set_uint8(v___x_2662_, sizeof(void*)*6 + 1, v___x_2660_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___x_2662_);
v___x_2664_ = v___x_2647_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_reader_2638_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2672_, 2, v_config_2639_);
lean_ctor_set(v_reuseFailAlloc_2672_, 3, v_events_2640_);
lean_ctor_set(v_reuseFailAlloc_2672_, 4, v_error_2641_);
lean_ctor_set(v_reuseFailAlloc_2672_, 5, v_instant_2642_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, sizeof(void*)*6, v_keepAlive_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, sizeof(void*)*6 + 1, v_forcedFlush_2644_);
lean_ctor_set_uint8(v_reuseFailAlloc_2672_, sizeof(void*)*6 + 2, v_pullBodyStalled_2645_);
v___x_2664_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2665_ = lean_box(0);
v___x_2666_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v_requestStream_2626_);
lean_ctor_set(v___x_2666_, 2, v_keepAliveTimeout_2627_);
lean_ctor_set(v___x_2666_, 3, v_currentTimeout_2628_);
lean_ctor_set(v___x_2666_, 4, v_headerTimeout_2629_);
lean_ctor_set(v___x_2666_, 5, v_response_2630_);
lean_ctor_set(v___x_2666_, 6, v___x_2665_);
lean_ctor_set(v___x_2666_, 7, v_expectData_2632_);
lean_ctor_set(v___x_2666_, 8, v_pendingHead_2634_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*9, v_requiresData_2631_);
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*9 + 1, v_handlerDispatched_2633_);
v___x_2667_ = 0;
v___x_2668_ = lean_box(v___x_2667_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2666_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
return v___x_2671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_2676_, lean_object* v_requestStream_2677_, lean_object* v_keepAliveTimeout_2678_, lean_object* v_currentTimeout_2679_, lean_object* v_headerTimeout_2680_, lean_object* v_response_2681_, lean_object* v_requiresData_2682_, lean_object* v_expectData_2683_, lean_object* v_handlerDispatched_2684_, lean_object* v_pendingHead_2685_, lean_object* v_____r_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v_requiresData_boxed_2688_; uint8_t v_handlerDispatched_boxed_2689_; lean_object* v_res_2690_; 
v_requiresData_boxed_2688_ = lean_unbox(v_requiresData_2682_);
v_handlerDispatched_boxed_2689_ = lean_unbox(v_handlerDispatched_2684_);
v_res_2690_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_2676_, v_requestStream_2677_, v_keepAliveTimeout_2678_, v_currentTimeout_2679_, v_headerTimeout_2680_, v_response_2681_, v_requiresData_boxed_2688_, v_expectData_2683_, v_handlerDispatched_boxed_2689_, v_pendingHead_2685_, v_____r_2686_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_2691_, lean_object* v_x_2692_){
_start:
{
if (lean_obj_tag(v_x_2692_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2702_; 
lean_dec_ref(v___f_2691_);
v_a_2694_ = lean_ctor_get(v_x_2692_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_x_2692_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2696_ = v_x_2692_;
v_isShared_2697_ = v_isSharedCheck_2702_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v_x_2692_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2702_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2704_; 
v_a_2703_ = lean_ctor_get(v_x_2692_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v_x_2692_, 1);
v___x_2704_ = lean_apply_2(v___f_2691_, v_a_2703_, lean_box(0));
return v___x_2704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_2705_, lean_object* v_x_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_2705_, v_x_2706_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_2709_, lean_object* v_val_2710_, lean_object* v___f_2711_, lean_object* v___f_2712_, lean_object* v_x_2713_){
_start:
{
if (lean_obj_tag(v_x_2713_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2723_; 
lean_dec_ref(v___f_2712_);
lean_dec_ref(v___f_2711_);
lean_dec(v_val_2710_);
lean_dec_ref(v_close_2709_);
v_a_2715_ = lean_ctor_get(v_x_2713_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_x_2713_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2717_ = v_x_2713_;
v_isShared_2718_ = v_isSharedCheck_2723_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v_x_2713_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2723_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2721_; 
v___x_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
return v___x_2721_;
}
}
}
else
{
lean_object* v_a_2724_; uint8_t v___x_2725_; 
v_a_2724_ = lean_ctor_get(v_x_2713_, 0);
lean_inc(v_a_2724_);
lean_dec_ref_known(v_x_2713_, 1);
v___x_2725_ = lean_unbox(v_a_2724_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; lean_object* v___x_2729_; 
lean_dec_ref(v___f_2712_);
v___x_2726_ = lean_unsigned_to_nat(0u);
v___x_2727_ = lean_apply_2(v_close_2709_, v_val_2710_, lean_box(0));
v___x_2728_ = lean_unbox(v_a_2724_);
lean_dec(v_a_2724_);
v___x_2729_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2726_, v___x_2728_, v___x_2727_, v___f_2711_);
return v___x_2729_;
}
else
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
lean_dec(v_a_2724_);
lean_dec_ref(v___f_2711_);
lean_dec(v_val_2710_);
lean_dec_ref(v_close_2709_);
v___x_2730_ = lean_box(0);
v___x_2731_ = lean_apply_2(v___f_2712_, v___x_2730_, lean_box(0));
return v___x_2731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_2732_, lean_object* v_val_2733_, lean_object* v___f_2734_, lean_object* v___f_2735_, lean_object* v_x_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_2732_, v_val_2733_, v___f_2734_, v___f_2735_, v_x_2736_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_inst_2739_, lean_object* v_handler_2740_, lean_object* v_x_2741_){
_start:
{
if (lean_obj_tag(v_x_2741_) == 0)
{
lean_object* v_a_2743_; lean_object* v_onFailure_2744_; lean_object* v___x_2745_; 
v_a_2743_ = lean_ctor_get(v_x_2741_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v_x_2741_, 1);
v_onFailure_2744_ = lean_ctor_get(v_inst_2739_, 2);
lean_inc_ref(v_onFailure_2744_);
lean_dec_ref(v_inst_2739_);
v___x_2745_ = lean_apply_3(v_onFailure_2744_, v_handler_2740_, v_a_2743_, lean_box(0));
return v___x_2745_;
}
else
{
lean_object* v___x_2746_; 
lean_dec(v_handler_2740_);
lean_dec_ref(v_inst_2739_);
v___x_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2746_, 0, v_x_2741_);
return v___x_2746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_inst_2747_, lean_object* v_handler_2748_, lean_object* v_x_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_inst_2747_, v_handler_2748_, v_x_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object* v_st_2752_, lean_object* v_____r_2753_){
_start:
{
uint8_t v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2755_ = 0;
v___x_2756_ = lean_box(v___x_2755_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v_st_2752_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
v___x_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_st_2760_, lean_object* v_____r_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_2760_, v_____r_2761_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_requestStream_2764_, lean_object* v___f_2765_, lean_object* v___f_2766_, lean_object* v_x_2767_){
_start:
{
if (lean_obj_tag(v_x_2767_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2777_; 
lean_dec_ref(v___f_2766_);
lean_dec_ref(v___f_2765_);
lean_dec_ref(v_requestStream_2764_);
v_a_2769_ = lean_ctor_get(v_x_2767_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_x_2767_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2771_ = v_x_2767_;
v_isShared_2772_ = v_isSharedCheck_2777_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v_x_2767_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2777_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; 
v___x_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
return v___x_2775_;
}
}
}
else
{
lean_object* v_a_2778_; uint8_t v___x_2779_; 
v_a_2778_ = lean_ctor_get(v_x_2767_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v_x_2767_, 1);
v___x_2779_ = lean_unbox(v_a_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; 
lean_dec_ref(v___f_2766_);
v___x_2780_ = lean_unsigned_to_nat(0u);
v___x_2781_ = l_Std_Http_Body_Stream_close(v_requestStream_2764_);
v___x_2782_ = lean_unbox(v_a_2778_);
lean_dec(v_a_2778_);
v___x_2783_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2780_, v___x_2782_, v___x_2781_, v___f_2765_);
return v___x_2783_;
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_dec(v_a_2778_);
lean_dec_ref(v___f_2765_);
lean_dec_ref(v_requestStream_2764_);
v___x_2784_ = lean_box(0);
v___x_2785_ = lean_apply_2(v___f_2766_, v___x_2784_, lean_box(0));
return v___x_2785_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_requestStream_2786_, lean_object* v___f_2787_, lean_object* v___f_2788_, lean_object* v_x_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_requestStream_2786_, v___f_2787_, v___f_2788_, v_x_2789_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(uint8_t v_final_2792_, lean_object* v___f_2793_, lean_object* v___f_2794_, lean_object* v_requestStream_2795_, lean_object* v___f_2796_, lean_object* v_x_2797_){
_start:
{
if (lean_obj_tag(v_x_2797_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2807_; 
lean_dec_ref(v___f_2796_);
lean_dec_ref(v_requestStream_2795_);
lean_dec_ref(v___f_2794_);
lean_dec_ref(v___f_2793_);
v_a_2799_ = lean_ctor_get(v_x_2797_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_x_2797_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2801_ = v_x_2797_;
v_isShared_2802_ = v_isSharedCheck_2807_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v_x_2797_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2807_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
return v___x_2805_;
}
}
}
else
{
lean_dec_ref_known(v_x_2797_, 1);
if (v_final_2792_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
lean_dec_ref(v___f_2796_);
lean_dec_ref(v_requestStream_2795_);
lean_dec_ref(v___f_2794_);
v___x_2808_ = lean_box(0);
v___x_2809_ = lean_apply_2(v___f_2793_, v___x_2808_, lean_box(0));
return v___x_2809_;
}
else
{
lean_object* v___x_2810_; uint8_t v___x_2811_; lean_object* v___x_2812_; lean_object* v___f_2813_; lean_object* v___f_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_6684__overap_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_dec_ref(v___f_2793_);
v___x_2810_ = lean_unsigned_to_nat(0u);
v___x_2811_ = 0;
v___x_2812_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_2813_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_2814_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_2815_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_2816_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_2816_, 0, lean_box(0));
lean_closure_set(v___x_2816_, 1, lean_box(0));
lean_closure_set(v___x_2816_, 2, v___x_2812_);
lean_closure_set(v___x_2816_, 3, lean_box(0));
lean_closure_set(v___x_2816_, 4, lean_box(0));
lean_closure_set(v___x_2816_, 5, v___x_2815_);
lean_closure_set(v___x_2816_, 6, v___f_2794_);
v___x_6684__overap_2817_ = l_Std_Mutex_atomically___redArg(v___x_2812_, v___f_2813_, v___f_2814_, v_requestStream_2795_, v___x_2816_);
v___x_2818_ = lean_apply_1(v___x_6684__overap_2817_, lean_box(0));
v___x_2819_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2810_, v___x_2811_, v___x_2818_, v___f_2796_);
return v___x_2819_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_final_2820_, lean_object* v___f_2821_, lean_object* v___f_2822_, lean_object* v_requestStream_2823_, lean_object* v___f_2824_, lean_object* v_x_2825_, lean_object* v___y_2826_){
_start:
{
uint8_t v_final_boxed_2827_; lean_object* v_res_2828_; 
v_final_boxed_2827_ = lean_unbox(v_final_2820_);
v_res_2828_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_final_boxed_2827_, v___f_2821_, v___f_2822_, v_requestStream_2823_, v___f_2824_, v_x_2825_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_state_2829_, lean_object* v_x_2830_){
_start:
{
if (lean_obj_tag(v_x_2830_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2840_; 
lean_dec_ref(v_state_2829_);
v_a_2832_ = lean_ctor_get(v_x_2830_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_x_2830_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2834_ = v_x_2830_;
v_isShared_2835_ = v_isSharedCheck_2840_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v_x_2830_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2840_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2838_; 
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
return v___x_2838_;
}
}
}
else
{
lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2870_; 
v_isSharedCheck_2870_ = !lean_is_exclusive(v_x_2830_);
if (v_isSharedCheck_2870_ == 0)
{
lean_object* v_unused_2871_; 
v_unused_2871_ = lean_ctor_get(v_x_2830_, 0);
lean_dec(v_unused_2871_);
v___x_2842_ = v_x_2830_;
v_isShared_2843_ = v_isSharedCheck_2870_;
goto v_resetjp_2841_;
}
else
{
lean_dec(v_x_2830_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2870_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v_machine_2844_; lean_object* v_requestStream_2845_; lean_object* v_keepAliveTimeout_2846_; lean_object* v_currentTimeout_2847_; lean_object* v_headerTimeout_2848_; lean_object* v_response_2849_; lean_object* v_respStream_2850_; uint8_t v_requiresData_2851_; lean_object* v_expectData_2852_; lean_object* v_pendingHead_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2869_; 
v_machine_2844_ = lean_ctor_get(v_state_2829_, 0);
v_requestStream_2845_ = lean_ctor_get(v_state_2829_, 1);
v_keepAliveTimeout_2846_ = lean_ctor_get(v_state_2829_, 2);
v_currentTimeout_2847_ = lean_ctor_get(v_state_2829_, 3);
v_headerTimeout_2848_ = lean_ctor_get(v_state_2829_, 4);
v_response_2849_ = lean_ctor_get(v_state_2829_, 5);
v_respStream_2850_ = lean_ctor_get(v_state_2829_, 6);
v_requiresData_2851_ = lean_ctor_get_uint8(v_state_2829_, sizeof(void*)*9);
v_expectData_2852_ = lean_ctor_get(v_state_2829_, 7);
v_pendingHead_2853_ = lean_ctor_get(v_state_2829_, 8);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_state_2829_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2855_ = v_state_2829_;
v_isShared_2856_ = v_isSharedCheck_2869_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_pendingHead_2853_);
lean_inc(v_expectData_2852_);
lean_inc(v_respStream_2850_);
lean_inc(v_response_2849_);
lean_inc(v_headerTimeout_2848_);
lean_inc(v_currentTimeout_2847_);
lean_inc(v_keepAliveTimeout_2846_);
lean_inc(v_requestStream_2845_);
lean_inc(v_machine_2844_);
lean_dec(v_state_2829_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2869_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; lean_object* v___x_2861_; 
v___x_2857_ = lean_box(52);
v___x_2858_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_2844_, v___x_2857_);
v___x_2859_ = 0;
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2858_);
v___x_2861_ = v___x_2855_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_requestStream_2845_);
lean_ctor_set(v_reuseFailAlloc_2868_, 2, v_keepAliveTimeout_2846_);
lean_ctor_set(v_reuseFailAlloc_2868_, 3, v_currentTimeout_2847_);
lean_ctor_set(v_reuseFailAlloc_2868_, 4, v_headerTimeout_2848_);
lean_ctor_set(v_reuseFailAlloc_2868_, 5, v_response_2849_);
lean_ctor_set(v_reuseFailAlloc_2868_, 6, v_respStream_2850_);
lean_ctor_set(v_reuseFailAlloc_2868_, 7, v_expectData_2852_);
lean_ctor_set(v_reuseFailAlloc_2868_, 8, v_pendingHead_2853_);
lean_ctor_set_uint8(v_reuseFailAlloc_2868_, sizeof(void*)*9, v_requiresData_2851_);
v___x_2861_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*9 + 1, v___x_2859_);
v___x_2862_ = lean_box(v___x_2859_);
v___x_2863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2861_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2863_);
v___x_2865_ = v___x_2842_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; 
v___x_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
return v___x_2866_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_state_2872_, lean_object* v_x_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_state_2872_, v_x_2873_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_machine_2876_, lean_object* v_requestStream_2877_, lean_object* v_keepAliveTimeout_2878_, lean_object* v_currentTimeout_2879_, lean_object* v_headerTimeout_2880_, lean_object* v_response_2881_, lean_object* v_respStream_2882_, uint8_t v_requiresData_2883_, lean_object* v_expectData_2884_, lean_object* v_pendingHead_2885_, lean_object* v_____r_2886_){
_start:
{
uint8_t v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2888_ = 0;
v___x_2889_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2889_, 0, v_machine_2876_);
lean_ctor_set(v___x_2889_, 1, v_requestStream_2877_);
lean_ctor_set(v___x_2889_, 2, v_keepAliveTimeout_2878_);
lean_ctor_set(v___x_2889_, 3, v_currentTimeout_2879_);
lean_ctor_set(v___x_2889_, 4, v_headerTimeout_2880_);
lean_ctor_set(v___x_2889_, 5, v_response_2881_);
lean_ctor_set(v___x_2889_, 6, v_respStream_2882_);
lean_ctor_set(v___x_2889_, 7, v_expectData_2884_);
lean_ctor_set(v___x_2889_, 8, v_pendingHead_2885_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*9, v_requiresData_2883_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*9 + 1, v___x_2888_);
v___x_2890_ = lean_box(v___x_2888_);
v___x_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
v___x_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_machine_2894_, lean_object* v_requestStream_2895_, lean_object* v_keepAliveTimeout_2896_, lean_object* v_currentTimeout_2897_, lean_object* v_headerTimeout_2898_, lean_object* v_response_2899_, lean_object* v_respStream_2900_, lean_object* v_requiresData_2901_, lean_object* v_expectData_2902_, lean_object* v_pendingHead_2903_, lean_object* v_____r_2904_, lean_object* v___y_2905_){
_start:
{
uint8_t v_requiresData_boxed_2906_; lean_object* v_res_2907_; 
v_requiresData_boxed_2906_ = lean_unbox(v_requiresData_2901_);
v_res_2907_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_machine_2894_, v_requestStream_2895_, v_keepAliveTimeout_2896_, v_currentTimeout_2897_, v_headerTimeout_2898_, v_response_2899_, v_respStream_2900_, v_requiresData_boxed_2906_, v_expectData_2902_, v_pendingHead_2903_, v_____r_2904_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_close_2908_, lean_object* v_body_2909_, lean_object* v___f_2910_, lean_object* v___f_2911_, lean_object* v_x_2912_){
_start:
{
if (lean_obj_tag(v_x_2912_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2922_; 
lean_dec_ref(v___f_2911_);
lean_dec_ref(v___f_2910_);
lean_dec(v_body_2909_);
lean_dec_ref(v_close_2908_);
v_a_2914_ = lean_ctor_get(v_x_2912_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_x_2912_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2916_ = v_x_2912_;
v_isShared_2917_ = v_isSharedCheck_2922_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v_x_2912_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2922_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
return v___x_2920_;
}
}
}
else
{
lean_object* v_a_2923_; uint8_t v___x_2924_; 
v_a_2923_ = lean_ctor_get(v_x_2912_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v_x_2912_, 1);
v___x_2924_ = lean_unbox(v_a_2923_);
if (v___x_2924_ == 0)
{
lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; lean_object* v___x_2928_; 
lean_dec_ref(v___f_2911_);
v___x_2925_ = lean_unsigned_to_nat(0u);
v___x_2926_ = lean_apply_2(v_close_2908_, v_body_2909_, lean_box(0));
v___x_2927_ = lean_unbox(v_a_2923_);
lean_dec(v_a_2923_);
v___x_2928_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2925_, v___x_2927_, v___x_2926_, v___f_2910_);
return v___x_2928_;
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec(v_a_2923_);
lean_dec_ref(v___f_2910_);
lean_dec(v_body_2909_);
lean_dec_ref(v_close_2908_);
v___x_2929_ = lean_box(0);
v___x_2930_ = lean_apply_2(v___f_2911_, v___x_2929_, lean_box(0));
return v___x_2930_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_close_2931_, lean_object* v_body_2932_, lean_object* v___f_2933_, lean_object* v___f_2934_, lean_object* v_x_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_close_2931_, v_body_2932_, v___f_2933_, v___f_2934_, v_x_2935_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_requestStream_2938_, lean_object* v_keepAliveTimeout_2939_, lean_object* v_currentTimeout_2940_, lean_object* v_headerTimeout_2941_, lean_object* v_response_2942_, uint8_t v_requiresData_2943_, lean_object* v_expectData_2944_, uint8_t v___x_2945_, lean_object* v_pendingHead_2946_, lean_object* v_____x_2947_){
_start:
{
lean_object* v_snd_2949_; lean_object* v_fst_2950_; lean_object* v_fst_2951_; lean_object* v_snd_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2962_; 
v_snd_2949_ = lean_ctor_get(v_____x_2947_, 1);
lean_inc(v_snd_2949_);
v_fst_2950_ = lean_ctor_get(v_____x_2947_, 0);
lean_inc(v_fst_2950_);
lean_dec_ref(v_____x_2947_);
v_fst_2951_ = lean_ctor_get(v_snd_2949_, 0);
v_snd_2952_ = lean_ctor_get(v_snd_2949_, 1);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_snd_2949_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2954_ = v_snd_2949_;
v_isShared_2955_ = v_isSharedCheck_2962_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_snd_2952_);
lean_inc(v_fst_2951_);
lean_dec(v_snd_2949_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2962_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2956_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2956_, 0, v_fst_2950_);
lean_ctor_set(v___x_2956_, 1, v_requestStream_2938_);
lean_ctor_set(v___x_2956_, 2, v_keepAliveTimeout_2939_);
lean_ctor_set(v___x_2956_, 3, v_currentTimeout_2940_);
lean_ctor_set(v___x_2956_, 4, v_headerTimeout_2941_);
lean_ctor_set(v___x_2956_, 5, v_response_2942_);
lean_ctor_set(v___x_2956_, 6, v_fst_2951_);
lean_ctor_set(v___x_2956_, 7, v_expectData_2944_);
lean_ctor_set(v___x_2956_, 8, v_pendingHead_2946_);
lean_ctor_set_uint8(v___x_2956_, sizeof(void*)*9, v_requiresData_2943_);
lean_ctor_set_uint8(v___x_2956_, sizeof(void*)*9 + 1, v___x_2945_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v___x_2956_);
v___x_2958_ = v___x_2954_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_snd_2952_);
v___x_2958_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
return v___x_2960_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_requestStream_2963_, lean_object* v_keepAliveTimeout_2964_, lean_object* v_currentTimeout_2965_, lean_object* v_headerTimeout_2966_, lean_object* v_response_2967_, lean_object* v_requiresData_2968_, lean_object* v_expectData_2969_, lean_object* v___x_2970_, lean_object* v_pendingHead_2971_, lean_object* v_____x_2972_, lean_object* v___y_2973_){
_start:
{
uint8_t v_requiresData_boxed_2974_; uint8_t v___x_7494__boxed_2975_; lean_object* v_res_2976_; 
v_requiresData_boxed_2974_ = lean_unbox(v_requiresData_2968_);
v___x_7494__boxed_2975_ = lean_unbox(v___x_2970_);
v_res_2976_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_requestStream_2963_, v_keepAliveTimeout_2964_, v_currentTimeout_2965_, v_headerTimeout_2966_, v_response_2967_, v_requiresData_boxed_2974_, v_expectData_2969_, v___x_7494__boxed_2975_, v_pendingHead_2971_, v_____x_2972_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v___f_2977_, lean_object* v_x_2978_){
_start:
{
if (lean_obj_tag(v_x_2978_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2988_; 
lean_dec_ref(v___f_2977_);
v_a_2980_ = lean_ctor_get(v_x_2978_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_x_2978_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2982_ = v_x_2978_;
v_isShared_2983_ = v_isSharedCheck_2988_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v_x_2978_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2988_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
return v___x_2986_;
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2990_; 
v_a_2989_ = lean_ctor_get(v_x_2978_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v_x_2978_, 1);
v___x_2990_ = lean_apply_2(v___f_2977_, v_a_2989_, lean_box(0));
return v___x_2990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___f_2991_, lean_object* v_x_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___f_2991_, v_x_2992_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___x_2995_, lean_object* v_x_2996_){
_start:
{
if (lean_obj_tag(v_x_2996_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3006_; 
v_a_2998_ = lean_ctor_get(v_x_2996_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_x_2996_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3000_ = v_x_2996_;
v_isShared_3001_ = v_isSharedCheck_3006_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v_x_2996_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3006_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
return v___x_3004_;
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3026_; 
v_a_3007_ = lean_ctor_get(v_x_2996_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_x_2996_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3009_ = v_x_2996_;
v_isShared_3010_ = v_isSharedCheck_3026_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v_x_2996_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3026_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v_fst_3011_; lean_object* v_snd_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3025_; 
v_fst_3011_ = lean_ctor_get(v_a_3007_, 0);
v_snd_3012_ = lean_ctor_get(v_a_3007_, 1);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_a_3007_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3014_ = v_a_3007_;
v_isShared_3015_ = v_isSharedCheck_3025_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_snd_3012_);
lean_inc(v_fst_3011_);
lean_dec(v_a_3007_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3025_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3016_ = lean_box(v___x_2995_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 1, v___x_3016_);
lean_ctor_set(v___x_3014_, 0, v_snd_3012_);
v___x_3018_ = v___x_3014_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_snd_3012_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v_fst_3011_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v___x_3019_);
v___x_3021_ = v___x_3009_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
return v___x_3022_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___x_3027_, lean_object* v_x_3028_, lean_object* v___y_3029_){
_start:
{
uint8_t v___x_7562__boxed_3030_; lean_object* v_res_3031_; 
v___x_7562__boxed_3030_ = lean_unbox(v___x_3027_);
v_res_3031_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___x_7562__boxed_3030_, v_x_3028_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_snd_3032_, uint8_t v___x_3033_, lean_object* v_fst_3034_, lean_object* v_x_3035_){
_start:
{
if (lean_obj_tag(v_x_3035_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v_fst_3034_);
lean_dec(v_snd_3032_);
v_a_3037_ = lean_ctor_get(v_x_3035_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v_x_3035_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3039_ = v_x_3035_;
v_isShared_3040_ = v_isSharedCheck_3045_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v_x_3035_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3045_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
return v___x_3043_;
}
}
}
else
{
lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3056_; 
v_isSharedCheck_3056_ = !lean_is_exclusive(v_x_3035_);
if (v_isSharedCheck_3056_ == 0)
{
lean_object* v_unused_3057_; 
v_unused_3057_ = lean_ctor_get(v_x_3035_, 0);
lean_dec(v_unused_3057_);
v___x_3047_ = v_x_3035_;
v_isShared_3048_ = v_isSharedCheck_3056_;
goto v_resetjp_3046_;
}
else
{
lean_dec(v_x_3035_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3056_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3049_ = lean_box(v___x_3033_);
v___x_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3050_, 0, v_snd_3032_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v_fst_3034_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 0, v___x_3051_);
v___x_3053_ = v___x_3047_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
return v___x_3054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_snd_3058_, lean_object* v___x_3059_, lean_object* v_fst_3060_, lean_object* v_x_3061_, lean_object* v___y_3062_){
_start:
{
uint8_t v___x_7630__boxed_3063_; lean_object* v_res_3064_; 
v___x_7630__boxed_3063_ = lean_unbox(v___x_3059_);
v_res_3064_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_snd_3058_, v___x_7630__boxed_3063_, v_fst_3060_, v_x_3061_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object* v_inst_3065_, lean_object* v_handler_3066_, uint8_t v___x_3067_, lean_object* v___f_3068_, lean_object* v_x_3069_){
_start:
{
if (lean_obj_tag(v_x_3069_) == 0)
{
lean_object* v_a_3071_; lean_object* v_onFailure_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v_a_3071_ = lean_ctor_get(v_x_3069_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v_x_3069_, 1);
v_onFailure_3072_ = lean_ctor_get(v_inst_3065_, 2);
lean_inc_ref(v_onFailure_3072_);
lean_dec_ref(v_inst_3065_);
v___x_3073_ = lean_unsigned_to_nat(0u);
v___x_3074_ = lean_apply_3(v_onFailure_3072_, v_handler_3066_, v_a_3071_, lean_box(0));
v___x_3075_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3073_, v___x_3067_, v___x_3074_, v___f_3068_);
return v___x_3075_;
}
else
{
lean_object* v___x_3076_; 
lean_dec_ref(v___f_3068_);
lean_dec(v_handler_3066_);
lean_dec_ref(v_inst_3065_);
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_x_3069_);
return v___x_3076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v_inst_3077_, lean_object* v_handler_3078_, lean_object* v___x_3079_, lean_object* v___f_3080_, lean_object* v_x_3081_, lean_object* v___y_3082_){
_start:
{
uint8_t v___x_7688__boxed_3083_; lean_object* v_res_3084_; 
v___x_7688__boxed_3083_ = lean_unbox(v___x_3079_);
v_res_3084_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3077_, v_handler_3078_, v___x_7688__boxed_3083_, v___f_3080_, v_x_3081_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint8_t v___x_3085_, lean_object* v___f_3086_, uint8_t v___x_3087_, lean_object* v_inst_3088_, lean_object* v_handler_3089_, lean_object* v_inst_3090_, lean_object* v___f_3091_, lean_object* v___f_3092_, lean_object* v_x_3093_){
_start:
{
if (lean_obj_tag(v_x_3093_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3103_; 
lean_dec_ref(v___f_3092_);
lean_dec_ref(v___f_3091_);
lean_dec_ref(v_inst_3090_);
lean_dec(v_handler_3089_);
lean_dec_ref(v_inst_3088_);
lean_dec_ref(v___f_3086_);
v_a_3095_ = lean_ctor_get(v_x_3093_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_x_3093_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3097_ = v_x_3093_;
v_isShared_3098_ = v_isSharedCheck_3103_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v_x_3093_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3103_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
lean_object* v___x_3101_; 
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
return v___x_3101_;
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3137_; 
v_a_3104_ = lean_ctor_get(v_x_3093_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_x_3093_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3106_ = v_x_3093_;
v_isShared_3107_ = v_isSharedCheck_3137_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v_x_3093_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3137_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v_snd_3108_; 
v_snd_3108_ = lean_ctor_get(v_a_3104_, 1);
lean_inc(v_snd_3108_);
if (lean_obj_tag(v_snd_3108_) == 0)
{
lean_object* v_fst_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v___f_3092_);
lean_dec_ref(v___f_3091_);
lean_dec_ref(v_inst_3090_);
lean_dec(v_handler_3089_);
lean_dec_ref(v_inst_3088_);
v_fst_3109_ = lean_ctor_get(v_a_3104_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_a_3104_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v_a_3104_, 1);
lean_dec(v_unused_3125_);
v___x_3111_ = v_a_3104_;
v_isShared_3112_ = v_isSharedCheck_3124_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_fst_3109_);
lean_dec(v_a_3104_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3124_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3113_ = lean_box(v___x_3085_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 1, v___x_3113_);
lean_ctor_set(v___x_3111_, 0, v_snd_3108_);
v___x_3115_ = v___x_3111_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_snd_3108_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v_fst_3109_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v___x_3117_ = lean_unsigned_to_nat(0u);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v___x_3116_);
v___x_3119_ = v___x_3106_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3116_);
v___x_3119_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
v___x_3121_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3117_, v___x_3085_, v___x_3120_, v___f_3086_);
return v___x_3121_;
}
}
}
}
else
{
lean_object* v_fst_3126_; lean_object* v_val_3127_; lean_object* v___x_3128_; lean_object* v___f_3129_; lean_object* v___x_3130_; lean_object* v___f_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_del_object(v___x_3106_);
lean_dec_ref(v___f_3086_);
v_fst_3126_ = lean_ctor_get(v_a_3104_, 0);
lean_inc_n(v_fst_3126_, 2);
lean_dec(v_a_3104_);
v_val_3127_ = lean_ctor_get(v_snd_3108_, 0);
lean_inc(v_val_3127_);
v___x_3128_ = lean_box(v___x_3087_);
v___f_3129_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_3129_, 0, v_snd_3108_);
lean_closure_set(v___f_3129_, 1, v___x_3128_);
lean_closure_set(v___f_3129_, 2, v_fst_3126_);
v___x_3130_ = lean_box(v___x_3085_);
v___f_3131_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 6, 4);
lean_closure_set(v___f_3131_, 0, v_inst_3088_);
lean_closure_set(v___f_3131_, 1, v_handler_3089_);
lean_closure_set(v___f_3131_, 2, v___x_3130_);
lean_closure_set(v___f_3131_, 3, v___f_3129_);
v___x_3132_ = lean_unsigned_to_nat(0u);
v___x_3133_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3090_, v_fst_3126_, v_val_3127_);
v___x_3134_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3132_, v___x_3085_, v___x_3133_, v___f_3091_);
v___x_3135_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3132_, v___x_3085_, v___x_3134_, v___f_3131_);
v___x_3136_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3132_, v___x_3085_, v___x_3135_, v___f_3092_);
return v___x_3136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v___x_3138_, lean_object* v___f_3139_, lean_object* v___x_3140_, lean_object* v_inst_3141_, lean_object* v_handler_3142_, lean_object* v_inst_3143_, lean_object* v___f_3144_, lean_object* v___f_3145_, lean_object* v_x_3146_, lean_object* v___y_3147_){
_start:
{
uint8_t v___x_7713__boxed_3148_; uint8_t v___x_7715__boxed_3149_; lean_object* v_res_3150_; 
v___x_7713__boxed_3148_ = lean_unbox(v___x_3138_);
v___x_7715__boxed_3149_ = lean_unbox(v___x_3140_);
v_res_3150_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_7713__boxed_3148_, v___f_3139_, v___x_7715__boxed_3149_, v_inst_3141_, v_handler_3142_, v_inst_3143_, v___f_3144_, v___f_3145_, v_x_3146_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object* v_state_3151_, lean_object* v_x_3152_){
_start:
{
if (lean_obj_tag(v_x_3152_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3162_; 
lean_dec_ref(v_state_3151_);
v_a_3154_ = lean_ctor_get(v_x_3152_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_x_3152_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3156_ = v_x_3152_;
v_isShared_3157_ = v_isSharedCheck_3162_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v_x_3152_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3162_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3160_; 
v___x_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
return v___x_3160_;
}
}
}
else
{
lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3192_; 
v_isSharedCheck_3192_ = !lean_is_exclusive(v_x_3152_);
if (v_isSharedCheck_3192_ == 0)
{
lean_object* v_unused_3193_; 
v_unused_3193_ = lean_ctor_get(v_x_3152_, 0);
lean_dec(v_unused_3193_);
v___x_3164_ = v_x_3152_;
v_isShared_3165_ = v_isSharedCheck_3192_;
goto v_resetjp_3163_;
}
else
{
lean_dec(v_x_3152_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3192_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v_machine_3166_; lean_object* v_requestStream_3167_; lean_object* v_keepAliveTimeout_3168_; lean_object* v_currentTimeout_3169_; lean_object* v_headerTimeout_3170_; lean_object* v_response_3171_; lean_object* v_respStream_3172_; uint8_t v_requiresData_3173_; lean_object* v_expectData_3174_; lean_object* v_pendingHead_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3191_; 
v_machine_3166_ = lean_ctor_get(v_state_3151_, 0);
v_requestStream_3167_ = lean_ctor_get(v_state_3151_, 1);
v_keepAliveTimeout_3168_ = lean_ctor_get(v_state_3151_, 2);
v_currentTimeout_3169_ = lean_ctor_get(v_state_3151_, 3);
v_headerTimeout_3170_ = lean_ctor_get(v_state_3151_, 4);
v_response_3171_ = lean_ctor_get(v_state_3151_, 5);
v_respStream_3172_ = lean_ctor_get(v_state_3151_, 6);
v_requiresData_3173_ = lean_ctor_get_uint8(v_state_3151_, sizeof(void*)*9);
v_expectData_3174_ = lean_ctor_get(v_state_3151_, 7);
v_pendingHead_3175_ = lean_ctor_get(v_state_3151_, 8);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_state_3151_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3177_ = v_state_3151_;
v_isShared_3178_ = v_isSharedCheck_3191_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_pendingHead_3175_);
lean_inc(v_expectData_3174_);
lean_inc(v_respStream_3172_);
lean_inc(v_response_3171_);
lean_inc(v_headerTimeout_3170_);
lean_inc(v_currentTimeout_3169_);
lean_inc(v_keepAliveTimeout_3168_);
lean_inc(v_requestStream_3167_);
lean_inc(v_machine_3166_);
lean_dec(v_state_3151_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3191_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; uint8_t v___x_3181_; lean_object* v___x_3183_; 
v___x_3179_ = lean_box(31);
v___x_3180_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3166_, v___x_3179_);
v___x_3181_ = 0;
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v___x_3180_);
v___x_3183_ = v___x_3177_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_requestStream_3167_);
lean_ctor_set(v_reuseFailAlloc_3190_, 2, v_keepAliveTimeout_3168_);
lean_ctor_set(v_reuseFailAlloc_3190_, 3, v_currentTimeout_3169_);
lean_ctor_set(v_reuseFailAlloc_3190_, 4, v_headerTimeout_3170_);
lean_ctor_set(v_reuseFailAlloc_3190_, 5, v_response_3171_);
lean_ctor_set(v_reuseFailAlloc_3190_, 6, v_respStream_3172_);
lean_ctor_set(v_reuseFailAlloc_3190_, 7, v_expectData_3174_);
lean_ctor_set(v_reuseFailAlloc_3190_, 8, v_pendingHead_3175_);
lean_ctor_set_uint8(v_reuseFailAlloc_3190_, sizeof(void*)*9, v_requiresData_3173_);
v___x_3183_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
lean_ctor_set_uint8(v___x_3183_, sizeof(void*)*9 + 1, v___x_3181_);
v___x_3184_ = lean_box(v___x_3181_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 0, v___x_3185_);
v___x_3187_ = v___x_3164_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3188_; 
v___x_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
return v___x_3188_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v_state_3194_, lean_object* v_x_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_state_3194_, v_x_3195_);
return v_res_3197_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
v___x_3203_ = lean_mk_io_user_error(v___x_3202_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3204_, lean_object* v_inst_3205_, lean_object* v_handler_3206_, lean_object* v_config_3207_, lean_object* v_event_3208_, lean_object* v_state_3209_){
_start:
{
switch(lean_obj_tag(v_event_3208_))
{
case 0:
{
lean_object* v_x_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3318_; 
lean_dec(v_handler_3206_);
lean_dec_ref(v_inst_3205_);
lean_dec_ref(v_inst_3204_);
v_x_3211_ = lean_ctor_get(v_event_3208_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_event_3208_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3213_ = v_event_3208_;
v_isShared_3214_ = v_isSharedCheck_3318_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_x_3211_);
lean_dec(v_event_3208_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3318_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
if (lean_obj_tag(v_x_3211_) == 0)
{
lean_object* v_machine_3215_; lean_object* v_reader_3216_; lean_object* v_requestStream_3217_; lean_object* v_keepAliveTimeout_3218_; lean_object* v_currentTimeout_3219_; lean_object* v_headerTimeout_3220_; lean_object* v_response_3221_; lean_object* v_respStream_3222_; uint8_t v_requiresData_3223_; lean_object* v_expectData_3224_; uint8_t v_handlerDispatched_3225_; lean_object* v_pendingHead_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3269_; 
lean_dec_ref(v_config_3207_);
v_machine_3215_ = lean_ctor_get(v_state_3209_, 0);
lean_inc_ref(v_machine_3215_);
v_reader_3216_ = lean_ctor_get(v_machine_3215_, 0);
lean_inc_ref(v_reader_3216_);
v_requestStream_3217_ = lean_ctor_get(v_state_3209_, 1);
v_keepAliveTimeout_3218_ = lean_ctor_get(v_state_3209_, 2);
v_currentTimeout_3219_ = lean_ctor_get(v_state_3209_, 3);
v_headerTimeout_3220_ = lean_ctor_get(v_state_3209_, 4);
v_response_3221_ = lean_ctor_get(v_state_3209_, 5);
v_respStream_3222_ = lean_ctor_get(v_state_3209_, 6);
v_requiresData_3223_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9);
v_expectData_3224_ = lean_ctor_get(v_state_3209_, 7);
v_handlerDispatched_3225_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9 + 1);
v_pendingHead_3226_ = lean_ctor_get(v_state_3209_, 8);
v_isSharedCheck_3269_ = !lean_is_exclusive(v_state_3209_);
if (v_isSharedCheck_3269_ == 0)
{
lean_object* v_unused_3270_; 
v_unused_3270_ = lean_ctor_get(v_state_3209_, 0);
lean_dec(v_unused_3270_);
v___x_3228_ = v_state_3209_;
v_isShared_3229_ = v_isSharedCheck_3269_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_pendingHead_3226_);
lean_inc(v_expectData_3224_);
lean_inc(v_respStream_3222_);
lean_inc(v_response_3221_);
lean_inc(v_headerTimeout_3220_);
lean_inc(v_currentTimeout_3219_);
lean_inc(v_keepAliveTimeout_3218_);
lean_inc(v_requestStream_3217_);
lean_dec(v_state_3209_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3269_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_writer_3230_; lean_object* v_config_3231_; lean_object* v_events_3232_; lean_object* v_error_3233_; lean_object* v_instant_3234_; uint8_t v_keepAlive_3235_; uint8_t v_forcedFlush_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3267_; 
v_writer_3230_ = lean_ctor_get(v_machine_3215_, 1);
v_config_3231_ = lean_ctor_get(v_machine_3215_, 2);
v_events_3232_ = lean_ctor_get(v_machine_3215_, 3);
v_error_3233_ = lean_ctor_get(v_machine_3215_, 4);
v_instant_3234_ = lean_ctor_get(v_machine_3215_, 5);
v_keepAlive_3235_ = lean_ctor_get_uint8(v_machine_3215_, sizeof(void*)*6);
v_forcedFlush_3236_ = lean_ctor_get_uint8(v_machine_3215_, sizeof(void*)*6 + 1);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_machine_3215_);
if (v_isSharedCheck_3267_ == 0)
{
lean_object* v_unused_3268_; 
v_unused_3268_ = lean_ctor_get(v_machine_3215_, 0);
lean_dec(v_unused_3268_);
v___x_3238_ = v_machine_3215_;
v_isShared_3239_ = v_isSharedCheck_3267_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_instant_3234_);
lean_inc(v_error_3233_);
lean_inc(v_events_3232_);
lean_inc(v_config_3231_);
lean_inc(v_writer_3230_);
lean_dec(v_machine_3215_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3267_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v_state_3240_; lean_object* v_input_3241_; lean_object* v_messageHead_3242_; lean_object* v_messageCount_3243_; lean_object* v_bodyBytesRead_3244_; lean_object* v_headerBytesRead_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3266_; 
v_state_3240_ = lean_ctor_get(v_reader_3216_, 0);
v_input_3241_ = lean_ctor_get(v_reader_3216_, 1);
v_messageHead_3242_ = lean_ctor_get(v_reader_3216_, 2);
v_messageCount_3243_ = lean_ctor_get(v_reader_3216_, 3);
v_bodyBytesRead_3244_ = lean_ctor_get(v_reader_3216_, 4);
v_headerBytesRead_3245_ = lean_ctor_get(v_reader_3216_, 5);
v_isSharedCheck_3266_ = !lean_is_exclusive(v_reader_3216_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3247_ = v_reader_3216_;
v_isShared_3248_ = v_isSharedCheck_3266_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_headerBytesRead_3245_);
lean_inc(v_bodyBytesRead_3244_);
lean_inc(v_messageCount_3243_);
lean_inc(v_messageHead_3242_);
lean_inc(v_input_3241_);
lean_inc(v_state_3240_);
lean_dec(v_reader_3216_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3266_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
uint8_t v___x_3249_; lean_object* v___x_3251_; 
v___x_3249_ = 1;
if (v_isShared_3248_ == 0)
{
v___x_3251_ = v___x_3247_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_state_3240_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_input_3241_);
lean_ctor_set(v_reuseFailAlloc_3265_, 2, v_messageHead_3242_);
lean_ctor_set(v_reuseFailAlloc_3265_, 3, v_messageCount_3243_);
lean_ctor_set(v_reuseFailAlloc_3265_, 4, v_bodyBytesRead_3244_);
lean_ctor_set(v_reuseFailAlloc_3265_, 5, v_headerBytesRead_3245_);
v___x_3251_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
uint8_t v___x_3252_; lean_object* v___x_3254_; 
lean_ctor_set_uint8(v___x_3251_, sizeof(void*)*6, v___x_3249_);
v___x_3252_ = 0;
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v___x_3251_);
v___x_3254_ = v___x_3238_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_writer_3230_);
lean_ctor_set(v_reuseFailAlloc_3264_, 2, v_config_3231_);
lean_ctor_set(v_reuseFailAlloc_3264_, 3, v_events_3232_);
lean_ctor_set(v_reuseFailAlloc_3264_, 4, v_error_3233_);
lean_ctor_set(v_reuseFailAlloc_3264_, 5, v_instant_3234_);
lean_ctor_set_uint8(v_reuseFailAlloc_3264_, sizeof(void*)*6, v_keepAlive_3235_);
lean_ctor_set_uint8(v_reuseFailAlloc_3264_, sizeof(void*)*6 + 1, v_forcedFlush_3236_);
v___x_3254_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3256_; 
lean_ctor_set_uint8(v___x_3254_, sizeof(void*)*6 + 2, v___x_3252_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3254_);
v___x_3256_ = v___x_3228_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3254_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_requestStream_3217_);
lean_ctor_set(v_reuseFailAlloc_3263_, 2, v_keepAliveTimeout_3218_);
lean_ctor_set(v_reuseFailAlloc_3263_, 3, v_currentTimeout_3219_);
lean_ctor_set(v_reuseFailAlloc_3263_, 4, v_headerTimeout_3220_);
lean_ctor_set(v_reuseFailAlloc_3263_, 5, v_response_3221_);
lean_ctor_set(v_reuseFailAlloc_3263_, 6, v_respStream_3222_);
lean_ctor_set(v_reuseFailAlloc_3263_, 7, v_expectData_3224_);
lean_ctor_set(v_reuseFailAlloc_3263_, 8, v_pendingHead_3226_);
lean_ctor_set_uint8(v_reuseFailAlloc_3263_, sizeof(void*)*9, v_requiresData_3223_);
lean_ctor_set_uint8(v_reuseFailAlloc_3263_, sizeof(void*)*9 + 1, v_handlerDispatched_3225_);
v___x_3256_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3257_ = lean_box(v___x_3252_);
v___x_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3256_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set_tag(v___x_3213_, 1);
lean_ctor_set(v___x_3213_, 0, v___x_3258_);
v___x_3260_ = v___x_3213_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3261_; 
v___x_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
return v___x_3261_;
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
lean_object* v_val_3271_; lean_object* v_machine_3272_; lean_object* v_requestStream_3273_; lean_object* v_keepAliveTimeout_3274_; lean_object* v_currentTimeout_3275_; lean_object* v_response_3276_; lean_object* v_respStream_3277_; uint8_t v_requiresData_3278_; lean_object* v_expectData_3279_; uint8_t v_handlerDispatched_3280_; lean_object* v_pendingHead_3281_; lean_object* v___f_3282_; 
lean_del_object(v___x_3213_);
v_val_3271_ = lean_ctor_get(v_x_3211_, 0);
lean_inc_n(v_val_3271_, 2);
lean_dec_ref_known(v_x_3211_, 1);
v_machine_3272_ = lean_ctor_get(v_state_3209_, 0);
v_requestStream_3273_ = lean_ctor_get(v_state_3209_, 1);
v_keepAliveTimeout_3274_ = lean_ctor_get(v_state_3209_, 2);
lean_inc(v_keepAliveTimeout_3274_);
v_currentTimeout_3275_ = lean_ctor_get(v_state_3209_, 3);
v_response_3276_ = lean_ctor_get(v_state_3209_, 5);
v_respStream_3277_ = lean_ctor_get(v_state_3209_, 6);
v_requiresData_3278_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9);
v_expectData_3279_ = lean_ctor_get(v_state_3209_, 7);
v_handlerDispatched_3280_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9 + 1);
v_pendingHead_3281_ = lean_ctor_get(v_state_3209_, 8);
v___f_3282_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3282_, 0, v_val_3271_);
if (lean_obj_tag(v_keepAliveTimeout_3274_) == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
lean_dec_ref(v___f_3282_);
lean_dec_ref(v_config_3207_);
v___x_3283_ = lean_box(0);
v___x_3284_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3271_, v___x_3283_, v_state_3209_);
return v___x_3284_;
}
else
{
lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3316_; 
lean_inc(v_pendingHead_3281_);
lean_inc(v_expectData_3279_);
lean_inc(v_respStream_3277_);
lean_inc_ref(v_response_3276_);
lean_inc(v_currentTimeout_3275_);
lean_inc_ref(v_requestStream_3273_);
lean_inc_ref(v_machine_3272_);
lean_dec(v_val_3271_);
lean_dec_ref(v_state_3209_);
v_isSharedCheck_3316_ = !lean_is_exclusive(v_keepAliveTimeout_3274_);
if (v_isSharedCheck_3316_ == 0)
{
lean_object* v_unused_3317_; 
v_unused_3317_ = lean_ctor_get(v_keepAliveTimeout_3274_, 0);
lean_dec(v_unused_3317_);
v___x_3286_ = v_keepAliveTimeout_3274_;
v_isShared_3287_ = v_isSharedCheck_3316_;
goto v_resetjp_3285_;
}
else
{
lean_dec(v_keepAliveTimeout_3274_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3316_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___f_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; lean_object* v_val_3294_; lean_object* v___x_3299_; 
v___x_3288_ = lean_box(v_requiresData_3278_);
v___x_3289_ = lean_box(v_handlerDispatched_3280_);
v___f_3290_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3290_, 0, v_config_3207_);
lean_closure_set(v___f_3290_, 1, v_machine_3272_);
lean_closure_set(v___f_3290_, 2, v_requestStream_3273_);
lean_closure_set(v___f_3290_, 3, v_currentTimeout_3275_);
lean_closure_set(v___f_3290_, 4, v_response_3276_);
lean_closure_set(v___f_3290_, 5, v_respStream_3277_);
lean_closure_set(v___f_3290_, 6, v___x_3288_);
lean_closure_set(v___f_3290_, 7, v_expectData_3279_);
lean_closure_set(v___f_3290_, 8, v___x_3289_);
lean_closure_set(v___f_3290_, 9, v_pendingHead_3281_);
lean_closure_set(v___f_3290_, 10, v___f_3282_);
v___x_3291_ = lean_unsigned_to_nat(0u);
v___x_3292_ = 0;
v___x_3299_ = lean_get_current_time();
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3299_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3299_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
lean_ctor_set_tag(v___x_3302_, 1);
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
v_val_3294_ = v___x_3305_;
goto v___jp_3293_;
}
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
v_a_3308_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3299_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3299_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
lean_ctor_set_tag(v___x_3310_, 0);
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
v_val_3294_ = v___x_3313_;
goto v___jp_3293_;
}
}
}
v___jp_3293_:
{
lean_object* v___x_3296_; 
if (v_isShared_3287_ == 0)
{
lean_ctor_set_tag(v___x_3286_, 0);
lean_ctor_set(v___x_3286_, 0, v_val_3294_);
v___x_3296_ = v___x_3286_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_val_3294_);
v___x_3296_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3297_; 
v___x_3297_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3291_, v___x_3292_, v___x_3296_, v___f_3290_);
return v___x_3297_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v_config_3207_);
lean_dec(v_handler_3206_);
lean_dec_ref(v_inst_3204_);
v_x_3319_ = lean_ctor_get(v_event_3208_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_event_3208_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3321_ = v_event_3208_;
v_isShared_3322_ = v_isSharedCheck_3430_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_x_3319_);
lean_dec(v_event_3208_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3430_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
if (lean_obj_tag(v_x_3319_) == 0)
{
lean_object* v_machine_3323_; lean_object* v_requestStream_3324_; lean_object* v_keepAliveTimeout_3325_; lean_object* v_currentTimeout_3326_; lean_object* v_headerTimeout_3327_; lean_object* v_response_3328_; lean_object* v_respStream_3329_; uint8_t v_requiresData_3330_; lean_object* v_expectData_3331_; uint8_t v_handlerDispatched_3332_; lean_object* v_pendingHead_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___f_3336_; 
lean_del_object(v___x_3321_);
v_machine_3323_ = lean_ctor_get(v_state_3209_, 0);
lean_inc_ref_n(v_machine_3323_, 2);
v_requestStream_3324_ = lean_ctor_get(v_state_3209_, 1);
lean_inc_ref_n(v_requestStream_3324_, 2);
v_keepAliveTimeout_3325_ = lean_ctor_get(v_state_3209_, 2);
lean_inc_n(v_keepAliveTimeout_3325_, 2);
v_currentTimeout_3326_ = lean_ctor_get(v_state_3209_, 3);
lean_inc_n(v_currentTimeout_3326_, 2);
v_headerTimeout_3327_ = lean_ctor_get(v_state_3209_, 4);
lean_inc_n(v_headerTimeout_3327_, 2);
v_response_3328_ = lean_ctor_get(v_state_3209_, 5);
lean_inc_ref_n(v_response_3328_, 2);
v_respStream_3329_ = lean_ctor_get(v_state_3209_, 6);
lean_inc(v_respStream_3329_);
v_requiresData_3330_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9);
v_expectData_3331_ = lean_ctor_get(v_state_3209_, 7);
lean_inc_n(v_expectData_3331_, 2);
v_handlerDispatched_3332_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9 + 1);
v_pendingHead_3333_ = lean_ctor_get(v_state_3209_, 8);
lean_inc_n(v_pendingHead_3333_, 2);
lean_dec_ref(v_state_3209_);
v___x_3334_ = lean_box(v_requiresData_3330_);
v___x_3335_ = lean_box(v_handlerDispatched_3332_);
v___f_3336_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_3336_, 0, v_machine_3323_);
lean_closure_set(v___f_3336_, 1, v_requestStream_3324_);
lean_closure_set(v___f_3336_, 2, v_keepAliveTimeout_3325_);
lean_closure_set(v___f_3336_, 3, v_currentTimeout_3326_);
lean_closure_set(v___f_3336_, 4, v_headerTimeout_3327_);
lean_closure_set(v___f_3336_, 5, v_response_3328_);
lean_closure_set(v___f_3336_, 6, v___x_3334_);
lean_closure_set(v___f_3336_, 7, v_expectData_3331_);
lean_closure_set(v___f_3336_, 8, v___x_3335_);
lean_closure_set(v___f_3336_, 9, v_pendingHead_3333_);
if (lean_obj_tag(v_respStream_3329_) == 1)
{
lean_object* v_val_3337_; lean_object* v_close_3338_; lean_object* v_isClosed_3339_; lean_object* v___f_3340_; lean_object* v___f_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
lean_dec(v_pendingHead_3333_);
lean_dec(v_expectData_3331_);
lean_dec_ref(v_response_3328_);
lean_dec(v_headerTimeout_3327_);
lean_dec(v_currentTimeout_3326_);
lean_dec(v_keepAliveTimeout_3325_);
lean_dec_ref(v_requestStream_3324_);
lean_dec_ref(v_machine_3323_);
v_val_3337_ = lean_ctor_get(v_respStream_3329_, 0);
lean_inc_n(v_val_3337_, 2);
lean_dec_ref_known(v_respStream_3329_, 1);
v_close_3338_ = lean_ctor_get(v_inst_3205_, 1);
lean_inc_ref(v_close_3338_);
v_isClosed_3339_ = lean_ctor_get(v_inst_3205_, 2);
lean_inc_ref(v_isClosed_3339_);
lean_dec_ref(v_inst_3205_);
lean_inc_ref(v___f_3336_);
v___f_3340_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3340_, 0, v___f_3336_);
v___f_3341_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_3341_, 0, v_close_3338_);
lean_closure_set(v___f_3341_, 1, v_val_3337_);
lean_closure_set(v___f_3341_, 2, v___f_3340_);
lean_closure_set(v___f_3341_, 3, v___f_3336_);
v___x_3342_ = lean_unsigned_to_nat(0u);
v___x_3343_ = 0;
v___x_3344_ = lean_apply_2(v_isClosed_3339_, v_val_3337_, lean_box(0));
v___x_3345_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3342_, v___x_3343_, v___x_3344_, v___f_3341_);
return v___x_3345_;
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_dec_ref(v___f_3336_);
lean_dec(v_respStream_3329_);
lean_dec_ref(v_inst_3205_);
v___x_3346_ = lean_box(0);
v___x_3347_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3323_, v_requestStream_3324_, v_keepAliveTimeout_3325_, v_currentTimeout_3326_, v_headerTimeout_3327_, v_response_3328_, v_requiresData_3330_, v_expectData_3331_, v_handlerDispatched_3332_, v_pendingHead_3333_, v___x_3346_);
return v___x_3347_;
}
}
else
{
lean_object* v_val_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3429_; 
lean_dec_ref(v_inst_3205_);
v_val_3348_ = lean_ctor_get(v_x_3319_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_x_3319_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3350_ = v_x_3319_;
v_isShared_3351_ = v_isSharedCheck_3429_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_val_3348_);
lean_dec(v_x_3319_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3429_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v_machine_3352_; lean_object* v_requestStream_3353_; lean_object* v_keepAliveTimeout_3354_; lean_object* v_currentTimeout_3355_; lean_object* v_headerTimeout_3356_; lean_object* v_response_3357_; lean_object* v_respStream_3358_; uint8_t v_requiresData_3359_; lean_object* v_expectData_3360_; uint8_t v_handlerDispatched_3361_; lean_object* v_pendingHead_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3428_; 
v_machine_3352_ = lean_ctor_get(v_state_3209_, 0);
v_requestStream_3353_ = lean_ctor_get(v_state_3209_, 1);
v_keepAliveTimeout_3354_ = lean_ctor_get(v_state_3209_, 2);
v_currentTimeout_3355_ = lean_ctor_get(v_state_3209_, 3);
v_headerTimeout_3356_ = lean_ctor_get(v_state_3209_, 4);
v_response_3357_ = lean_ctor_get(v_state_3209_, 5);
v_respStream_3358_ = lean_ctor_get(v_state_3209_, 6);
v_requiresData_3359_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9);
v_expectData_3360_ = lean_ctor_get(v_state_3209_, 7);
v_handlerDispatched_3361_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9 + 1);
v_pendingHead_3362_ = lean_ctor_get(v_state_3209_, 8);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_state_3209_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3364_ = v_state_3209_;
v_isShared_3365_ = v_isSharedCheck_3428_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_pendingHead_3362_);
lean_inc(v_expectData_3360_);
lean_inc(v_respStream_3358_);
lean_inc(v_response_3357_);
lean_inc(v_headerTimeout_3356_);
lean_inc(v_currentTimeout_3355_);
lean_inc(v_keepAliveTimeout_3354_);
lean_inc(v_requestStream_3353_);
lean_inc(v_machine_3352_);
lean_dec(v_state_3209_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3428_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___y_3367_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; 
v___x_3380_ = lean_unsigned_to_nat(1u);
v___x_3381_ = lean_mk_empty_array_with_capacity(v___x_3380_);
v___x_3382_ = lean_array_push(v___x_3381_, v_val_3348_);
v___x_3383_ = lean_array_get_size(v___x_3382_);
v___x_3384_ = lean_unsigned_to_nat(0u);
v___x_3385_ = lean_nat_dec_eq(v___x_3383_, v___x_3384_);
if (v___x_3385_ == 0)
{
lean_object* v_reader_3386_; lean_object* v_writer_3387_; lean_object* v_config_3388_; lean_object* v_events_3389_; lean_object* v_error_3390_; lean_object* v_instant_3391_; uint8_t v_keepAlive_3392_; uint8_t v_forcedFlush_3393_; uint8_t v_pullBodyStalled_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3427_; 
v_reader_3386_ = lean_ctor_get(v_machine_3352_, 0);
v_writer_3387_ = lean_ctor_get(v_machine_3352_, 1);
v_config_3388_ = lean_ctor_get(v_machine_3352_, 2);
v_events_3389_ = lean_ctor_get(v_machine_3352_, 3);
v_error_3390_ = lean_ctor_get(v_machine_3352_, 4);
v_instant_3391_ = lean_ctor_get(v_machine_3352_, 5);
v_keepAlive_3392_ = lean_ctor_get_uint8(v_machine_3352_, sizeof(void*)*6);
v_forcedFlush_3393_ = lean_ctor_get_uint8(v_machine_3352_, sizeof(void*)*6 + 1);
v_pullBodyStalled_3394_ = lean_ctor_get_uint8(v_machine_3352_, sizeof(void*)*6 + 2);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_machine_3352_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3396_ = v_machine_3352_;
v_isShared_3397_ = v_isSharedCheck_3427_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_instant_3391_);
lean_inc(v_error_3390_);
lean_inc(v_events_3389_);
lean_inc(v_config_3388_);
lean_inc(v_writer_3387_);
lean_inc(v_reader_3386_);
lean_dec(v_machine_3352_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3427_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___y_3399_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
v___x_3421_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_3422_ = lean_nat_dec_lt(v___x_3384_, v___x_3383_);
if (v___x_3422_ == 0)
{
v___y_3399_ = v___x_3384_;
goto v___jp_3398_;
}
else
{
lean_object* v___f_3423_; size_t v___x_3424_; size_t v___x_3425_; lean_object* v___x_3426_; 
v___f_3423_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_3424_ = ((size_t)0ULL);
v___x_3425_ = lean_usize_of_nat(v___x_3383_);
lean_inc_ref(v___x_3382_);
v___x_3426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3421_, v___f_3423_, v___x_3382_, v___x_3424_, v___x_3425_, v___x_3384_);
v___y_3399_ = v___x_3426_;
goto v___jp_3398_;
}
v___jp_3398_:
{
lean_object* v_userData_3400_; lean_object* v_outputData_3401_; lean_object* v_state_3402_; lean_object* v_knownSize_3403_; lean_object* v_messageHead_3404_; uint8_t v_sentMessage_3405_; uint8_t v_userClosedBody_3406_; uint8_t v_omitBody_3407_; lean_object* v_userDataBytes_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3420_; 
v_userData_3400_ = lean_ctor_get(v_writer_3387_, 0);
v_outputData_3401_ = lean_ctor_get(v_writer_3387_, 1);
v_state_3402_ = lean_ctor_get(v_writer_3387_, 2);
v_knownSize_3403_ = lean_ctor_get(v_writer_3387_, 3);
v_messageHead_3404_ = lean_ctor_get(v_writer_3387_, 4);
v_sentMessage_3405_ = lean_ctor_get_uint8(v_writer_3387_, sizeof(void*)*6);
v_userClosedBody_3406_ = lean_ctor_get_uint8(v_writer_3387_, sizeof(void*)*6 + 1);
v_omitBody_3407_ = lean_ctor_get_uint8(v_writer_3387_, sizeof(void*)*6 + 2);
v_userDataBytes_3408_ = lean_ctor_get(v_writer_3387_, 5);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_writer_3387_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3410_ = v_writer_3387_;
v_isShared_3411_ = v_isSharedCheck_3420_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_userDataBytes_3408_);
lean_inc(v_messageHead_3404_);
lean_inc(v_knownSize_3403_);
lean_inc(v_state_3402_);
lean_inc(v_outputData_3401_);
lean_inc(v_userData_3400_);
lean_dec(v_writer_3387_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3420_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3415_; 
v___x_3412_ = l_Array_append___redArg(v_userData_3400_, v___x_3382_);
lean_dec_ref(v___x_3382_);
v___x_3413_ = lean_nat_add(v_userDataBytes_3408_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec(v_userDataBytes_3408_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 5, v___x_3413_);
lean_ctor_set(v___x_3410_, 0, v___x_3412_);
v___x_3415_ = v___x_3410_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3412_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_outputData_3401_);
lean_ctor_set(v_reuseFailAlloc_3419_, 2, v_state_3402_);
lean_ctor_set(v_reuseFailAlloc_3419_, 3, v_knownSize_3403_);
lean_ctor_set(v_reuseFailAlloc_3419_, 4, v_messageHead_3404_);
lean_ctor_set(v_reuseFailAlloc_3419_, 5, v___x_3413_);
lean_ctor_set_uint8(v_reuseFailAlloc_3419_, sizeof(void*)*6, v_sentMessage_3405_);
lean_ctor_set_uint8(v_reuseFailAlloc_3419_, sizeof(void*)*6 + 1, v_userClosedBody_3406_);
lean_ctor_set_uint8(v_reuseFailAlloc_3419_, sizeof(void*)*6 + 2, v_omitBody_3407_);
v___x_3415_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3417_; 
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 1, v___x_3415_);
v___x_3417_ = v___x_3396_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_reader_3386_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3418_, 2, v_config_3388_);
lean_ctor_set(v_reuseFailAlloc_3418_, 3, v_events_3389_);
lean_ctor_set(v_reuseFailAlloc_3418_, 4, v_error_3390_);
lean_ctor_set(v_reuseFailAlloc_3418_, 5, v_instant_3391_);
lean_ctor_set_uint8(v_reuseFailAlloc_3418_, sizeof(void*)*6, v_keepAlive_3392_);
lean_ctor_set_uint8(v_reuseFailAlloc_3418_, sizeof(void*)*6 + 1, v_forcedFlush_3393_);
lean_ctor_set_uint8(v_reuseFailAlloc_3418_, sizeof(void*)*6 + 2, v_pullBodyStalled_3394_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
v___y_3367_ = v___x_3417_;
goto v___jp_3366_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3382_);
v___y_3367_ = v_machine_3352_;
goto v___jp_3366_;
}
v___jp_3366_:
{
lean_object* v___x_3369_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___y_3367_);
v___x_3369_ = v___x_3364_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___y_3367_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_requestStream_3353_);
lean_ctor_set(v_reuseFailAlloc_3379_, 2, v_keepAliveTimeout_3354_);
lean_ctor_set(v_reuseFailAlloc_3379_, 3, v_currentTimeout_3355_);
lean_ctor_set(v_reuseFailAlloc_3379_, 4, v_headerTimeout_3356_);
lean_ctor_set(v_reuseFailAlloc_3379_, 5, v_response_3357_);
lean_ctor_set(v_reuseFailAlloc_3379_, 6, v_respStream_3358_);
lean_ctor_set(v_reuseFailAlloc_3379_, 7, v_expectData_3360_);
lean_ctor_set(v_reuseFailAlloc_3379_, 8, v_pendingHead_3362_);
lean_ctor_set_uint8(v_reuseFailAlloc_3379_, sizeof(void*)*9, v_requiresData_3359_);
lean_ctor_set_uint8(v_reuseFailAlloc_3379_, sizeof(void*)*9 + 1, v_handlerDispatched_3361_);
v___x_3369_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
uint8_t v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3370_ = 0;
v___x_3371_ = lean_box(v___x_3370_);
v___x_3372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3369_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v___x_3372_);
v___x_3374_ = v___x_3350_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3372_);
v___x_3374_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3376_; 
if (v_isShared_3322_ == 0)
{
lean_ctor_set_tag(v___x_3321_, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3374_);
v___x_3376_ = v___x_3321_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
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
uint8_t v_x_3431_; 
lean_dec_ref(v_config_3207_);
lean_dec_ref(v_inst_3205_);
v_x_3431_ = lean_ctor_get_uint8(v_event_3208_, 0);
lean_dec_ref_known(v_event_3208_, 0);
if (v_x_3431_ == 0)
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
lean_dec(v_handler_3206_);
lean_dec_ref(v_inst_3204_);
v___x_3432_ = lean_box(v_x_3431_);
v___x_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3433_, 0, v_state_3209_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
v___x_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
return v___x_3435_;
}
else
{
lean_object* v_machine_3436_; lean_object* v_requestStream_3437_; lean_object* v_keepAliveTimeout_3438_; lean_object* v_currentTimeout_3439_; lean_object* v_headerTimeout_3440_; lean_object* v_response_3441_; lean_object* v_respStream_3442_; uint8_t v_requiresData_3443_; lean_object* v_expectData_3444_; uint8_t v_handlerDispatched_3445_; lean_object* v_pendingHead_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3496_; 
v_machine_3436_ = lean_ctor_get(v_state_3209_, 0);
v_requestStream_3437_ = lean_ctor_get(v_state_3209_, 1);
v_keepAliveTimeout_3438_ = lean_ctor_get(v_state_3209_, 2);
v_currentTimeout_3439_ = lean_ctor_get(v_state_3209_, 3);
v_headerTimeout_3440_ = lean_ctor_get(v_state_3209_, 4);
v_response_3441_ = lean_ctor_get(v_state_3209_, 5);
v_respStream_3442_ = lean_ctor_get(v_state_3209_, 6);
v_requiresData_3443_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9);
v_expectData_3444_ = lean_ctor_get(v_state_3209_, 7);
v_handlerDispatched_3445_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9 + 1);
v_pendingHead_3446_ = lean_ctor_get(v_state_3209_, 8);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_state_3209_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3448_ = v_state_3209_;
v_isShared_3449_ = v_isSharedCheck_3496_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_pendingHead_3446_);
lean_inc(v_expectData_3444_);
lean_inc(v_respStream_3442_);
lean_inc(v_response_3441_);
lean_inc(v_headerTimeout_3440_);
lean_inc(v_currentTimeout_3439_);
lean_inc(v_keepAliveTimeout_3438_);
lean_inc(v_requestStream_3437_);
lean_inc(v_machine_3436_);
lean_dec(v_state_3209_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3496_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
uint8_t v___x_3450_; lean_object* v___x_3451_; lean_object* v_fst_3452_; lean_object* v_snd_3453_; lean_object* v_reader_3454_; lean_object* v_writer_3455_; lean_object* v_config_3456_; lean_object* v_events_3457_; lean_object* v_error_3458_; lean_object* v_instant_3459_; uint8_t v_keepAlive_3460_; uint8_t v_forcedFlush_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3495_; 
v___x_3450_ = 0;
v___x_3451_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_3450_, v_machine_3436_);
v_fst_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_fst_3452_);
v_snd_3453_ = lean_ctor_get(v___x_3451_, 1);
lean_inc(v_snd_3453_);
lean_dec_ref(v___x_3451_);
v_reader_3454_ = lean_ctor_get(v_fst_3452_, 0);
v_writer_3455_ = lean_ctor_get(v_fst_3452_, 1);
v_config_3456_ = lean_ctor_get(v_fst_3452_, 2);
v_events_3457_ = lean_ctor_get(v_fst_3452_, 3);
v_error_3458_ = lean_ctor_get(v_fst_3452_, 4);
v_instant_3459_ = lean_ctor_get(v_fst_3452_, 5);
v_keepAlive_3460_ = lean_ctor_get_uint8(v_fst_3452_, sizeof(void*)*6);
v_forcedFlush_3461_ = lean_ctor_get_uint8(v_fst_3452_, sizeof(void*)*6 + 1);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_fst_3452_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3463_ = v_fst_3452_;
v_isShared_3464_ = v_isSharedCheck_3495_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_instant_3459_);
lean_inc(v_error_3458_);
lean_inc(v_events_3457_);
lean_inc(v_config_3456_);
lean_inc(v_writer_3455_);
lean_inc(v_reader_3454_);
lean_dec(v_fst_3452_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3495_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___f_3465_; lean_object* v___f_3466_; uint8_t v___y_3468_; 
v___f_3465_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_3466_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_3466_, 0, v_inst_3204_);
lean_closure_set(v___f_3466_, 1, v_handler_3206_);
if (lean_obj_tag(v_snd_3453_) == 0)
{
uint8_t v_sentMessage_3491_; 
v_sentMessage_3491_ = lean_ctor_get_uint8(v_writer_3455_, sizeof(void*)*6);
if (v_sentMessage_3491_ == 0)
{
lean_object* v_state_3492_; 
v_state_3492_ = lean_ctor_get(v_reader_3454_, 0);
if (lean_obj_tag(v_state_3492_) == 2)
{
v___y_3468_ = v_x_3431_;
goto v___jp_3467_;
}
else
{
v___y_3468_ = v_sentMessage_3491_;
goto v___jp_3467_;
}
}
else
{
uint8_t v___x_3493_; 
v___x_3493_ = 0;
v___y_3468_ = v___x_3493_;
goto v___jp_3467_;
}
}
else
{
uint8_t v___x_3494_; 
v___x_3494_ = 0;
v___y_3468_ = v___x_3494_;
goto v___jp_3467_;
}
v___jp_3467_:
{
lean_object* v___x_3470_; 
if (v_isShared_3464_ == 0)
{
v___x_3470_ = v___x_3463_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_reader_3454_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_writer_3455_);
lean_ctor_set(v_reuseFailAlloc_3490_, 2, v_config_3456_);
lean_ctor_set(v_reuseFailAlloc_3490_, 3, v_events_3457_);
lean_ctor_set(v_reuseFailAlloc_3490_, 4, v_error_3458_);
lean_ctor_set(v_reuseFailAlloc_3490_, 5, v_instant_3459_);
lean_ctor_set_uint8(v_reuseFailAlloc_3490_, sizeof(void*)*6, v_keepAlive_3460_);
lean_ctor_set_uint8(v_reuseFailAlloc_3490_, sizeof(void*)*6 + 1, v_forcedFlush_3461_);
v___x_3470_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v_st_3472_; 
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*6 + 2, v___y_3468_);
lean_inc_ref(v_requestStream_3437_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3470_);
v_st_3472_ = v___x_3448_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_requestStream_3437_);
lean_ctor_set(v_reuseFailAlloc_3489_, 2, v_keepAliveTimeout_3438_);
lean_ctor_set(v_reuseFailAlloc_3489_, 3, v_currentTimeout_3439_);
lean_ctor_set(v_reuseFailAlloc_3489_, 4, v_headerTimeout_3440_);
lean_ctor_set(v_reuseFailAlloc_3489_, 5, v_response_3441_);
lean_ctor_set(v_reuseFailAlloc_3489_, 6, v_respStream_3442_);
lean_ctor_set(v_reuseFailAlloc_3489_, 7, v_expectData_3444_);
lean_ctor_set(v_reuseFailAlloc_3489_, 8, v_pendingHead_3446_);
lean_ctor_set_uint8(v_reuseFailAlloc_3489_, sizeof(void*)*9, v_requiresData_3443_);
lean_ctor_set_uint8(v_reuseFailAlloc_3489_, sizeof(void*)*9 + 1, v_handlerDispatched_3445_);
v_st_3472_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___f_3473_; 
lean_inc_ref(v_st_3472_);
v___f_3473_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_3473_, 0, v_st_3472_);
if (lean_obj_tag(v_snd_3453_) == 1)
{
lean_object* v_val_3474_; uint8_t v_final_3475_; uint8_t v_incomplete_3476_; lean_object* v_chunk_3477_; lean_object* v___f_3478_; lean_object* v___f_3479_; lean_object* v___x_3480_; lean_object* v___f_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
lean_dec_ref(v_st_3472_);
v_val_3474_ = lean_ctor_get(v_snd_3453_, 0);
lean_inc(v_val_3474_);
lean_dec_ref_known(v_snd_3453_, 1);
v_final_3475_ = lean_ctor_get_uint8(v_val_3474_, sizeof(void*)*1);
v_incomplete_3476_ = lean_ctor_get_uint8(v_val_3474_, sizeof(void*)*1 + 1);
v_chunk_3477_ = lean_ctor_get(v_val_3474_, 0);
lean_inc_ref(v_chunk_3477_);
lean_dec(v_val_3474_);
lean_inc_ref_n(v___f_3473_, 2);
v___f_3478_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3478_, 0, v___f_3473_);
lean_inc_ref_n(v_requestStream_3437_, 2);
v___f_3479_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3479_, 0, v_requestStream_3437_);
lean_closure_set(v___f_3479_, 1, v___f_3478_);
lean_closure_set(v___f_3479_, 2, v___f_3473_);
v___x_3480_ = lean_box(v_final_3475_);
v___f_3481_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 7, 5);
lean_closure_set(v___f_3481_, 0, v___x_3480_);
lean_closure_set(v___f_3481_, 1, v___f_3473_);
lean_closure_set(v___f_3481_, 2, v___f_3465_);
lean_closure_set(v___f_3481_, 3, v_requestStream_3437_);
lean_closure_set(v___f_3481_, 4, v___f_3479_);
v___x_3482_ = lean_unsigned_to_nat(0u);
v___x_3483_ = 0;
v___x_3484_ = l_Std_Http_Body_Stream_send(v_requestStream_3437_, v_chunk_3477_, v_incomplete_3476_);
v___x_3485_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3482_, v___x_3483_, v___x_3484_, v___f_3466_);
v___x_3486_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3482_, v___x_3483_, v___x_3485_, v___f_3481_);
return v___x_3486_;
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec_ref(v___f_3473_);
lean_dec_ref(v___f_3466_);
lean_dec(v_snd_3453_);
lean_dec_ref(v_requestStream_3437_);
v___x_3487_ = lean_box(0);
v___x_3488_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_3472_, v___x_3487_);
return v___x_3488_;
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
lean_object* v_x_3497_; 
v_x_3497_ = lean_ctor_get(v_event_3208_, 0);
lean_inc_ref(v_x_3497_);
lean_dec_ref_known(v_event_3208_, 1);
if (lean_obj_tag(v_x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v_onFailure_3499_; lean_object* v___f_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
lean_dec_ref(v_config_3207_);
lean_dec_ref(v_inst_3205_);
v_a_3498_ = lean_ctor_get(v_x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v_x_3497_, 1);
v_onFailure_3499_ = lean_ctor_get(v_inst_3204_, 2);
lean_inc_ref(v_onFailure_3499_);
lean_dec_ref(v_inst_3204_);
v___f_3500_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_3500_, 0, v_state_3209_);
v___x_3501_ = lean_unsigned_to_nat(0u);
v___x_3502_ = 0;
v___x_3503_ = lean_apply_3(v_onFailure_3499_, v_handler_3206_, v_a_3498_, lean_box(0));
v___x_3504_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3501_, v___x_3502_, v___x_3503_, v___f_3500_);
return v___x_3504_;
}
else
{
lean_object* v_machine_3505_; lean_object* v_reader_3506_; lean_object* v_state_3507_; 
v_machine_3505_ = lean_ctor_get(v_state_3209_, 0);
lean_inc_ref(v_machine_3505_);
v_reader_3506_ = lean_ctor_get(v_machine_3505_, 0);
v_state_3507_ = lean_ctor_get(v_reader_3506_, 0);
if (lean_obj_tag(v_state_3507_) == 7)
{
lean_object* v_a_3508_; lean_object* v_requestStream_3509_; lean_object* v_keepAliveTimeout_3510_; lean_object* v_currentTimeout_3511_; lean_object* v_headerTimeout_3512_; lean_object* v_response_3513_; lean_object* v_respStream_3514_; uint8_t v_requiresData_3515_; lean_object* v_expectData_3516_; lean_object* v_pendingHead_3517_; lean_object* v_close_3518_; lean_object* v_isClosed_3519_; lean_object* v_body_3520_; lean_object* v___x_3521_; lean_object* v___f_3522_; lean_object* v___f_3523_; lean_object* v___f_3524_; lean_object* v___x_3525_; uint8_t v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
lean_dec_ref(v_config_3207_);
lean_dec(v_handler_3206_);
lean_dec_ref(v_inst_3204_);
v_a_3508_ = lean_ctor_get(v_x_3497_, 0);
lean_inc(v_a_3508_);
lean_dec_ref_known(v_x_3497_, 1);
v_requestStream_3509_ = lean_ctor_get(v_state_3209_, 1);
lean_inc_ref(v_requestStream_3509_);
v_keepAliveTimeout_3510_ = lean_ctor_get(v_state_3209_, 2);
lean_inc(v_keepAliveTimeout_3510_);
v_currentTimeout_3511_ = lean_ctor_get(v_state_3209_, 3);
lean_inc(v_currentTimeout_3511_);
v_headerTimeout_3512_ = lean_ctor_get(v_state_3209_, 4);
lean_inc(v_headerTimeout_3512_);
v_response_3513_ = lean_ctor_get(v_state_3209_, 5);
lean_inc_ref(v_response_3513_);
v_respStream_3514_ = lean_ctor_get(v_state_3209_, 6);
lean_inc(v_respStream_3514_);
v_requiresData_3515_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9);
v_expectData_3516_ = lean_ctor_get(v_state_3209_, 7);
lean_inc(v_expectData_3516_);
v_pendingHead_3517_ = lean_ctor_get(v_state_3209_, 8);
lean_inc(v_pendingHead_3517_);
lean_dec_ref(v_state_3209_);
v_close_3518_ = lean_ctor_get(v_inst_3205_, 1);
lean_inc_ref(v_close_3518_);
v_isClosed_3519_ = lean_ctor_get(v_inst_3205_, 2);
lean_inc_ref(v_isClosed_3519_);
lean_dec_ref(v_inst_3205_);
v_body_3520_ = lean_ctor_get(v_a_3508_, 1);
lean_inc_n(v_body_3520_, 2);
lean_dec(v_a_3508_);
v___x_3521_ = lean_box(v_requiresData_3515_);
v___f_3522_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 12, 10);
lean_closure_set(v___f_3522_, 0, v_machine_3505_);
lean_closure_set(v___f_3522_, 1, v_requestStream_3509_);
lean_closure_set(v___f_3522_, 2, v_keepAliveTimeout_3510_);
lean_closure_set(v___f_3522_, 3, v_currentTimeout_3511_);
lean_closure_set(v___f_3522_, 4, v_headerTimeout_3512_);
lean_closure_set(v___f_3522_, 5, v_response_3513_);
lean_closure_set(v___f_3522_, 6, v_respStream_3514_);
lean_closure_set(v___f_3522_, 7, v___x_3521_);
lean_closure_set(v___f_3522_, 8, v_expectData_3516_);
lean_closure_set(v___f_3522_, 9, v_pendingHead_3517_);
lean_inc_ref(v___f_3522_);
v___f_3523_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_3523_, 0, v___f_3522_);
v___f_3524_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3524_, 0, v_close_3518_);
lean_closure_set(v___f_3524_, 1, v_body_3520_);
lean_closure_set(v___f_3524_, 2, v___f_3523_);
lean_closure_set(v___f_3524_, 3, v___f_3522_);
v___x_3525_ = lean_unsigned_to_nat(0u);
v___x_3526_ = 0;
v___x_3527_ = lean_apply_2(v_isClosed_3519_, v_body_3520_, lean_box(0));
v___x_3528_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3525_, v___x_3526_, v___x_3527_, v___f_3524_);
return v___x_3528_;
}
else
{
lean_object* v_a_3529_; lean_object* v_requestStream_3530_; lean_object* v_keepAliveTimeout_3531_; lean_object* v_currentTimeout_3532_; lean_object* v_headerTimeout_3533_; lean_object* v_response_3534_; uint8_t v_requiresData_3535_; lean_object* v_expectData_3536_; lean_object* v_pendingHead_3537_; uint8_t v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___f_3541_; lean_object* v___f_3542_; lean_object* v___f_3543_; uint8_t v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___f_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v_a_3529_ = lean_ctor_get(v_x_3497_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v_x_3497_, 1);
v_requestStream_3530_ = lean_ctor_get(v_state_3209_, 1);
lean_inc_ref(v_requestStream_3530_);
v_keepAliveTimeout_3531_ = lean_ctor_get(v_state_3209_, 2);
lean_inc(v_keepAliveTimeout_3531_);
v_currentTimeout_3532_ = lean_ctor_get(v_state_3209_, 3);
lean_inc(v_currentTimeout_3532_);
v_headerTimeout_3533_ = lean_ctor_get(v_state_3209_, 4);
lean_inc(v_headerTimeout_3533_);
v_response_3534_ = lean_ctor_get(v_state_3209_, 5);
lean_inc_ref(v_response_3534_);
v_requiresData_3535_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9);
v_expectData_3536_ = lean_ctor_get(v_state_3209_, 7);
lean_inc(v_expectData_3536_);
v_pendingHead_3537_ = lean_ctor_get(v_state_3209_, 8);
lean_inc(v_pendingHead_3537_);
lean_dec_ref(v_state_3209_);
v___x_3538_ = 0;
v___x_3539_ = lean_box(v_requiresData_3535_);
v___x_3540_ = lean_box(v___x_3538_);
v___f_3541_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_3541_, 0, v_requestStream_3530_);
lean_closure_set(v___f_3541_, 1, v_keepAliveTimeout_3531_);
lean_closure_set(v___f_3541_, 2, v_currentTimeout_3532_);
lean_closure_set(v___f_3541_, 3, v_headerTimeout_3533_);
lean_closure_set(v___f_3541_, 4, v_response_3534_);
lean_closure_set(v___f_3541_, 5, v___x_3539_);
lean_closure_set(v___f_3541_, 6, v_expectData_3536_);
lean_closure_set(v___f_3541_, 7, v___x_3540_);
lean_closure_set(v___f_3541_, 8, v_pendingHead_3537_);
v___f_3542_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 3, 1);
lean_closure_set(v___f_3542_, 0, v___f_3541_);
v___f_3543_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3544_ = 1;
v___x_3545_ = lean_box(v___x_3538_);
v___x_3546_ = lean_box(v___x_3544_);
lean_inc_ref(v_inst_3205_);
lean_inc_ref(v___f_3542_);
v___f_3547_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 10, 8);
lean_closure_set(v___f_3547_, 0, v___x_3545_);
lean_closure_set(v___f_3547_, 1, v___f_3542_);
lean_closure_set(v___f_3547_, 2, v___x_3546_);
lean_closure_set(v___f_3547_, 3, v_inst_3204_);
lean_closure_set(v___f_3547_, 4, v_handler_3206_);
lean_closure_set(v___f_3547_, 5, v_inst_3205_);
lean_closure_set(v___f_3547_, 6, v___f_3543_);
lean_closure_set(v___f_3547_, 7, v___f_3542_);
v___x_3548_ = lean_unsigned_to_nat(0u);
v___x_3549_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3205_, v_config_3207_, v_machine_3505_, v_a_3529_);
v___x_3550_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3548_, v___x_3538_, v___x_3549_, v___f_3547_);
return v___x_3550_;
}
}
}
case 4:
{
lean_object* v_onFailure_3551_; lean_object* v___f_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
lean_dec_ref(v_config_3207_);
lean_dec_ref(v_inst_3205_);
v_onFailure_3551_ = lean_ctor_get(v_inst_3204_, 2);
lean_inc_ref(v_onFailure_3551_);
lean_dec_ref(v_inst_3204_);
v___f_3552_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 3, 1);
lean_closure_set(v___f_3552_, 0, v_state_3209_);
v___x_3553_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2);
v___x_3554_ = lean_unsigned_to_nat(0u);
v___x_3555_ = 0;
v___x_3556_ = lean_apply_3(v_onFailure_3551_, v_handler_3206_, v___x_3553_, lean_box(0));
v___x_3557_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3554_, v___x_3555_, v___x_3556_, v___f_3552_);
return v___x_3557_;
}
case 5:
{
lean_object* v_machine_3558_; lean_object* v_requestStream_3559_; lean_object* v_keepAliveTimeout_3560_; lean_object* v_currentTimeout_3561_; lean_object* v_headerTimeout_3562_; lean_object* v_response_3563_; lean_object* v_respStream_3564_; uint8_t v_requiresData_3565_; lean_object* v_expectData_3566_; lean_object* v_pendingHead_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3581_; 
lean_dec_ref(v_config_3207_);
lean_dec(v_handler_3206_);
lean_dec_ref(v_inst_3205_);
lean_dec_ref(v_inst_3204_);
v_machine_3558_ = lean_ctor_get(v_state_3209_, 0);
v_requestStream_3559_ = lean_ctor_get(v_state_3209_, 1);
v_keepAliveTimeout_3560_ = lean_ctor_get(v_state_3209_, 2);
v_currentTimeout_3561_ = lean_ctor_get(v_state_3209_, 3);
v_headerTimeout_3562_ = lean_ctor_get(v_state_3209_, 4);
v_response_3563_ = lean_ctor_get(v_state_3209_, 5);
v_respStream_3564_ = lean_ctor_get(v_state_3209_, 6);
v_requiresData_3565_ = lean_ctor_get_uint8(v_state_3209_, sizeof(void*)*9);
v_expectData_3566_ = lean_ctor_get(v_state_3209_, 7);
v_pendingHead_3567_ = lean_ctor_get(v_state_3209_, 8);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_state_3209_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3569_ = v_state_3209_;
v_isShared_3570_ = v_isSharedCheck_3581_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_pendingHead_3567_);
lean_inc(v_expectData_3566_);
lean_inc(v_respStream_3564_);
lean_inc(v_response_3563_);
lean_inc(v_headerTimeout_3562_);
lean_inc(v_currentTimeout_3561_);
lean_inc(v_keepAliveTimeout_3560_);
lean_inc(v_requestStream_3559_);
lean_inc(v_machine_3558_);
lean_dec(v_state_3209_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3581_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; lean_object* v___x_3575_; 
v___x_3571_ = lean_box(55);
v___x_3572_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3558_, v___x_3571_);
v___x_3573_ = 0;
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3572_);
v___x_3575_ = v___x_3569_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_requestStream_3559_);
lean_ctor_set(v_reuseFailAlloc_3580_, 2, v_keepAliveTimeout_3560_);
lean_ctor_set(v_reuseFailAlloc_3580_, 3, v_currentTimeout_3561_);
lean_ctor_set(v_reuseFailAlloc_3580_, 4, v_headerTimeout_3562_);
lean_ctor_set(v_reuseFailAlloc_3580_, 5, v_response_3563_);
lean_ctor_set(v_reuseFailAlloc_3580_, 6, v_respStream_3564_);
lean_ctor_set(v_reuseFailAlloc_3580_, 7, v_expectData_3566_);
lean_ctor_set(v_reuseFailAlloc_3580_, 8, v_pendingHead_3567_);
lean_ctor_set_uint8(v_reuseFailAlloc_3580_, sizeof(void*)*9, v_requiresData_3565_);
v___x_3575_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
lean_ctor_set_uint8(v___x_3575_, sizeof(void*)*9 + 1, v___x_3573_);
v___x_3576_ = lean_box(v___x_3573_);
v___x_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3575_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
v___x_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
v___x_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
return v___x_3579_;
}
}
}
default: 
{
uint8_t v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_dec_ref(v_config_3207_);
lean_dec(v_handler_3206_);
lean_dec_ref(v_inst_3205_);
lean_dec_ref(v_inst_3204_);
v___x_3582_ = 1;
v___x_3583_ = lean_box(v___x_3582_);
v___x_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3584_, 0, v_state_3209_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
v___x_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3585_);
return v___x_3586_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_3587_, lean_object* v_inst_3588_, lean_object* v_handler_3589_, lean_object* v_config_3590_, lean_object* v_event_3591_, lean_object* v_state_3592_, lean_object* v_a_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3587_, v_inst_3588_, v_handler_3589_, v_config_3590_, v_event_3591_, v_state_3592_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_3595_, lean_object* v_00_u03b2_3596_, lean_object* v_inst_3597_, lean_object* v_inst_3598_, lean_object* v_handler_3599_, lean_object* v_config_3600_, lean_object* v_event_3601_, lean_object* v_state_3602_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_3597_, v_inst_3598_, v_handler_3599_, v_config_3600_, v_event_3601_, v_state_3602_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_3605_, lean_object* v_00_u03b2_3606_, lean_object* v_inst_3607_, lean_object* v_inst_3608_, lean_object* v_handler_3609_, lean_object* v_config_3610_, lean_object* v_event_3611_, lean_object* v_state_3612_, lean_object* v_a_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_3605_, v_00_u03b2_3606_, v_inst_3607_, v_inst_3608_, v_handler_3609_, v_config_3610_, v_event_3611_, v_state_3612_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_3615_, uint8_t v_handlerDispatched_3616_, lean_object* v_headerTimeout_3617_, lean_object* v_keepAliveTimeout_3618_, lean_object* v_currentTimeout_3619_, lean_object* v_expectData_3620_, lean_object* v_respStream_3621_, lean_object* v_response_3622_, lean_object* v_socket_3623_, uint8_t v_requiresData_3624_, uint8_t v_sentMessage_3625_, lean_object* v_reader_3626_, uint8_t v_requestBodyInterested_3627_, lean_object* v_requestBody_3628_){
_start:
{
lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3642_; 
if (v_requiresData_3624_ == 0)
{
if (v_handlerDispatched_3616_ == 0)
{
goto v___jp_3645_;
}
else
{
if (lean_obj_tag(v_respStream_3621_) == 0)
{
if (v_sentMessage_3625_ == 0)
{
lean_object* v_state_3649_; 
v_state_3649_ = lean_ctor_get(v_reader_3626_, 0);
if (lean_obj_tag(v_state_3649_) == 2)
{
if (v_requestBodyInterested_3627_ == 0)
{
lean_dec(v_socket_3623_);
goto v___jp_3647_;
}
else
{
goto v___jp_3645_;
}
}
else
{
lean_dec(v_socket_3623_);
goto v___jp_3647_;
}
}
else
{
goto v___jp_3645_;
}
}
else
{
goto v___jp_3645_;
}
}
}
else
{
goto v___jp_3645_;
}
v___jp_3630_:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3638_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3638_, 0, v___y_3633_);
lean_ctor_set(v___x_3638_, 1, v___y_3635_);
lean_ctor_set(v___x_3638_, 2, v___y_3637_);
lean_ctor_set(v___x_3638_, 3, v___y_3636_);
lean_ctor_set(v___x_3638_, 4, v_requestBody_3628_);
lean_ctor_set(v___x_3638_, 5, v___y_3634_);
lean_ctor_set(v___x_3638_, 6, v___y_3632_);
lean_ctor_set(v___x_3638_, 7, v___y_3631_);
lean_ctor_set(v___x_3638_, 8, v_connectionContext_3615_);
v___x_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
v___x_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3639_);
return v___x_3640_;
}
v___jp_3641_:
{
if (v_handlerDispatched_3616_ == 0)
{
lean_object* v___x_3643_; 
lean_dec_ref(v_response_3622_);
v___x_3643_ = lean_box(0);
v___y_3631_ = v_headerTimeout_3617_;
v___y_3632_ = v_keepAliveTimeout_3618_;
v___y_3633_ = v___y_3642_;
v___y_3634_ = v_currentTimeout_3619_;
v___y_3635_ = v_expectData_3620_;
v___y_3636_ = v_respStream_3621_;
v___y_3637_ = v___x_3643_;
goto v___jp_3630_;
}
else
{
lean_object* v___x_3644_; 
v___x_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3644_, 0, v_response_3622_);
v___y_3631_ = v_headerTimeout_3617_;
v___y_3632_ = v_keepAliveTimeout_3618_;
v___y_3633_ = v___y_3642_;
v___y_3634_ = v_currentTimeout_3619_;
v___y_3635_ = v_expectData_3620_;
v___y_3636_ = v_respStream_3621_;
v___y_3637_ = v___x_3644_;
goto v___jp_3630_;
}
}
v___jp_3645_:
{
lean_object* v___x_3646_; 
v___x_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3646_, 0, v_socket_3623_);
v___y_3642_ = v___x_3646_;
goto v___jp_3641_;
}
v___jp_3647_:
{
lean_object* v___x_3648_; 
v___x_3648_ = lean_box(0);
v___y_3642_ = v___x_3648_;
goto v___jp_3641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_connectionContext_3650_, lean_object* v_handlerDispatched_3651_, lean_object* v_headerTimeout_3652_, lean_object* v_keepAliveTimeout_3653_, lean_object* v_currentTimeout_3654_, lean_object* v_expectData_3655_, lean_object* v_respStream_3656_, lean_object* v_response_3657_, lean_object* v_socket_3658_, lean_object* v_requiresData_3659_, lean_object* v_sentMessage_3660_, lean_object* v_reader_3661_, lean_object* v_requestBodyInterested_3662_, lean_object* v_requestBody_3663_, lean_object* v___y_3664_){
_start:
{
uint8_t v_handlerDispatched_boxed_3665_; uint8_t v_requiresData_boxed_3666_; uint8_t v_sentMessage_boxed_3667_; uint8_t v_requestBodyInterested_boxed_3668_; lean_object* v_res_3669_; 
v_handlerDispatched_boxed_3665_ = lean_unbox(v_handlerDispatched_3651_);
v_requiresData_boxed_3666_ = lean_unbox(v_requiresData_3659_);
v_sentMessage_boxed_3667_ = lean_unbox(v_sentMessage_3660_);
v_requestBodyInterested_boxed_3668_ = lean_unbox(v_requestBodyInterested_3662_);
v_res_3669_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_3650_, v_handlerDispatched_boxed_3665_, v_headerTimeout_3652_, v_keepAliveTimeout_3653_, v_currentTimeout_3654_, v_expectData_3655_, v_respStream_3656_, v_response_3657_, v_socket_3658_, v_requiresData_boxed_3666_, v_sentMessage_boxed_3667_, v_reader_3661_, v_requestBodyInterested_boxed_3668_, v_requestBody_3663_);
lean_dec_ref(v_reader_3661_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_3670_, lean_object* v_x_3671_){
_start:
{
if (lean_obj_tag(v_x_3671_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3681_; 
lean_dec_ref(v___f_3670_);
v_a_3673_ = lean_ctor_get(v_x_3671_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_x_3671_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3675_ = v_x_3671_;
v_isShared_3676_ = v_isSharedCheck_3681_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v_x_3671_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3681_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3676_ == 0)
{
v___x_3678_ = v___x_3675_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3679_; 
v___x_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
return v___x_3679_;
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3683_; 
v_a_3682_ = lean_ctor_get(v_x_3671_, 0);
lean_inc(v_a_3682_);
lean_dec_ref_known(v_x_3671_, 1);
v___x_3683_ = lean_apply_2(v___f_3670_, v_a_3682_, lean_box(0));
return v___x_3683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_3684_, lean_object* v_x_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_3684_, v_x_3685_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_3692_, uint8_t v_handlerDispatched_3693_, lean_object* v_headerTimeout_3694_, lean_object* v_keepAliveTimeout_3695_, lean_object* v_currentTimeout_3696_, lean_object* v_expectData_3697_, lean_object* v_respStream_3698_, lean_object* v_response_3699_, lean_object* v_socket_3700_, uint8_t v_requiresData_3701_, uint8_t v_sentMessage_3702_, lean_object* v_reader_3703_, uint8_t v_pullBodyStalled_3704_, uint8_t v_requestBodyOpen_3705_, lean_object* v_requestStream_3706_, uint8_t v_requestBodyInterested_3707_){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___f_3713_; lean_object* v___f_3714_; uint8_t v___y_3716_; 
v___x_3709_ = lean_box(v_handlerDispatched_3693_);
v___x_3710_ = lean_box(v_requiresData_3701_);
v___x_3711_ = lean_box(v_sentMessage_3702_);
v___x_3712_ = lean_box(v_requestBodyInterested_3707_);
lean_inc_ref(v_reader_3703_);
v___f_3713_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_3713_, 0, v_connectionContext_3692_);
lean_closure_set(v___f_3713_, 1, v___x_3709_);
lean_closure_set(v___f_3713_, 2, v_headerTimeout_3694_);
lean_closure_set(v___f_3713_, 3, v_keepAliveTimeout_3695_);
lean_closure_set(v___f_3713_, 4, v_currentTimeout_3696_);
lean_closure_set(v___f_3713_, 5, v_expectData_3697_);
lean_closure_set(v___f_3713_, 6, v_respStream_3698_);
lean_closure_set(v___f_3713_, 7, v_response_3699_);
lean_closure_set(v___f_3713_, 8, v_socket_3700_);
lean_closure_set(v___f_3713_, 9, v___x_3710_);
lean_closure_set(v___f_3713_, 10, v___x_3711_);
lean_closure_set(v___f_3713_, 11, v_reader_3703_);
lean_closure_set(v___f_3713_, 12, v___x_3712_);
v___f_3714_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3714_, 0, v___f_3713_);
if (v_sentMessage_3702_ == 0)
{
lean_object* v_state_3720_; 
v_state_3720_ = lean_ctor_get(v_reader_3703_, 0);
lean_inc(v_state_3720_);
lean_dec_ref(v_reader_3703_);
if (lean_obj_tag(v_state_3720_) == 2)
{
lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3731_; 
v_isSharedCheck_3731_ = !lean_is_exclusive(v_state_3720_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; 
v_unused_3732_ = lean_ctor_get(v_state_3720_, 0);
lean_dec(v_unused_3732_);
v___x_3722_ = v_state_3720_;
v_isShared_3723_ = v_isSharedCheck_3731_;
goto v_resetjp_3721_;
}
else
{
lean_dec(v_state_3720_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3731_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
if (v_pullBodyStalled_3704_ == 0)
{
if (v_requestBodyOpen_3705_ == 0)
{
lean_del_object(v___x_3722_);
lean_dec_ref(v_requestStream_3706_);
v___y_3716_ = v_requestBodyOpen_3705_;
goto v___jp_3715_;
}
else
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
lean_ctor_set_tag(v___x_3722_, 1);
lean_ctor_set(v___x_3722_, 0, v_requestStream_3706_);
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_requestStream_3706_);
v___x_3725_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3726_ = lean_unsigned_to_nat(0u);
v___x_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
v___x_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
v___x_3729_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3726_, v_pullBodyStalled_3704_, v___x_3728_, v___f_3714_);
return v___x_3729_;
}
}
}
else
{
lean_del_object(v___x_3722_);
lean_dec_ref(v_requestStream_3706_);
v___y_3716_ = v_sentMessage_3702_;
goto v___jp_3715_;
}
}
}
else
{
lean_dec(v_state_3720_);
lean_dec_ref(v_requestStream_3706_);
v___y_3716_ = v_sentMessage_3702_;
goto v___jp_3715_;
}
}
else
{
uint8_t v___x_3733_; 
lean_dec_ref(v_requestStream_3706_);
lean_dec_ref(v_reader_3703_);
v___x_3733_ = 0;
v___y_3716_ = v___x_3733_;
goto v___jp_3715_;
}
v___jp_3715_:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = lean_unsigned_to_nat(0u);
v___x_3718_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_3719_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3717_, v___y_3716_, v___x_3718_, v___f_3714_);
return v___x_3719_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_3734_ = _args[0];
lean_object* v_handlerDispatched_3735_ = _args[1];
lean_object* v_headerTimeout_3736_ = _args[2];
lean_object* v_keepAliveTimeout_3737_ = _args[3];
lean_object* v_currentTimeout_3738_ = _args[4];
lean_object* v_expectData_3739_ = _args[5];
lean_object* v_respStream_3740_ = _args[6];
lean_object* v_response_3741_ = _args[7];
lean_object* v_socket_3742_ = _args[8];
lean_object* v_requiresData_3743_ = _args[9];
lean_object* v_sentMessage_3744_ = _args[10];
lean_object* v_reader_3745_ = _args[11];
lean_object* v_pullBodyStalled_3746_ = _args[12];
lean_object* v_requestBodyOpen_3747_ = _args[13];
lean_object* v_requestStream_3748_ = _args[14];
lean_object* v_requestBodyInterested_3749_ = _args[15];
lean_object* v___y_3750_ = _args[16];
_start:
{
uint8_t v_handlerDispatched_boxed_3751_; uint8_t v_requiresData_boxed_3752_; uint8_t v_sentMessage_boxed_3753_; uint8_t v_pullBodyStalled_boxed_3754_; uint8_t v_requestBodyOpen_boxed_3755_; uint8_t v_requestBodyInterested_boxed_3756_; lean_object* v_res_3757_; 
v_handlerDispatched_boxed_3751_ = lean_unbox(v_handlerDispatched_3735_);
v_requiresData_boxed_3752_ = lean_unbox(v_requiresData_3743_);
v_sentMessage_boxed_3753_ = lean_unbox(v_sentMessage_3744_);
v_pullBodyStalled_boxed_3754_ = lean_unbox(v_pullBodyStalled_3746_);
v_requestBodyOpen_boxed_3755_ = lean_unbox(v_requestBodyOpen_3747_);
v_requestBodyInterested_boxed_3756_ = lean_unbox(v_requestBodyInterested_3749_);
v_res_3757_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_3734_, v_handlerDispatched_boxed_3751_, v_headerTimeout_3736_, v_keepAliveTimeout_3737_, v_currentTimeout_3738_, v_expectData_3739_, v_respStream_3740_, v_response_3741_, v_socket_3742_, v_requiresData_boxed_3752_, v_sentMessage_boxed_3753_, v_reader_3745_, v_pullBodyStalled_boxed_3754_, v_requestBodyOpen_boxed_3755_, v_requestStream_3748_, v_requestBodyInterested_boxed_3756_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_3758_, lean_object* v_x_3759_){
_start:
{
if (lean_obj_tag(v_x_3759_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3769_; 
lean_dec_ref(v___f_3758_);
v_a_3761_ = lean_ctor_get(v_x_3759_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v_x_3759_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3763_ = v_x_3759_;
v_isShared_3764_ = v_isSharedCheck_3769_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v_x_3759_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3769_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3767_; 
v___x_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
return v___x_3767_;
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3771_; 
v_a_3770_ = lean_ctor_get(v_x_3759_, 0);
lean_inc(v_a_3770_);
lean_dec_ref_known(v_x_3759_, 1);
v___x_3771_ = lean_apply_2(v___f_3758_, v_a_3770_, lean_box(0));
return v___x_3771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_3772_, lean_object* v_x_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_3772_, v_x_3773_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_3776_, uint8_t v_handlerDispatched_3777_, lean_object* v_headerTimeout_3778_, lean_object* v_keepAliveTimeout_3779_, lean_object* v_currentTimeout_3780_, lean_object* v_expectData_3781_, lean_object* v_respStream_3782_, lean_object* v_response_3783_, lean_object* v_socket_3784_, uint8_t v_requiresData_3785_, uint8_t v_sentMessage_3786_, lean_object* v_reader_3787_, uint8_t v_pullBodyStalled_3788_, lean_object* v_requestStream_3789_, uint8_t v_requestBodyOpen_3790_){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___f_3797_; lean_object* v___f_3798_; uint8_t v___y_3800_; 
v___x_3792_ = lean_box(v_handlerDispatched_3777_);
v___x_3793_ = lean_box(v_requiresData_3785_);
v___x_3794_ = lean_box(v_sentMessage_3786_);
v___x_3795_ = lean_box(v_pullBodyStalled_3788_);
v___x_3796_ = lean_box(v_requestBodyOpen_3790_);
lean_inc_ref(v_requestStream_3789_);
lean_inc_ref(v_reader_3787_);
v___f_3797_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 17, 15);
lean_closure_set(v___f_3797_, 0, v_connectionContext_3776_);
lean_closure_set(v___f_3797_, 1, v___x_3792_);
lean_closure_set(v___f_3797_, 2, v_headerTimeout_3778_);
lean_closure_set(v___f_3797_, 3, v_keepAliveTimeout_3779_);
lean_closure_set(v___f_3797_, 4, v_currentTimeout_3780_);
lean_closure_set(v___f_3797_, 5, v_expectData_3781_);
lean_closure_set(v___f_3797_, 6, v_respStream_3782_);
lean_closure_set(v___f_3797_, 7, v_response_3783_);
lean_closure_set(v___f_3797_, 8, v_socket_3784_);
lean_closure_set(v___f_3797_, 9, v___x_3793_);
lean_closure_set(v___f_3797_, 10, v___x_3794_);
lean_closure_set(v___f_3797_, 11, v_reader_3787_);
lean_closure_set(v___f_3797_, 12, v___x_3795_);
lean_closure_set(v___f_3797_, 13, v___x_3796_);
lean_closure_set(v___f_3797_, 14, v_requestStream_3789_);
v___f_3798_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3798_, 0, v___f_3797_);
if (v_sentMessage_3786_ == 0)
{
lean_object* v_state_3806_; 
v_state_3806_ = lean_ctor_get(v_reader_3787_, 0);
lean_inc(v_state_3806_);
lean_dec_ref(v_reader_3787_);
if (lean_obj_tag(v_state_3806_) == 2)
{
lean_dec_ref_known(v_state_3806_, 1);
if (v_requestBodyOpen_3790_ == 0)
{
lean_dec_ref(v_requestStream_3789_);
v___y_3800_ = v_requestBodyOpen_3790_;
goto v___jp_3799_;
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_unsigned_to_nat(0u);
v___x_3808_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_3789_);
v___x_3809_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3807_, v_sentMessage_3786_, v___x_3808_, v___f_3798_);
return v___x_3809_;
}
}
else
{
lean_dec(v_state_3806_);
lean_dec_ref(v_requestStream_3789_);
v___y_3800_ = v_sentMessage_3786_;
goto v___jp_3799_;
}
}
else
{
uint8_t v___x_3810_; 
lean_dec_ref(v_requestStream_3789_);
lean_dec_ref(v_reader_3787_);
v___x_3810_ = 0;
v___y_3800_ = v___x_3810_;
goto v___jp_3799_;
}
v___jp_3799_:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3801_ = lean_unsigned_to_nat(0u);
v___x_3802_ = lean_box(v___y_3800_);
v___x_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
v___x_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3803_);
v___x_3805_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3801_, v___y_3800_, v___x_3804_, v___f_3798_);
return v___x_3805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_connectionContext_3811_, lean_object* v_handlerDispatched_3812_, lean_object* v_headerTimeout_3813_, lean_object* v_keepAliveTimeout_3814_, lean_object* v_currentTimeout_3815_, lean_object* v_expectData_3816_, lean_object* v_respStream_3817_, lean_object* v_response_3818_, lean_object* v_socket_3819_, lean_object* v_requiresData_3820_, lean_object* v_sentMessage_3821_, lean_object* v_reader_3822_, lean_object* v_pullBodyStalled_3823_, lean_object* v_requestStream_3824_, lean_object* v_requestBodyOpen_3825_, lean_object* v___y_3826_){
_start:
{
uint8_t v_handlerDispatched_boxed_3827_; uint8_t v_requiresData_boxed_3828_; uint8_t v_sentMessage_boxed_3829_; uint8_t v_pullBodyStalled_boxed_3830_; uint8_t v_requestBodyOpen_boxed_3831_; lean_object* v_res_3832_; 
v_handlerDispatched_boxed_3827_ = lean_unbox(v_handlerDispatched_3812_);
v_requiresData_boxed_3828_ = lean_unbox(v_requiresData_3820_);
v_sentMessage_boxed_3829_ = lean_unbox(v_sentMessage_3821_);
v_pullBodyStalled_boxed_3830_ = lean_unbox(v_pullBodyStalled_3823_);
v_requestBodyOpen_boxed_3831_ = lean_unbox(v_requestBodyOpen_3825_);
v_res_3832_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_3811_, v_handlerDispatched_boxed_3827_, v_headerTimeout_3813_, v_keepAliveTimeout_3814_, v_currentTimeout_3815_, v_expectData_3816_, v_respStream_3817_, v_response_3818_, v_socket_3819_, v_requiresData_boxed_3828_, v_sentMessage_boxed_3829_, v_reader_3822_, v_pullBodyStalled_boxed_3830_, v_requestStream_3824_, v_requestBodyOpen_boxed_3831_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(uint8_t v_sentMessage_3833_, lean_object* v___f_3834_, uint8_t v___x_3835_, lean_object* v_x_3836_){
_start:
{
uint8_t v___y_3839_; 
if (lean_obj_tag(v_x_3836_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3853_; 
lean_dec_ref(v___f_3834_);
v_a_3845_ = lean_ctor_get(v_x_3836_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_x_3836_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3847_ = v_x_3836_;
v_isShared_3848_ = v_isSharedCheck_3853_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v_x_3836_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3853_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
lean_object* v___x_3851_; 
v___x_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
return v___x_3851_;
}
}
}
else
{
lean_object* v_a_3854_; uint8_t v___x_3855_; 
v_a_3854_ = lean_ctor_get(v_x_3836_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v_x_3836_, 1);
v___x_3855_ = lean_unbox(v_a_3854_);
lean_dec(v_a_3854_);
if (v___x_3855_ == 0)
{
v___y_3839_ = v___x_3835_;
goto v___jp_3838_;
}
else
{
v___y_3839_ = v_sentMessage_3833_;
goto v___jp_3838_;
}
}
v___jp_3838_:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3840_ = lean_unsigned_to_nat(0u);
v___x_3841_ = lean_box(v___y_3839_);
v___x_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3841_);
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
v___x_3844_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3840_, v_sentMessage_3833_, v___x_3843_, v___f_3834_);
return v___x_3844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed(lean_object* v_sentMessage_3856_, lean_object* v___f_3857_, lean_object* v___x_3858_, lean_object* v_x_3859_, lean_object* v___y_3860_){
_start:
{
uint8_t v_sentMessage_boxed_3861_; uint8_t v___x_2892__boxed_3862_; lean_object* v_res_3863_; 
v_sentMessage_boxed_3861_ = lean_unbox(v_sentMessage_3856_);
v___x_2892__boxed_3862_ = lean_unbox(v___x_3858_);
v_res_3863_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8(v_sentMessage_boxed_3861_, v___f_3857_, v___x_2892__boxed_3862_, v_x_3859_);
return v_res_3863_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0(void){
_start:
{
lean_object* v___f_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___f_3864_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_3865_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_3866_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___x_3867_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_3867_, 0, lean_box(0));
lean_closure_set(v___x_3867_, 1, lean_box(0));
lean_closure_set(v___x_3867_, 2, v___x_3866_);
lean_closure_set(v___x_3867_, 3, lean_box(0));
lean_closure_set(v___x_3867_, 4, lean_box(0));
lean_closure_set(v___x_3867_, 5, v___x_3865_);
lean_closure_set(v___x_3867_, 6, v___f_3864_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_3868_, lean_object* v_connectionContext_3869_, lean_object* v_state_3870_){
_start:
{
lean_object* v_machine_3872_; lean_object* v_writer_3873_; lean_object* v_requestStream_3874_; lean_object* v_keepAliveTimeout_3875_; lean_object* v_currentTimeout_3876_; lean_object* v_headerTimeout_3877_; lean_object* v_response_3878_; lean_object* v_respStream_3879_; uint8_t v_requiresData_3880_; lean_object* v_expectData_3881_; uint8_t v_handlerDispatched_3882_; lean_object* v_reader_3883_; uint8_t v_pullBodyStalled_3884_; uint8_t v_sentMessage_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___f_3890_; lean_object* v___f_3891_; uint8_t v___y_3893_; 
v_machine_3872_ = lean_ctor_get(v_state_3870_, 0);
lean_inc_ref(v_machine_3872_);
v_writer_3873_ = lean_ctor_get(v_machine_3872_, 1);
lean_inc_ref(v_writer_3873_);
v_requestStream_3874_ = lean_ctor_get(v_state_3870_, 1);
lean_inc_ref_n(v_requestStream_3874_, 2);
v_keepAliveTimeout_3875_ = lean_ctor_get(v_state_3870_, 2);
lean_inc(v_keepAliveTimeout_3875_);
v_currentTimeout_3876_ = lean_ctor_get(v_state_3870_, 3);
lean_inc(v_currentTimeout_3876_);
v_headerTimeout_3877_ = lean_ctor_get(v_state_3870_, 4);
lean_inc(v_headerTimeout_3877_);
v_response_3878_ = lean_ctor_get(v_state_3870_, 5);
lean_inc_ref(v_response_3878_);
v_respStream_3879_ = lean_ctor_get(v_state_3870_, 6);
lean_inc(v_respStream_3879_);
v_requiresData_3880_ = lean_ctor_get_uint8(v_state_3870_, sizeof(void*)*9);
v_expectData_3881_ = lean_ctor_get(v_state_3870_, 7);
lean_inc(v_expectData_3881_);
v_handlerDispatched_3882_ = lean_ctor_get_uint8(v_state_3870_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_3870_);
v_reader_3883_ = lean_ctor_get(v_machine_3872_, 0);
lean_inc_ref_n(v_reader_3883_, 2);
v_pullBodyStalled_3884_ = lean_ctor_get_uint8(v_machine_3872_, sizeof(void*)*6 + 2);
lean_dec_ref(v_machine_3872_);
v_sentMessage_3885_ = lean_ctor_get_uint8(v_writer_3873_, sizeof(void*)*6);
lean_dec_ref(v_writer_3873_);
v___x_3886_ = lean_box(v_handlerDispatched_3882_);
v___x_3887_ = lean_box(v_requiresData_3880_);
v___x_3888_ = lean_box(v_sentMessage_3885_);
v___x_3889_ = lean_box(v_pullBodyStalled_3884_);
v___f_3890_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 16, 14);
lean_closure_set(v___f_3890_, 0, v_connectionContext_3869_);
lean_closure_set(v___f_3890_, 1, v___x_3886_);
lean_closure_set(v___f_3890_, 2, v_headerTimeout_3877_);
lean_closure_set(v___f_3890_, 3, v_keepAliveTimeout_3875_);
lean_closure_set(v___f_3890_, 4, v_currentTimeout_3876_);
lean_closure_set(v___f_3890_, 5, v_expectData_3881_);
lean_closure_set(v___f_3890_, 6, v_respStream_3879_);
lean_closure_set(v___f_3890_, 7, v_response_3878_);
lean_closure_set(v___f_3890_, 8, v_socket_3868_);
lean_closure_set(v___f_3890_, 9, v___x_3887_);
lean_closure_set(v___f_3890_, 10, v___x_3888_);
lean_closure_set(v___f_3890_, 11, v_reader_3883_);
lean_closure_set(v___f_3890_, 12, v___x_3889_);
lean_closure_set(v___f_3890_, 13, v_requestStream_3874_);
v___f_3891_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3891_, 0, v___f_3890_);
if (v_sentMessage_3885_ == 0)
{
lean_object* v_state_3899_; 
v_state_3899_ = lean_ctor_get(v_reader_3883_, 0);
lean_inc(v_state_3899_);
lean_dec_ref(v_reader_3883_);
if (lean_obj_tag(v_state_3899_) == 2)
{
uint8_t v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___f_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___f_3906_; lean_object* v___f_3907_; lean_object* v___x_3908_; lean_object* v___x_2542__overap_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_dec_ref_known(v_state_3899_, 1);
v___x_3900_ = 1;
v___x_3901_ = lean_box(v_sentMessage_3885_);
v___x_3902_ = lean_box(v___x_3900_);
v___f_3903_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_3903_, 0, v___x_3901_);
lean_closure_set(v___f_3903_, 1, v___f_3891_);
lean_closure_set(v___f_3903_, 2, v___x_3902_);
v___x_3904_ = lean_unsigned_to_nat(0u);
v___x_3905_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_3906_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_3907_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_3908_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0);
v___x_2542__overap_3909_ = l_Std_Mutex_atomically___redArg(v___x_3905_, v___f_3906_, v___f_3907_, v_requestStream_3874_, v___x_3908_);
v___x_3910_ = lean_apply_1(v___x_2542__overap_3909_, lean_box(0));
v___x_3911_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3904_, v_sentMessage_3885_, v___x_3910_, v___f_3903_);
return v___x_3911_;
}
else
{
lean_dec(v_state_3899_);
lean_dec_ref(v_requestStream_3874_);
v___y_3893_ = v_sentMessage_3885_;
goto v___jp_3892_;
}
}
else
{
uint8_t v___x_3912_; 
lean_dec_ref(v_reader_3883_);
lean_dec_ref(v_requestStream_3874_);
v___x_3912_ = 0;
v___y_3893_ = v___x_3912_;
goto v___jp_3892_;
}
v___jp_3892_:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3894_ = lean_unsigned_to_nat(0u);
v___x_3895_ = lean_box(v___y_3893_);
v___x_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
v___x_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
v___x_3898_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3894_, v___y_3893_, v___x_3897_, v___f_3891_);
return v___x_3898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_3913_, lean_object* v_connectionContext_3914_, lean_object* v_state_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3913_, v_connectionContext_3914_, v_state_3915_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_3918_, lean_object* v_00_u03b2_3919_, lean_object* v_inst_3920_, lean_object* v_socket_3921_, lean_object* v_connectionContext_3922_, lean_object* v_state_3923_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_3921_, v_connectionContext_3922_, v_state_3923_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_3926_, lean_object* v_00_u03b2_3927_, lean_object* v_inst_3928_, lean_object* v_socket_3929_, lean_object* v_connectionContext_3930_, lean_object* v_state_3931_, lean_object* v_a_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_3926_, v_00_u03b2_3927_, v_inst_3928_, v_socket_3929_, v_connectionContext_3930_, v_state_3931_);
lean_dec_ref(v_inst_3928_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_3934_){
_start:
{
if (lean_obj_tag(v_x_3934_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3944_; 
v_a_3936_ = lean_ctor_get(v_x_3934_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_x_3934_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3938_ = v_x_3934_;
v_isShared_3939_ = v_isSharedCheck_3944_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v_x_3934_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3944_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; 
v___x_3942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
return v___x_3942_;
}
}
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3954_; 
v_a_3945_ = lean_ctor_get(v_x_3934_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_x_3934_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3947_ = v_x_3934_;
v_isShared_3948_ = v_isSharedCheck_3954_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v_x_3934_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3954_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3949_; lean_object* v___x_3951_; 
v___x_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3949_, 0, v_a_3945_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 0, v___x_3949_);
v___x_3951_ = v___x_3947_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3949_);
v___x_3951_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
lean_object* v___x_3952_; 
v___x_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
return v___x_3952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_3955_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_3962_){
_start:
{
if (lean_obj_tag(v_x_3962_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3972_; 
v_a_3964_ = lean_ctor_get(v_x_3962_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v_x_3962_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3966_ = v_x_3962_;
v_isShared_3967_ = v_isSharedCheck_3972_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v_x_3962_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3972_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
lean_object* v___x_3970_; 
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
return v___x_3970_;
}
}
}
else
{
lean_object* v___x_3973_; 
lean_dec_ref_known(v_x_3962_, 1);
v___x_3973_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___closed__1));
return v___x_3973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_3974_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_onFailure_3977_, lean_object* v_handler_3978_, lean_object* v___f_3979_, lean_object* v_x_3980_){
_start:
{
if (lean_obj_tag(v_x_3980_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_a_3982_ = lean_ctor_get(v_x_3980_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v_x_3980_, 1);
v___x_3983_ = lean_unsigned_to_nat(0u);
v___x_3984_ = 0;
v___x_3985_ = lean_apply_3(v_onFailure_3977_, v_handler_3978_, v_a_3982_, lean_box(0));
v___x_3986_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3983_, v___x_3984_, v___x_3985_, v___f_3979_);
return v___x_3986_;
}
else
{
lean_object* v___x_3987_; 
lean_dec_ref(v___f_3979_);
lean_dec(v_handler_3978_);
lean_dec_ref(v_onFailure_3977_);
v___x_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3987_, 0, v_x_3980_);
return v___x_3987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_onFailure_3988_, lean_object* v_handler_3989_, lean_object* v___f_3990_, lean_object* v_x_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_onFailure_3988_, v_handler_3989_, v___f_3990_, v_x_3991_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_x_3994_){
_start:
{
if (lean_obj_tag(v_x_3994_) == 0)
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4004_; 
v_a_3996_ = lean_ctor_get(v_x_3994_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v_x_3994_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3998_ = v_x_3994_;
v_isShared_3999_ = v_isSharedCheck_4004_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v_x_3994_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4004_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
lean_object* v___x_4002_; 
v___x_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
return v___x_4002_;
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4023_; 
v_a_4005_ = lean_ctor_get(v_x_3994_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v_x_3994_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4007_ = v_x_3994_;
v_isShared_4008_ = v_isSharedCheck_4023_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v_x_3994_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4023_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v_snd_4009_; uint8_t v___x_4010_; 
v_snd_4009_ = lean_ctor_get(v_a_4005_, 1);
v___x_4010_ = lean_unbox(v_snd_4009_);
if (v___x_4010_ == 0)
{
lean_object* v_fst_4011_; lean_object* v___x_4012_; lean_object* v___x_4014_; 
v_fst_4011_ = lean_ctor_get(v_a_4005_, 0);
lean_inc(v_fst_4011_);
lean_dec(v_a_4005_);
v___x_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4012_, 0, v_fst_4011_);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v___x_4012_);
v___x_4014_ = v___x_4007_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
lean_object* v___x_4015_; 
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4014_);
return v___x_4015_;
}
}
else
{
lean_object* v_fst_4017_; lean_object* v___x_4018_; lean_object* v___x_4020_; 
v_fst_4017_ = lean_ctor_get(v_a_4005_, 0);
lean_inc(v_fst_4017_);
lean_dec(v_a_4005_);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v_fst_4017_);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v___x_4018_);
v___x_4020_ = v___x_4007_;
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v_x_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_x_4024_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_inst_4027_, lean_object* v_socket_4028_, lean_object* v_____r_4029_){
_start:
{
lean_object* v_val_4032_; lean_object* v_close_4034_; lean_object* v___x_4035_; 
v_close_4034_ = lean_ctor_get(v_inst_4027_, 3);
lean_inc_ref(v_close_4034_);
lean_dec_ref(v_inst_4027_);
v___x_4035_ = lean_apply_2(v_close_4034_, v_socket_4028_, lean_box(0));
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
lean_ctor_set_tag(v___x_4038_, 1);
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
v_val_4032_ = v___x_4041_;
goto v___jp_4031_;
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
v_a_4044_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4035_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4035_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
lean_ctor_set_tag(v___x_4046_, 0);
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
v_val_4032_ = v___x_4049_;
goto v___jp_4031_;
}
}
}
v___jp_4031_:
{
lean_object* v___x_4033_; 
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v_val_4032_);
return v___x_4033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_inst_4052_, lean_object* v_socket_4053_, lean_object* v_____r_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_inst_4052_, v_socket_4053_, v_____r_4054_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v___f_4057_, lean_object* v_x_4058_){
_start:
{
if (lean_obj_tag(v_x_4058_) == 0)
{
lean_object* v___x_4060_; 
lean_dec_ref(v___f_4057_);
v___x_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4060_, 0, v_x_4058_);
return v___x_4060_;
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4062_; 
v_a_4061_ = lean_ctor_get(v_x_4058_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v_x_4058_, 1);
v___x_4062_ = lean_apply_2(v___f_4057_, v_a_4061_, lean_box(0));
return v___x_4062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object* v___f_4063_, lean_object* v_x_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v___f_4063_, v_x_4064_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_close_4067_, lean_object* v_val_4068_, lean_object* v___f_4069_, lean_object* v___f_4070_, lean_object* v_x_4071_){
_start:
{
if (lean_obj_tag(v_x_4071_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4081_; 
lean_dec_ref(v___f_4070_);
lean_dec_ref(v___f_4069_);
lean_dec(v_val_4068_);
lean_dec_ref(v_close_4067_);
v_a_4073_ = lean_ctor_get(v_x_4071_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_x_4071_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4075_ = v_x_4071_;
v_isShared_4076_ = v_isSharedCheck_4081_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v_x_4071_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4081_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4078_);
return v___x_4079_;
}
}
}
else
{
lean_object* v_a_4082_; uint8_t v___x_4083_; 
v_a_4082_ = lean_ctor_get(v_x_4071_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v_x_4071_, 1);
v___x_4083_ = lean_unbox(v_a_4082_);
if (v___x_4083_ == 0)
{
lean_object* v___x_4084_; lean_object* v___x_4085_; uint8_t v___x_4086_; lean_object* v___x_4087_; 
lean_dec_ref(v___f_4070_);
v___x_4084_ = lean_unsigned_to_nat(0u);
v___x_4085_ = lean_apply_2(v_close_4067_, v_val_4068_, lean_box(0));
v___x_4086_ = lean_unbox(v_a_4082_);
lean_dec(v_a_4082_);
v___x_4087_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4084_, v___x_4086_, v___x_4085_, v___f_4069_);
return v___x_4087_;
}
else
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
lean_dec(v_a_4082_);
lean_dec_ref(v___f_4069_);
lean_dec(v_val_4068_);
lean_dec_ref(v_close_4067_);
v___x_4088_ = lean_box(0);
v___x_4089_ = lean_apply_2(v___f_4070_, v___x_4088_, lean_box(0));
return v___x_4089_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_close_4090_, lean_object* v_val_4091_, lean_object* v___f_4092_, lean_object* v___f_4093_, lean_object* v_x_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_close_4090_, v_val_4091_, v___f_4092_, v___f_4093_, v_x_4094_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_respStream_4097_, lean_object* v_responseBodyInstance_4098_, lean_object* v___f_4099_, lean_object* v___f_4100_, lean_object* v_____r_4101_){
_start:
{
if (lean_obj_tag(v_respStream_4097_) == 1)
{
lean_object* v_val_4103_; lean_object* v_close_4104_; lean_object* v_isClosed_4105_; lean_object* v___f_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v_val_4103_ = lean_ctor_get(v_respStream_4097_, 0);
lean_inc_n(v_val_4103_, 2);
lean_dec_ref_known(v_respStream_4097_, 1);
v_close_4104_ = lean_ctor_get(v_responseBodyInstance_4098_, 1);
lean_inc_ref(v_close_4104_);
v_isClosed_4105_ = lean_ctor_get(v_responseBodyInstance_4098_, 2);
lean_inc_ref(v_isClosed_4105_);
lean_dec_ref(v_responseBodyInstance_4098_);
v___f_4106_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_4106_, 0, v_close_4104_);
lean_closure_set(v___f_4106_, 1, v_val_4103_);
lean_closure_set(v___f_4106_, 2, v___f_4099_);
lean_closure_set(v___f_4106_, 3, v___f_4100_);
v___x_4107_ = lean_unsigned_to_nat(0u);
v___x_4108_ = 0;
v___x_4109_ = lean_apply_2(v_isClosed_4105_, v_val_4103_, lean_box(0));
v___x_4110_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4107_, v___x_4108_, v___x_4109_, v___f_4106_);
return v___x_4110_;
}
else
{
lean_object* v___x_4111_; lean_object* v___x_4112_; 
lean_dec_ref(v___f_4099_);
lean_dec_ref(v_responseBodyInstance_4098_);
lean_dec(v_respStream_4097_);
v___x_4111_ = lean_box(0);
v___x_4112_ = lean_apply_2(v___f_4100_, v___x_4111_, lean_box(0));
return v___x_4112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_respStream_4113_, lean_object* v_responseBodyInstance_4114_, lean_object* v___f_4115_, lean_object* v___f_4116_, lean_object* v_____r_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_respStream_4113_, v_responseBodyInstance_4114_, v___f_4115_, v___f_4116_, v_____r_4117_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_requestStream_4120_, lean_object* v___f_4121_, lean_object* v___f_4122_, lean_object* v_x_4123_){
_start:
{
if (lean_obj_tag(v_x_4123_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4133_; 
lean_dec_ref(v___f_4122_);
lean_dec_ref(v___f_4121_);
lean_dec_ref(v_requestStream_4120_);
v_a_4125_ = lean_ctor_get(v_x_4123_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_x_4123_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4127_ = v_x_4123_;
v_isShared_4128_ = v_isSharedCheck_4133_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v_x_4123_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4133_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
lean_object* v___x_4131_; 
v___x_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4130_);
return v___x_4131_;
}
}
}
else
{
lean_object* v_a_4134_; uint8_t v___x_4135_; 
v_a_4134_ = lean_ctor_get(v_x_4123_, 0);
lean_inc(v_a_4134_);
lean_dec_ref_known(v_x_4123_, 1);
v___x_4135_ = lean_unbox(v_a_4134_);
if (v___x_4135_ == 0)
{
lean_object* v___x_4136_; lean_object* v___x_4137_; uint8_t v___x_4138_; lean_object* v___x_4139_; 
lean_dec_ref(v___f_4122_);
v___x_4136_ = lean_unsigned_to_nat(0u);
v___x_4137_ = l_Std_Http_Body_Stream_close(v_requestStream_4120_);
v___x_4138_ = lean_unbox(v_a_4134_);
lean_dec(v_a_4134_);
v___x_4139_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4136_, v___x_4138_, v___x_4137_, v___f_4121_);
return v___x_4139_;
}
else
{
lean_object* v___x_4140_; lean_object* v___x_4141_; 
lean_dec(v_a_4134_);
lean_dec_ref(v___f_4121_);
lean_dec_ref(v_requestStream_4120_);
v___x_4140_ = lean_box(0);
v___x_4141_ = lean_apply_2(v___f_4122_, v___x_4140_, lean_box(0));
return v___x_4141_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_requestStream_4142_, lean_object* v___f_4143_, lean_object* v___f_4144_, lean_object* v_x_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_requestStream_4142_, v___f_4143_, v___f_4144_, v_x_4145_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v_responseBodyInstance_4148_, lean_object* v___f_4149_, lean_object* v___f_4150_, lean_object* v___f_4151_, lean_object* v_x_4152_){
_start:
{
if (lean_obj_tag(v_x_4152_) == 0)
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4162_; 
lean_dec_ref(v___f_4151_);
lean_dec_ref(v___f_4150_);
lean_dec_ref(v___f_4149_);
lean_dec_ref(v_responseBodyInstance_4148_);
v_a_4154_ = lean_ctor_get(v_x_4152_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_x_4152_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4156_ = v_x_4152_;
v_isShared_4157_ = v_isSharedCheck_4162_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v_x_4152_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4162_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
lean_object* v___x_4160_; 
v___x_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
return v___x_4160_;
}
}
}
else
{
lean_object* v_a_4163_; lean_object* v_requestStream_4164_; lean_object* v_respStream_4165_; lean_object* v___f_4166_; lean_object* v___f_4167_; lean_object* v___f_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; lean_object* v___x_4171_; lean_object* v___f_4172_; lean_object* v___f_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4542__overap_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v_a_4163_ = lean_ctor_get(v_x_4152_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v_x_4152_, 1);
v_requestStream_4164_ = lean_ctor_get(v_a_4163_, 1);
lean_inc_ref_n(v_requestStream_4164_, 2);
v_respStream_4165_ = lean_ctor_get(v_a_4163_, 6);
lean_inc(v_respStream_4165_);
lean_dec(v_a_4163_);
v___f_4166_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_4166_, 0, v_respStream_4165_);
lean_closure_set(v___f_4166_, 1, v_responseBodyInstance_4148_);
lean_closure_set(v___f_4166_, 2, v___f_4149_);
lean_closure_set(v___f_4166_, 3, v___f_4150_);
lean_inc_ref(v___f_4166_);
v___f_4167_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4167_, 0, v___f_4166_);
v___f_4168_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 5, 3);
lean_closure_set(v___f_4168_, 0, v_requestStream_4164_);
lean_closure_set(v___f_4168_, 1, v___f_4167_);
lean_closure_set(v___f_4168_, 2, v___f_4166_);
v___x_4169_ = lean_unsigned_to_nat(0u);
v___x_4170_ = 0;
v___x_4171_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__0);
v___f_4172_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__5);
v___f_4173_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__6));
v___x_4174_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___closed__11);
v___x_4175_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4175_, 0, lean_box(0));
lean_closure_set(v___x_4175_, 1, lean_box(0));
lean_closure_set(v___x_4175_, 2, v___x_4171_);
lean_closure_set(v___x_4175_, 3, lean_box(0));
lean_closure_set(v___x_4175_, 4, lean_box(0));
lean_closure_set(v___x_4175_, 5, v___x_4174_);
lean_closure_set(v___x_4175_, 6, v___f_4151_);
v___x_4542__overap_4176_ = l_Std_Mutex_atomically___redArg(v___x_4171_, v___f_4172_, v___f_4173_, v_requestStream_4164_, v___x_4175_);
v___x_4177_ = lean_apply_1(v___x_4542__overap_4176_, lean_box(0));
v___x_4178_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4169_, v___x_4170_, v___x_4177_, v___f_4168_);
return v___x_4178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v_responseBodyInstance_4179_, lean_object* v___f_4180_, lean_object* v___f_4181_, lean_object* v___f_4182_, lean_object* v_x_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v_responseBodyInstance_4179_, v___f_4180_, v___f_4181_, v___f_4182_, v_x_4183_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_4186_, lean_object* v_responseBodyInstance_4187_, lean_object* v_handler_4188_, lean_object* v_config_4189_, lean_object* v___x_4190_, uint8_t v___x_4191_, lean_object* v___f_4192_, lean_object* v_x_4193_){
_start:
{
if (lean_obj_tag(v_x_4193_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4203_; 
lean_dec_ref(v___f_4192_);
lean_dec_ref(v___x_4190_);
lean_dec_ref(v_config_4189_);
lean_dec(v_handler_4188_);
lean_dec_ref(v_responseBodyInstance_4187_);
lean_dec_ref(v_h_4186_);
v_a_4195_ = lean_ctor_get(v_x_4193_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v_x_4193_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4197_ = v_x_4193_;
v_isShared_4198_ = v_isSharedCheck_4203_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v_x_4193_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4203_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
lean_object* v___x_4201_; 
v___x_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4200_);
return v___x_4201_;
}
}
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_a_4204_ = lean_ctor_get(v_x_4193_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v_x_4193_, 1);
v___x_4205_ = lean_unsigned_to_nat(0u);
v___x_4206_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_4186_, v_responseBodyInstance_4187_, v_handler_4188_, v_config_4189_, v_a_4204_, v___x_4190_);
v___x_4207_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4205_, v___x_4191_, v___x_4206_, v___f_4192_);
return v___x_4207_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_4208_, lean_object* v_responseBodyInstance_4209_, lean_object* v_handler_4210_, lean_object* v_config_4211_, lean_object* v___x_4212_, lean_object* v___x_4213_, lean_object* v___f_4214_, lean_object* v_x_4215_, lean_object* v___y_4216_){
_start:
{
uint8_t v___x_5208__boxed_4217_; lean_object* v_res_4218_; 
v___x_5208__boxed_4217_ = lean_unbox(v___x_4213_);
v_res_4218_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_4208_, v_responseBodyInstance_4209_, v_handler_4210_, v_config_4211_, v___x_4212_, v___x_5208__boxed_4217_, v___f_4214_, v_x_4215_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_inst_4219_, lean_object* v_h_4220_, lean_object* v_responseBodyInstance_4221_, lean_object* v_config_4222_, lean_object* v_handler_4223_, uint8_t v___x_4224_, lean_object* v___f_4225_, lean_object* v_x_4226_){
_start:
{
if (lean_obj_tag(v_x_4226_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4236_; 
lean_dec_ref(v___f_4225_);
lean_dec(v_handler_4223_);
lean_dec_ref(v_config_4222_);
lean_dec_ref(v_responseBodyInstance_4221_);
lean_dec_ref(v_h_4220_);
lean_dec_ref(v_inst_4219_);
v_a_4228_ = lean_ctor_get(v_x_4226_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v_x_4226_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4230_ = v_x_4226_;
v_isShared_4231_ = v_isSharedCheck_4236_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v_x_4226_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4236_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
lean_object* v___x_4234_; 
v___x_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4233_);
return v___x_4234_;
}
}
}
else
{
lean_object* v_a_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v_a_4237_ = lean_ctor_get(v_x_4226_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v_x_4226_, 1);
v___x_4238_ = lean_unsigned_to_nat(0u);
v___x_4239_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_4219_, v_h_4220_, v_responseBodyInstance_4221_, v_config_4222_, v_handler_4223_, v_a_4237_);
v___x_4240_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4238_, v___x_4224_, v___x_4239_, v___f_4225_);
return v___x_4240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_inst_4241_, lean_object* v_h_4242_, lean_object* v_responseBodyInstance_4243_, lean_object* v_config_4244_, lean_object* v_handler_4245_, lean_object* v___x_4246_, lean_object* v___f_4247_, lean_object* v_x_4248_, lean_object* v___y_4249_){
_start:
{
uint8_t v___x_5249__boxed_4250_; lean_object* v_res_4251_; 
v___x_5249__boxed_4250_ = lean_unbox(v___x_4246_);
v_res_4251_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_inst_4241_, v_h_4242_, v_responseBodyInstance_4243_, v_config_4244_, v_handler_4245_, v___x_5249__boxed_4250_, v___f_4247_, v_x_4248_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(uint8_t v___x_4252_, lean_object* v_h_4253_, lean_object* v_responseBodyInstance_4254_, lean_object* v_handler_4255_, lean_object* v_config_4256_, lean_object* v___f_4257_, lean_object* v_inst_4258_, lean_object* v_socket_4259_, lean_object* v_connectionContext_4260_, lean_object* v_x_4261_){
_start:
{
if (lean_obj_tag(v_x_4261_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4271_; 
lean_dec_ref(v_connectionContext_4260_);
lean_dec(v_socket_4259_);
lean_dec_ref(v_inst_4258_);
lean_dec_ref(v___f_4257_);
lean_dec_ref(v_config_4256_);
lean_dec(v_handler_4255_);
lean_dec_ref(v_responseBodyInstance_4254_);
lean_dec_ref(v_h_4253_);
v_a_4263_ = lean_ctor_get(v_x_4261_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v_x_4261_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4265_ = v_x_4261_;
v_isShared_4266_ = v_isSharedCheck_4271_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v_x_4261_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4271_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
lean_object* v___x_4269_; 
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
return v___x_4269_;
}
}
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4306_; 
v_a_4272_ = lean_ctor_get(v_x_4261_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v_x_4261_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4274_ = v_x_4261_;
v_isShared_4275_ = v_isSharedCheck_4306_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v_x_4261_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4306_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v_machine_4282_; lean_object* v_requestStream_4283_; lean_object* v_keepAliveTimeout_4284_; lean_object* v_currentTimeout_4285_; lean_object* v_headerTimeout_4286_; lean_object* v_response_4287_; lean_object* v_respStream_4288_; uint8_t v_requiresData_4289_; lean_object* v_expectData_4290_; uint8_t v_handlerDispatched_4291_; lean_object* v_pendingHead_4292_; 
v_machine_4282_ = lean_ctor_get(v_a_4272_, 0);
v_requestStream_4283_ = lean_ctor_get(v_a_4272_, 1);
v_keepAliveTimeout_4284_ = lean_ctor_get(v_a_4272_, 2);
v_currentTimeout_4285_ = lean_ctor_get(v_a_4272_, 3);
v_headerTimeout_4286_ = lean_ctor_get(v_a_4272_, 4);
v_response_4287_ = lean_ctor_get(v_a_4272_, 5);
v_respStream_4288_ = lean_ctor_get(v_a_4272_, 6);
v_requiresData_4289_ = lean_ctor_get_uint8(v_a_4272_, sizeof(void*)*9);
v_expectData_4290_ = lean_ctor_get(v_a_4272_, 7);
v_handlerDispatched_4291_ = lean_ctor_get_uint8(v_a_4272_, sizeof(void*)*9 + 1);
v_pendingHead_4292_ = lean_ctor_get(v_a_4272_, 8);
if (v_requiresData_4289_ == 0)
{
if (v_handlerDispatched_4291_ == 0)
{
if (lean_obj_tag(v_respStream_4288_) == 0)
{
lean_object* v_writer_4302_; uint8_t v_sentMessage_4303_; 
v_writer_4302_ = lean_ctor_get(v_machine_4282_, 1);
v_sentMessage_4303_ = lean_ctor_get_uint8(v_writer_4302_, sizeof(void*)*6);
if (v_sentMessage_4303_ == 0)
{
lean_object* v_reader_4304_; lean_object* v_state_4305_; 
v_reader_4304_ = lean_ctor_get(v_machine_4282_, 0);
v_state_4305_ = lean_ctor_get(v_reader_4304_, 0);
if (lean_obj_tag(v_state_4305_) == 2)
{
lean_inc(v_respStream_4288_);
lean_inc(v_pendingHead_4292_);
lean_inc(v_expectData_4290_);
lean_inc_ref(v_response_4287_);
lean_inc(v_headerTimeout_4286_);
lean_inc(v_currentTimeout_4285_);
lean_inc(v_keepAliveTimeout_4284_);
lean_inc_ref(v_requestStream_4283_);
lean_inc_ref(v_machine_4282_);
lean_del_object(v___x_4274_);
lean_dec(v_a_4272_);
goto v___jp_4293_;
}
else
{
lean_dec_ref(v_connectionContext_4260_);
lean_dec(v_socket_4259_);
lean_dec_ref(v_inst_4258_);
lean_dec_ref(v___f_4257_);
lean_dec_ref(v_config_4256_);
lean_dec(v_handler_4255_);
lean_dec_ref(v_responseBodyInstance_4254_);
lean_dec_ref(v_h_4253_);
goto v___jp_4276_;
}
}
else
{
lean_dec_ref(v_connectionContext_4260_);
lean_dec(v_socket_4259_);
lean_dec_ref(v_inst_4258_);
lean_dec_ref(v___f_4257_);
lean_dec_ref(v_config_4256_);
lean_dec(v_handler_4255_);
lean_dec_ref(v_responseBodyInstance_4254_);
lean_dec_ref(v_h_4253_);
goto v___jp_4276_;
}
}
else
{
lean_inc_ref(v_respStream_4288_);
lean_inc(v_pendingHead_4292_);
lean_inc(v_expectData_4290_);
lean_inc_ref(v_response_4287_);
lean_inc(v_headerTimeout_4286_);
lean_inc(v_currentTimeout_4285_);
lean_inc(v_keepAliveTimeout_4284_);
lean_inc_ref(v_requestStream_4283_);
lean_inc_ref(v_machine_4282_);
lean_del_object(v___x_4274_);
lean_dec(v_a_4272_);
goto v___jp_4293_;
}
}
else
{
lean_inc(v_pendingHead_4292_);
lean_inc(v_expectData_4290_);
lean_inc(v_respStream_4288_);
lean_inc_ref(v_response_4287_);
lean_inc(v_headerTimeout_4286_);
lean_inc(v_currentTimeout_4285_);
lean_inc(v_keepAliveTimeout_4284_);
lean_inc_ref(v_requestStream_4283_);
lean_inc_ref(v_machine_4282_);
lean_del_object(v___x_4274_);
lean_dec(v_a_4272_);
goto v___jp_4293_;
}
}
else
{
lean_inc(v_pendingHead_4292_);
lean_inc(v_expectData_4290_);
lean_inc(v_respStream_4288_);
lean_inc_ref(v_response_4287_);
lean_inc(v_headerTimeout_4286_);
lean_inc(v_currentTimeout_4285_);
lean_inc(v_keepAliveTimeout_4284_);
lean_inc_ref(v_requestStream_4283_);
lean_inc_ref(v_machine_4282_);
lean_del_object(v___x_4274_);
lean_dec(v_a_4272_);
goto v___jp_4293_;
}
v___jp_4276_:
{
lean_object* v___x_4277_; lean_object* v___x_4279_; 
v___x_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4277_, 0, v_a_4272_);
if (v_isShared_4275_ == 0)
{
lean_ctor_set(v___x_4274_, 0, v___x_4277_);
v___x_4279_ = v___x_4274_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4277_);
v___x_4279_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
lean_object* v___x_4280_; 
v___x_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
return v___x_4280_;
}
}
v___jp_4293_:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___f_4296_; lean_object* v___x_4297_; lean_object* v___f_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4294_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4294_, 0, v_machine_4282_);
lean_ctor_set(v___x_4294_, 1, v_requestStream_4283_);
lean_ctor_set(v___x_4294_, 2, v_keepAliveTimeout_4284_);
lean_ctor_set(v___x_4294_, 3, v_currentTimeout_4285_);
lean_ctor_set(v___x_4294_, 4, v_headerTimeout_4286_);
lean_ctor_set(v___x_4294_, 5, v_response_4287_);
lean_ctor_set(v___x_4294_, 6, v_respStream_4288_);
lean_ctor_set(v___x_4294_, 7, v_expectData_4290_);
lean_ctor_set(v___x_4294_, 8, v_pendingHead_4292_);
lean_ctor_set_uint8(v___x_4294_, sizeof(void*)*9, v___x_4252_);
lean_ctor_set_uint8(v___x_4294_, sizeof(void*)*9 + 1, v_handlerDispatched_4291_);
v___x_4295_ = lean_box(v___x_4252_);
lean_inc_ref(v___x_4294_);
lean_inc_ref(v_config_4256_);
lean_inc(v_handler_4255_);
lean_inc_ref(v_responseBodyInstance_4254_);
lean_inc_ref(v_h_4253_);
v___f_4296_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 9, 7);
lean_closure_set(v___f_4296_, 0, v_h_4253_);
lean_closure_set(v___f_4296_, 1, v_responseBodyInstance_4254_);
lean_closure_set(v___f_4296_, 2, v_handler_4255_);
lean_closure_set(v___f_4296_, 3, v_config_4256_);
lean_closure_set(v___f_4296_, 4, v___x_4294_);
lean_closure_set(v___f_4296_, 5, v___x_4295_);
lean_closure_set(v___f_4296_, 6, v___f_4257_);
v___x_4297_ = lean_box(v___x_4252_);
v___f_4298_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 9, 7);
lean_closure_set(v___f_4298_, 0, v_inst_4258_);
lean_closure_set(v___f_4298_, 1, v_h_4253_);
lean_closure_set(v___f_4298_, 2, v_responseBodyInstance_4254_);
lean_closure_set(v___f_4298_, 3, v_config_4256_);
lean_closure_set(v___f_4298_, 4, v_handler_4255_);
lean_closure_set(v___f_4298_, 5, v___x_4297_);
lean_closure_set(v___f_4298_, 6, v___f_4296_);
v___x_4299_ = lean_unsigned_to_nat(0u);
v___x_4300_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4259_, v_connectionContext_4260_, v___x_4294_);
v___x_4301_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4299_, v___x_4252_, v___x_4300_, v___f_4298_);
return v___x_4301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v___x_4307_, lean_object* v_h_4308_, lean_object* v_responseBodyInstance_4309_, lean_object* v_handler_4310_, lean_object* v_config_4311_, lean_object* v___f_4312_, lean_object* v_inst_4313_, lean_object* v_socket_4314_, lean_object* v_connectionContext_4315_, lean_object* v_x_4316_, lean_object* v___y_4317_){
_start:
{
uint8_t v___x_5289__boxed_4318_; lean_object* v_res_4319_; 
v___x_5289__boxed_4318_ = lean_unbox(v___x_4307_);
v_res_4319_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v___x_5289__boxed_4318_, v_h_4308_, v_responseBodyInstance_4309_, v_handler_4310_, v_config_4311_, v___f_4312_, v_inst_4313_, v_socket_4314_, v_connectionContext_4315_, v_x_4316_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(lean_object* v_h_4320_, lean_object* v_handler_4321_, lean_object* v_extensions_4322_, lean_object* v_connectionContext_4323_, uint8_t v___x_4324_, lean_object* v___f_4325_, lean_object* v_x_4326_){
_start:
{
if (lean_obj_tag(v_x_4326_) == 0)
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4336_; 
lean_dec_ref(v___f_4325_);
lean_dec_ref(v_connectionContext_4323_);
lean_dec(v_extensions_4322_);
lean_dec(v_handler_4321_);
lean_dec_ref(v_h_4320_);
v_a_4328_ = lean_ctor_get(v_x_4326_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v_x_4326_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4330_ = v_x_4326_;
v_isShared_4331_ = v_isSharedCheck_4336_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v_x_4326_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4336_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
lean_object* v___x_4334_; 
v___x_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
return v___x_4334_;
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v_a_4337_ = lean_ctor_get(v_x_4326_, 0);
lean_inc(v_a_4337_);
lean_dec_ref_known(v_x_4326_, 1);
v___x_4338_ = lean_unsigned_to_nat(0u);
v___x_4339_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_4320_, v_handler_4321_, v_extensions_4322_, v_connectionContext_4323_, v_a_4337_);
v___x_4340_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4338_, v___x_4324_, v___x_4339_, v___f_4325_);
return v___x_4340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v_h_4341_, lean_object* v_handler_4342_, lean_object* v_extensions_4343_, lean_object* v_connectionContext_4344_, lean_object* v___x_4345_, lean_object* v___f_4346_, lean_object* v_x_4347_, lean_object* v___y_4348_){
_start:
{
uint8_t v___x_5364__boxed_4349_; lean_object* v_res_4350_; 
v___x_5364__boxed_4349_ = lean_unbox(v___x_4345_);
v_res_4350_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v_h_4341_, v_handler_4342_, v_extensions_4343_, v_connectionContext_4344_, v___x_5364__boxed_4349_, v___f_4346_, v_x_4347_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_4351_, lean_object* v_responseBodyInstance_4352_, lean_object* v_handler_4353_, lean_object* v_config_4354_, lean_object* v_connectionContext_4355_, lean_object* v_events_4356_, lean_object* v___x_4357_, uint8_t v___x_4358_, lean_object* v___f_4359_, lean_object* v_____r_4360_){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = lean_unsigned_to_nat(0u);
v___x_4363_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_4351_, v_responseBodyInstance_4352_, v_handler_4353_, v_config_4354_, v_connectionContext_4355_, v_events_4356_, v___x_4357_);
v___x_4364_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4362_, v___x_4358_, v___x_4363_, v___f_4359_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_4365_, lean_object* v_responseBodyInstance_4366_, lean_object* v_handler_4367_, lean_object* v_config_4368_, lean_object* v_connectionContext_4369_, lean_object* v_events_4370_, lean_object* v___x_4371_, lean_object* v___x_4372_, lean_object* v___f_4373_, lean_object* v_____r_4374_, lean_object* v___y_4375_){
_start:
{
uint8_t v___x_5403__boxed_4376_; lean_object* v_res_4377_; 
v___x_5403__boxed_4376_ = lean_unbox(v___x_4372_);
v_res_4377_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4365_, v_responseBodyInstance_4366_, v_handler_4367_, v_config_4368_, v_connectionContext_4369_, v_events_4370_, v___x_4371_, v___x_5403__boxed_4376_, v___f_4373_, v_____r_4374_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v___x_4378_, lean_object* v___f_4379_, lean_object* v_x_4380_){
_start:
{
if (lean_obj_tag(v_x_4380_) == 0)
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4390_; 
lean_dec_ref(v___f_4379_);
lean_dec_ref(v___x_4378_);
v_a_4382_ = lean_ctor_get(v_x_4380_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v_x_4380_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4384_ = v_x_4380_;
v_isShared_4385_ = v_isSharedCheck_4390_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v_x_4380_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4390_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
lean_object* v___x_4388_; 
v___x_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
return v___x_4388_;
}
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4402_; 
v_a_4391_ = lean_ctor_get(v_x_4380_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v_x_4380_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4393_ = v_x_4380_;
v_isShared_4394_ = v_isSharedCheck_4402_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v_x_4380_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4402_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
if (lean_obj_tag(v_a_4391_) == 0)
{
lean_object* v___x_4395_; lean_object* v___x_4397_; 
lean_dec_ref(v___f_4379_);
v___x_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4378_);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 0, v___x_4395_);
v___x_4397_ = v___x_4393_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4395_);
v___x_4397_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4398_; 
v___x_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4397_);
return v___x_4398_;
}
}
else
{
lean_object* v_val_4400_; lean_object* v___x_4401_; 
lean_del_object(v___x_4393_);
lean_dec_ref(v___x_4378_);
v_val_4400_ = lean_ctor_get(v_a_4391_, 0);
lean_inc(v_val_4400_);
lean_dec_ref_known(v_a_4391_, 1);
v___x_4401_ = lean_apply_2(v___f_4379_, v_val_4400_, lean_box(0));
return v___x_4401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v___x_4403_, lean_object* v___f_4404_, lean_object* v_x_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v___x_4403_, v___f_4404_, v_x_4405_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_h_4408_, lean_object* v_responseBodyInstance_4409_, lean_object* v_handler_4410_, lean_object* v_config_4411_, lean_object* v_connectionContext_4412_, uint8_t v___x_4413_, lean_object* v___f_4414_, lean_object* v_inst_4415_, lean_object* v_socket_4416_, lean_object* v___f_4417_, lean_object* v___f_4418_, lean_object* v_x_4419_, lean_object* v_____s_4420_){
_start:
{
lean_object* v_machine_4422_; lean_object* v_reader_4423_; lean_object* v_requestStream_4424_; lean_object* v_keepAliveTimeout_4425_; lean_object* v_currentTimeout_4426_; lean_object* v_headerTimeout_4427_; lean_object* v_response_4428_; lean_object* v_respStream_4429_; uint8_t v_requiresData_4430_; lean_object* v_expectData_4431_; uint8_t v_handlerDispatched_4432_; lean_object* v_pendingHead_4433_; lean_object* v_writer_4434_; lean_object* v_state_4435_; uint8_t v___x_4436_; 
v_machine_4422_ = lean_ctor_get(v_____s_4420_, 0);
v_reader_4423_ = lean_ctor_get(v_machine_4422_, 0);
v_requestStream_4424_ = lean_ctor_get(v_____s_4420_, 1);
v_keepAliveTimeout_4425_ = lean_ctor_get(v_____s_4420_, 2);
v_currentTimeout_4426_ = lean_ctor_get(v_____s_4420_, 3);
v_headerTimeout_4427_ = lean_ctor_get(v_____s_4420_, 4);
v_response_4428_ = lean_ctor_get(v_____s_4420_, 5);
v_respStream_4429_ = lean_ctor_get(v_____s_4420_, 6);
v_requiresData_4430_ = lean_ctor_get_uint8(v_____s_4420_, sizeof(void*)*9);
v_expectData_4431_ = lean_ctor_get(v_____s_4420_, 7);
v_handlerDispatched_4432_ = lean_ctor_get_uint8(v_____s_4420_, sizeof(void*)*9 + 1);
v_pendingHead_4433_ = lean_ctor_get(v_____s_4420_, 8);
v_writer_4434_ = lean_ctor_get(v_machine_4422_, 1);
v_state_4435_ = lean_ctor_get(v_reader_4423_, 0);
v___x_4436_ = 0;
if (lean_obj_tag(v_state_4435_) == 6)
{
lean_object* v_state_4458_; 
v_state_4458_ = lean_ctor_get(v_writer_4434_, 2);
if (lean_obj_tag(v_state_4458_) == 7)
{
lean_object* v_outputData_4459_; lean_object* v_size_4460_; lean_object* v___x_4461_; uint8_t v___x_4462_; 
v_outputData_4459_ = lean_ctor_get(v_writer_4434_, 1);
v_size_4460_ = lean_ctor_get(v_outputData_4459_, 1);
v___x_4461_ = lean_unsigned_to_nat(0u);
v___x_4462_ = lean_nat_dec_eq(v_size_4460_, v___x_4461_);
if (v___x_4462_ == 0)
{
lean_inc(v_pendingHead_4433_);
lean_inc(v_expectData_4431_);
lean_inc(v_respStream_4429_);
lean_inc_ref(v_response_4428_);
lean_inc(v_headerTimeout_4427_);
lean_inc(v_currentTimeout_4426_);
lean_inc(v_keepAliveTimeout_4425_);
lean_inc_ref(v_requestStream_4424_);
lean_inc_ref(v_machine_4422_);
lean_dec_ref(v_____s_4420_);
goto v___jp_4437_;
}
else
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
lean_dec_ref(v___f_4418_);
lean_dec_ref(v___f_4417_);
lean_dec(v_socket_4416_);
lean_dec_ref(v_inst_4415_);
lean_dec_ref(v___f_4414_);
lean_dec_ref(v_connectionContext_4412_);
lean_dec_ref(v_config_4411_);
lean_dec(v_handler_4410_);
lean_dec_ref(v_responseBodyInstance_4409_);
lean_dec_ref(v_h_4408_);
v___x_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4463_, 0, v_____s_4420_);
v___x_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4463_);
v___x_4465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4464_);
return v___x_4465_;
}
}
else
{
lean_inc(v_pendingHead_4433_);
lean_inc(v_expectData_4431_);
lean_inc(v_respStream_4429_);
lean_inc_ref(v_response_4428_);
lean_inc(v_headerTimeout_4427_);
lean_inc(v_currentTimeout_4426_);
lean_inc(v_keepAliveTimeout_4425_);
lean_inc_ref(v_requestStream_4424_);
lean_inc_ref(v_machine_4422_);
lean_dec_ref(v_____s_4420_);
goto v___jp_4437_;
}
}
else
{
lean_inc(v_pendingHead_4433_);
lean_inc(v_expectData_4431_);
lean_inc(v_respStream_4429_);
lean_inc_ref(v_response_4428_);
lean_inc(v_headerTimeout_4427_);
lean_inc(v_currentTimeout_4426_);
lean_inc(v_keepAliveTimeout_4425_);
lean_inc_ref(v_requestStream_4424_);
lean_inc_ref(v_machine_4422_);
lean_dec_ref(v_____s_4420_);
goto v___jp_4437_;
}
v___jp_4437_:
{
lean_object* v___x_4438_; lean_object* v_snd_4439_; lean_object* v_output_4440_; lean_object* v_fst_4441_; lean_object* v_events_4442_; lean_object* v_data_4443_; lean_object* v_size_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___f_4447_; lean_object* v___x_4448_; uint8_t v___x_4449_; 
v___x_4438_ = l_Std_Http_Protocol_H1_Machine_step(v___x_4436_, v_machine_4422_);
v_snd_4439_ = lean_ctor_get(v___x_4438_, 1);
lean_inc(v_snd_4439_);
v_output_4440_ = lean_ctor_get(v_snd_4439_, 1);
lean_inc_ref(v_output_4440_);
v_fst_4441_ = lean_ctor_get(v___x_4438_, 0);
lean_inc(v_fst_4441_);
lean_dec_ref(v___x_4438_);
v_events_4442_ = lean_ctor_get(v_snd_4439_, 0);
lean_inc_ref_n(v_events_4442_, 2);
lean_dec(v_snd_4439_);
v_data_4443_ = lean_ctor_get(v_output_4440_, 0);
lean_inc_ref(v_data_4443_);
v_size_4444_ = lean_ctor_get(v_output_4440_, 1);
lean_inc(v_size_4444_);
lean_dec_ref(v_output_4440_);
v___x_4445_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4445_, 0, v_fst_4441_);
lean_ctor_set(v___x_4445_, 1, v_requestStream_4424_);
lean_ctor_set(v___x_4445_, 2, v_keepAliveTimeout_4425_);
lean_ctor_set(v___x_4445_, 3, v_currentTimeout_4426_);
lean_ctor_set(v___x_4445_, 4, v_headerTimeout_4427_);
lean_ctor_set(v___x_4445_, 5, v_response_4428_);
lean_ctor_set(v___x_4445_, 6, v_respStream_4429_);
lean_ctor_set(v___x_4445_, 7, v_expectData_4431_);
lean_ctor_set(v___x_4445_, 8, v_pendingHead_4433_);
lean_ctor_set_uint8(v___x_4445_, sizeof(void*)*9, v_requiresData_4430_);
lean_ctor_set_uint8(v___x_4445_, sizeof(void*)*9 + 1, v_handlerDispatched_4432_);
v___x_4446_ = lean_box(v___x_4413_);
lean_inc_ref(v___f_4414_);
lean_inc_ref(v___x_4445_);
lean_inc_ref(v_connectionContext_4412_);
lean_inc_ref(v_config_4411_);
lean_inc(v_handler_4410_);
lean_inc_ref(v_responseBodyInstance_4409_);
lean_inc_ref(v_h_4408_);
v___f_4447_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_4447_, 0, v_h_4408_);
lean_closure_set(v___f_4447_, 1, v_responseBodyInstance_4409_);
lean_closure_set(v___f_4447_, 2, v_handler_4410_);
lean_closure_set(v___f_4447_, 3, v_config_4411_);
lean_closure_set(v___f_4447_, 4, v_connectionContext_4412_);
lean_closure_set(v___f_4447_, 5, v_events_4442_);
lean_closure_set(v___f_4447_, 6, v___x_4445_);
lean_closure_set(v___f_4447_, 7, v___x_4446_);
lean_closure_set(v___f_4447_, 8, v___f_4414_);
v___x_4448_ = lean_unsigned_to_nat(0u);
v___x_4449_ = lean_nat_dec_lt(v___x_4448_, v_size_4444_);
lean_dec(v_size_4444_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
lean_dec_ref(v___f_4447_);
lean_dec_ref(v_data_4443_);
lean_dec_ref(v___f_4418_);
lean_dec_ref(v___f_4417_);
lean_dec(v_socket_4416_);
lean_dec_ref(v_inst_4415_);
v___x_4450_ = lean_box(0);
v___x_4451_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_4408_, v_responseBodyInstance_4409_, v_handler_4410_, v_config_4411_, v_connectionContext_4412_, v_events_4442_, v___x_4445_, v___x_4413_, v___f_4414_, v___x_4450_);
return v___x_4451_;
}
else
{
lean_object* v_sendAll_4452_; lean_object* v___f_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
lean_dec_ref(v_events_4442_);
lean_dec_ref(v___f_4414_);
lean_dec_ref(v_connectionContext_4412_);
lean_dec_ref(v_config_4411_);
lean_dec(v_handler_4410_);
lean_dec_ref(v_responseBodyInstance_4409_);
lean_dec_ref(v_h_4408_);
v_sendAll_4452_ = lean_ctor_get(v_inst_4415_, 1);
lean_inc_ref(v_sendAll_4452_);
lean_dec_ref(v_inst_4415_);
v___f_4453_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 4, 2);
lean_closure_set(v___f_4453_, 0, v___x_4445_);
lean_closure_set(v___f_4453_, 1, v___f_4447_);
v___x_4454_ = lean_apply_3(v_sendAll_4452_, v_socket_4416_, v_data_4443_, lean_box(0));
v___x_4455_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4448_, v___x_4413_, v___x_4454_, v___f_4417_);
v___x_4456_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4448_, v___x_4413_, v___x_4455_, v___f_4418_);
v___x_4457_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4448_, v___x_4413_, v___x_4456_, v___f_4453_);
return v___x_4457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_h_4466_, lean_object* v_responseBodyInstance_4467_, lean_object* v_handler_4468_, lean_object* v_config_4469_, lean_object* v_connectionContext_4470_, lean_object* v___x_4471_, lean_object* v___f_4472_, lean_object* v_inst_4473_, lean_object* v_socket_4474_, lean_object* v___f_4475_, lean_object* v___f_4476_, lean_object* v_x_4477_, lean_object* v_____s_4478_, lean_object* v___y_4479_){
_start:
{
uint8_t v___x_5477__boxed_4480_; lean_object* v_res_4481_; 
v___x_5477__boxed_4480_ = lean_unbox(v___x_4471_);
v_res_4481_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_h_4466_, v_responseBodyInstance_4467_, v_handler_4468_, v_config_4469_, v_connectionContext_4470_, v___x_5477__boxed_4480_, v___f_4472_, v_inst_4473_, v_socket_4474_, v___f_4475_, v___f_4476_, v_x_4477_, v_____s_4478_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_a_4482_, lean_object* v_x_4483_){
_start:
{
if (lean_obj_tag(v_x_4483_) == 0)
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4493_; 
v_a_4485_ = lean_ctor_get(v_x_4483_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v_x_4483_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4487_ = v_x_4483_;
v_isShared_4488_ = v_isSharedCheck_4493_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v_x_4483_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4493_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
lean_object* v___x_4491_; 
v___x_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4490_);
return v___x_4491_;
}
}
}
else
{
lean_object* v___x_4494_; lean_object* v___x_4495_; 
lean_dec_ref_known(v_x_4483_, 1);
v___x_4494_ = l_IO_Promise_result_x21___redArg(v_a_4482_);
v___x_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
return v___x_4495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_a_4496_, lean_object* v_x_4497_, lean_object* v___y_4498_){
_start:
{
lean_object* v_res_4499_; 
v_res_4499_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_a_4496_, v_x_4497_);
lean_dec(v_a_4496_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v___f_4500_, lean_object* v___x_4501_, lean_object* v___x_4502_, uint8_t v___x_4503_, lean_object* v_x_4504_){
_start:
{
if (lean_obj_tag(v_x_4504_) == 0)
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4514_; 
lean_dec_ref(v___x_4502_);
lean_dec(v___x_4501_);
lean_dec_ref(v___f_4500_);
v_a_4506_ = lean_ctor_get(v_x_4504_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_x_4504_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4508_ = v_x_4504_;
v_isShared_4509_ = v_isSharedCheck_4514_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v_x_4504_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4514_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
lean_object* v___x_4512_; 
v___x_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4511_);
return v___x_4512_;
}
}
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4526_; 
v_a_4515_ = lean_ctor_get(v_x_4504_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v_x_4504_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4517_ = v_x_4504_;
v_isShared_4518_ = v_isSharedCheck_4526_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v_x_4504_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4526_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___f_4519_; lean_object* v___x_4520_; lean_object* v___x_4522_; 
lean_inc(v_a_4515_);
v___f_4519_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4519_, 0, v_a_4515_);
lean_inc(v___x_4501_);
v___x_4520_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_4500_, v___x_4501_, v_a_4515_, v___x_4502_);
if (v_isShared_4518_ == 0)
{
lean_ctor_set(v___x_4517_, 0, v___x_4520_);
v___x_4522_ = v___x_4517_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4520_);
v___x_4522_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
v___x_4524_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4501_, v___x_4503_, v___x_4523_, v___f_4519_);
return v___x_4524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v___f_4527_, lean_object* v___x_4528_, lean_object* v___x_4529_, lean_object* v___x_4530_, lean_object* v_x_4531_, lean_object* v___y_4532_){
_start:
{
uint8_t v___x_5580__boxed_4533_; lean_object* v_res_4534_; 
v___x_5580__boxed_4533_ = lean_unbox(v___x_4530_);
v_res_4534_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v___f_4527_, v___x_4528_, v___x_4529_, v___x_5580__boxed_4533_, v_x_4531_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v_config_4535_, lean_object* v_h_4536_, lean_object* v_responseBodyInstance_4537_, lean_object* v_handler_4538_, lean_object* v___f_4539_, lean_object* v_inst_4540_, lean_object* v_socket_4541_, lean_object* v_connectionContext_4542_, lean_object* v_extensions_4543_, lean_object* v___f_4544_, lean_object* v___f_4545_, lean_object* v_machine_4546_, lean_object* v_a_4547_, lean_object* v___x_4548_, lean_object* v___f_4549_, lean_object* v_x_4550_){
_start:
{
if (lean_obj_tag(v_x_4550_) == 0)
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4560_; 
lean_dec_ref(v___f_4549_);
lean_dec(v___x_4548_);
lean_dec_ref(v_a_4547_);
lean_dec_ref(v_machine_4546_);
lean_dec_ref(v___f_4545_);
lean_dec_ref(v___f_4544_);
lean_dec(v_extensions_4543_);
lean_dec_ref(v_connectionContext_4542_);
lean_dec(v_socket_4541_);
lean_dec_ref(v_inst_4540_);
lean_dec_ref(v___f_4539_);
lean_dec(v_handler_4538_);
lean_dec_ref(v_responseBodyInstance_4537_);
lean_dec_ref(v_h_4536_);
lean_dec_ref(v_config_4535_);
v_a_4552_ = lean_ctor_get(v_x_4550_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v_x_4550_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4554_ = v_x_4550_;
v_isShared_4555_ = v_isSharedCheck_4560_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v_x_4550_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4560_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4552_);
v___x_4557_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
lean_object* v___x_4558_; 
v___x_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4557_);
return v___x_4558_;
}
}
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4586_; 
v_a_4561_ = lean_ctor_get(v_x_4550_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v_x_4550_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4563_ = v_x_4550_;
v_isShared_4564_ = v_isSharedCheck_4586_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v_x_4550_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4586_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v_keepAliveTimeout_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; uint8_t v___x_4568_; lean_object* v___x_4569_; lean_object* v___f_4570_; lean_object* v___x_4571_; lean_object* v___f_4572_; lean_object* v___x_4573_; lean_object* v___f_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___f_4578_; lean_object* v___x_4579_; lean_object* v___x_4581_; 
v_keepAliveTimeout_4565_ = lean_ctor_get(v_config_4535_, 5);
lean_inc_n(v_keepAliveTimeout_4565_, 2);
v___x_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4566_, 0, v_keepAliveTimeout_4565_);
v___x_4567_ = lean_box(0);
v___x_4568_ = 0;
v___x_4569_ = lean_box(v___x_4568_);
lean_inc_ref_n(v_connectionContext_4542_, 2);
lean_inc(v_socket_4541_);
lean_inc_ref(v_inst_4540_);
lean_inc_ref(v_config_4535_);
lean_inc_n(v_handler_4538_, 2);
lean_inc_ref(v_responseBodyInstance_4537_);
lean_inc_ref_n(v_h_4536_, 2);
v___f_4570_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 11, 9);
lean_closure_set(v___f_4570_, 0, v___x_4569_);
lean_closure_set(v___f_4570_, 1, v_h_4536_);
lean_closure_set(v___f_4570_, 2, v_responseBodyInstance_4537_);
lean_closure_set(v___f_4570_, 3, v_handler_4538_);
lean_closure_set(v___f_4570_, 4, v_config_4535_);
lean_closure_set(v___f_4570_, 5, v___f_4539_);
lean_closure_set(v___f_4570_, 6, v_inst_4540_);
lean_closure_set(v___f_4570_, 7, v_socket_4541_);
lean_closure_set(v___f_4570_, 8, v_connectionContext_4542_);
v___x_4571_ = lean_box(v___x_4568_);
v___f_4572_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_4572_, 0, v_h_4536_);
lean_closure_set(v___f_4572_, 1, v_handler_4538_);
lean_closure_set(v___f_4572_, 2, v_extensions_4543_);
lean_closure_set(v___f_4572_, 3, v_connectionContext_4542_);
lean_closure_set(v___f_4572_, 4, v___x_4571_);
lean_closure_set(v___f_4572_, 5, v___f_4570_);
v___x_4573_ = lean_box(v___x_4568_);
v___f_4574_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 14, 11);
lean_closure_set(v___f_4574_, 0, v_h_4536_);
lean_closure_set(v___f_4574_, 1, v_responseBodyInstance_4537_);
lean_closure_set(v___f_4574_, 2, v_handler_4538_);
lean_closure_set(v___f_4574_, 3, v_config_4535_);
lean_closure_set(v___f_4574_, 4, v_connectionContext_4542_);
lean_closure_set(v___f_4574_, 5, v___x_4573_);
lean_closure_set(v___f_4574_, 6, v___f_4572_);
lean_closure_set(v___f_4574_, 7, v_inst_4540_);
lean_closure_set(v___f_4574_, 8, v_socket_4541_);
lean_closure_set(v___f_4574_, 9, v___f_4544_);
lean_closure_set(v___f_4574_, 10, v___f_4545_);
v___x_4575_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4575_, 0, v_machine_4546_);
lean_ctor_set(v___x_4575_, 1, v_a_4547_);
lean_ctor_set(v___x_4575_, 2, v___x_4566_);
lean_ctor_set(v___x_4575_, 3, v_keepAliveTimeout_4565_);
lean_ctor_set(v___x_4575_, 4, v___x_4567_);
lean_ctor_set(v___x_4575_, 5, v_a_4561_);
lean_ctor_set(v___x_4575_, 6, v___x_4567_);
lean_ctor_set(v___x_4575_, 7, v___x_4548_);
lean_ctor_set(v___x_4575_, 8, v___x_4567_);
lean_ctor_set_uint8(v___x_4575_, sizeof(void*)*9, v___x_4568_);
lean_ctor_set_uint8(v___x_4575_, sizeof(void*)*9 + 1, v___x_4568_);
v___x_4576_ = lean_unsigned_to_nat(0u);
v___x_4577_ = lean_box(v___x_4568_);
v___f_4578_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 6, 4);
lean_closure_set(v___f_4578_, 0, v___f_4574_);
lean_closure_set(v___f_4578_, 1, v___x_4576_);
lean_closure_set(v___f_4578_, 2, v___x_4575_);
lean_closure_set(v___f_4578_, 3, v___x_4577_);
v___x_4579_ = lean_io_promise_new();
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v___x_4579_);
v___x_4581_ = v___x_4563_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v___x_4579_);
v___x_4581_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
v___x_4583_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4576_, v___x_4568_, v___x_4582_, v___f_4578_);
v___x_4584_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4576_, v___x_4568_, v___x_4583_, v___f_4549_);
return v___x_4584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object** _args){
lean_object* v_config_4587_ = _args[0];
lean_object* v_h_4588_ = _args[1];
lean_object* v_responseBodyInstance_4589_ = _args[2];
lean_object* v_handler_4590_ = _args[3];
lean_object* v___f_4591_ = _args[4];
lean_object* v_inst_4592_ = _args[5];
lean_object* v_socket_4593_ = _args[6];
lean_object* v_connectionContext_4594_ = _args[7];
lean_object* v_extensions_4595_ = _args[8];
lean_object* v___f_4596_ = _args[9];
lean_object* v___f_4597_ = _args[10];
lean_object* v_machine_4598_ = _args[11];
lean_object* v_a_4599_ = _args[12];
lean_object* v___x_4600_ = _args[13];
lean_object* v___f_4601_ = _args[14];
lean_object* v_x_4602_ = _args[15];
lean_object* v___y_4603_ = _args[16];
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v_config_4587_, v_h_4588_, v_responseBodyInstance_4589_, v_handler_4590_, v___f_4591_, v_inst_4592_, v_socket_4593_, v_connectionContext_4594_, v_extensions_4595_, v___f_4596_, v___f_4597_, v_machine_4598_, v_a_4599_, v___x_4600_, v___f_4601_, v_x_4602_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_config_4605_, lean_object* v_h_4606_, lean_object* v_responseBodyInstance_4607_, lean_object* v_handler_4608_, lean_object* v___f_4609_, lean_object* v_inst_4610_, lean_object* v_socket_4611_, lean_object* v_connectionContext_4612_, lean_object* v_extensions_4613_, lean_object* v___f_4614_, lean_object* v___f_4615_, lean_object* v_machine_4616_, lean_object* v___f_4617_, lean_object* v_x_4618_){
_start:
{
if (lean_obj_tag(v_x_4618_) == 0)
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4628_; 
lean_dec_ref(v___f_4617_);
lean_dec_ref(v_machine_4616_);
lean_dec_ref(v___f_4615_);
lean_dec_ref(v___f_4614_);
lean_dec(v_extensions_4613_);
lean_dec_ref(v_connectionContext_4612_);
lean_dec(v_socket_4611_);
lean_dec_ref(v_inst_4610_);
lean_dec_ref(v___f_4609_);
lean_dec(v_handler_4608_);
lean_dec_ref(v_responseBodyInstance_4607_);
lean_dec_ref(v_h_4606_);
lean_dec_ref(v_config_4605_);
v_a_4620_ = lean_ctor_get(v_x_4618_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_x_4618_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4622_ = v_x_4618_;
v_isShared_4623_ = v_isSharedCheck_4628_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v_x_4618_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4628_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4620_);
v___x_4625_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
lean_object* v___x_4626_; 
v___x_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4625_);
return v___x_4626_;
}
}
}
else
{
lean_object* v_a_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4643_; 
v_a_4629_ = lean_ctor_get(v_x_4618_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v_x_4618_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4631_ = v_x_4618_;
v_isShared_4632_ = v_isSharedCheck_4643_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_a_4629_);
lean_dec(v_x_4618_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4643_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v___x_4633_; lean_object* v___f_4634_; lean_object* v___x_4635_; uint8_t v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4639_; 
v___x_4633_ = lean_box(0);
v___f_4634_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 17, 15);
lean_closure_set(v___f_4634_, 0, v_config_4605_);
lean_closure_set(v___f_4634_, 1, v_h_4606_);
lean_closure_set(v___f_4634_, 2, v_responseBodyInstance_4607_);
lean_closure_set(v___f_4634_, 3, v_handler_4608_);
lean_closure_set(v___f_4634_, 4, v___f_4609_);
lean_closure_set(v___f_4634_, 5, v_inst_4610_);
lean_closure_set(v___f_4634_, 6, v_socket_4611_);
lean_closure_set(v___f_4634_, 7, v_connectionContext_4612_);
lean_closure_set(v___f_4634_, 8, v_extensions_4613_);
lean_closure_set(v___f_4634_, 9, v___f_4614_);
lean_closure_set(v___f_4634_, 10, v___f_4615_);
lean_closure_set(v___f_4634_, 11, v_machine_4616_);
lean_closure_set(v___f_4634_, 12, v_a_4629_);
lean_closure_set(v___f_4634_, 13, v___x_4633_);
lean_closure_set(v___f_4634_, 14, v___f_4617_);
v___x_4635_ = lean_unsigned_to_nat(0u);
v___x_4636_ = 0;
v___x_4637_ = l_Std_CloseableChannel_new___redArg(v___x_4633_);
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 0, v___x_4637_);
v___x_4639_ = v___x_4631_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4637_);
v___x_4639_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; 
v___x_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
v___x_4641_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4635_, v___x_4636_, v___x_4640_, v___f_4634_);
return v___x_4641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_config_4644_, lean_object* v_h_4645_, lean_object* v_responseBodyInstance_4646_, lean_object* v_handler_4647_, lean_object* v___f_4648_, lean_object* v_inst_4649_, lean_object* v_socket_4650_, lean_object* v_connectionContext_4651_, lean_object* v_extensions_4652_, lean_object* v___f_4653_, lean_object* v___f_4654_, lean_object* v_machine_4655_, lean_object* v___f_4656_, lean_object* v_x_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_config_4644_, v_h_4645_, v_responseBodyInstance_4646_, v_handler_4647_, v___f_4648_, v_inst_4649_, v_socket_4650_, v_connectionContext_4651_, v_extensions_4652_, v___f_4653_, v___f_4654_, v_machine_4655_, v___f_4656_, v_x_4657_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_4663_, lean_object* v_h_4664_, lean_object* v_connection_4665_, lean_object* v_config_4666_, lean_object* v_connectionContext_4667_, lean_object* v_handler_4668_){
_start:
{
lean_object* v_responseBodyInstance_4670_; lean_object* v_onFailure_4671_; lean_object* v_socket_4672_; lean_object* v_machine_4673_; lean_object* v_extensions_4674_; lean_object* v___f_4675_; lean_object* v___f_4676_; lean_object* v___f_4677_; lean_object* v___f_4678_; lean_object* v___f_4679_; lean_object* v___f_4680_; lean_object* v___f_4681_; lean_object* v___f_4682_; lean_object* v___f_4683_; lean_object* v___x_4684_; uint8_t v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v_responseBodyInstance_4670_ = lean_ctor_get(v_h_4664_, 0);
lean_inc_ref_n(v_responseBodyInstance_4670_, 2);
v_onFailure_4671_ = lean_ctor_get(v_h_4664_, 2);
v_socket_4672_ = lean_ctor_get(v_connection_4665_, 0);
lean_inc_n(v_socket_4672_, 2);
v_machine_4673_ = lean_ctor_get(v_connection_4665_, 1);
lean_inc_ref(v_machine_4673_);
v_extensions_4674_ = lean_ctor_get(v_connection_4665_, 2);
lean_inc(v_extensions_4674_);
lean_dec_ref(v_connection_4665_);
v___f_4675_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___f_4676_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_4677_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
lean_inc(v_handler_4668_);
lean_inc_ref(v_onFailure_4671_);
v___f_4678_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4678_, 0, v_onFailure_4671_);
lean_closure_set(v___f_4678_, 1, v_handler_4668_);
lean_closure_set(v___f_4678_, 2, v___f_4677_);
v___f_4679_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
lean_inc_ref(v_inst_4663_);
v___f_4680_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4680_, 0, v_inst_4663_);
lean_closure_set(v___f_4680_, 1, v_socket_4672_);
lean_inc_ref(v___f_4680_);
v___f_4681_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4681_, 0, v___f_4680_);
v___f_4682_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_4682_, 0, v_responseBodyInstance_4670_);
lean_closure_set(v___f_4682_, 1, v___f_4681_);
lean_closure_set(v___f_4682_, 2, v___f_4680_);
lean_closure_set(v___f_4682_, 3, v___f_4675_);
v___f_4683_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 15, 13);
lean_closure_set(v___f_4683_, 0, v_config_4666_);
lean_closure_set(v___f_4683_, 1, v_h_4664_);
lean_closure_set(v___f_4683_, 2, v_responseBodyInstance_4670_);
lean_closure_set(v___f_4683_, 3, v_handler_4668_);
lean_closure_set(v___f_4683_, 4, v___f_4679_);
lean_closure_set(v___f_4683_, 5, v_inst_4663_);
lean_closure_set(v___f_4683_, 6, v_socket_4672_);
lean_closure_set(v___f_4683_, 7, v_connectionContext_4667_);
lean_closure_set(v___f_4683_, 8, v_extensions_4674_);
lean_closure_set(v___f_4683_, 9, v___f_4676_);
lean_closure_set(v___f_4683_, 10, v___f_4678_);
lean_closure_set(v___f_4683_, 11, v_machine_4673_);
lean_closure_set(v___f_4683_, 12, v___f_4682_);
v___x_4684_ = lean_unsigned_to_nat(0u);
v___x_4685_ = 0;
v___x_4686_ = l_Std_Http_Body_mkStream();
v___x_4687_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4684_, v___x_4685_, v___x_4686_, v___f_4683_);
return v___x_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_4688_, lean_object* v_h_4689_, lean_object* v_connection_4690_, lean_object* v_config_4691_, lean_object* v_connectionContext_4692_, lean_object* v_handler_4693_, lean_object* v_a_4694_){
_start:
{
lean_object* v_res_4695_; 
v_res_4695_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4688_, v_h_4689_, v_connection_4690_, v_config_4691_, v_connectionContext_4692_, v_handler_4693_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_4696_, lean_object* v_00_u03c3_4697_, lean_object* v_inst_4698_, lean_object* v_h_4699_, lean_object* v_connection_4700_, lean_object* v_config_4701_, lean_object* v_connectionContext_4702_, lean_object* v_handler_4703_){
_start:
{
lean_object* v___x_4705_; 
v___x_4705_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4698_, v_h_4699_, v_connection_4700_, v_config_4701_, v_connectionContext_4702_, v_handler_4703_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_4706_, lean_object* v_00_u03c3_4707_, lean_object* v_inst_4708_, lean_object* v_h_4709_, lean_object* v_connection_4710_, lean_object* v_config_4711_, lean_object* v_connectionContext_4712_, lean_object* v_handler_4713_, lean_object* v_a_4714_){
_start:
{
lean_object* v_res_4715_; 
v_res_4715_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_4706_, v_00_u03c3_4707_, v_inst_4708_, v_h_4709_, v_connection_4710_, v_config_4711_, v_connectionContext_4712_, v_handler_4713_);
return v_res_4715_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_4716_; lean_object* v___x_4717_; 
v___x_4716_ = 0;
v___x_4717_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4716_);
return v___x_4717_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4718_ = lean_unsigned_to_nat(4096u);
v___x_4719_ = lean_mk_empty_byte_array(v___x_4718_);
return v___x_4719_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4720_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_4721_ = l_ByteArray_mkIterator(v___x_4720_);
return v___x_4721_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4722_ = 0;
v___x_4723_ = lean_unsigned_to_nat(0u);
v___x_4724_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_4725_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_4726_ = lean_box(0);
v___x_4727_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_4727_, 0, v___x_4726_);
lean_ctor_set(v___x_4727_, 1, v___x_4725_);
lean_ctor_set(v___x_4727_, 2, v___x_4724_);
lean_ctor_set(v___x_4727_, 3, v___x_4723_);
lean_ctor_set(v___x_4727_, 4, v___x_4723_);
lean_ctor_set(v___x_4727_, 5, v___x_4723_);
lean_ctor_set_uint8(v___x_4727_, sizeof(void*)*6, v___x_4722_);
return v___x_4727_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_4735_; lean_object* v___x_4736_; 
v___x_4735_ = 1;
v___x_4736_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_4735_);
return v___x_4736_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4737_; uint8_t v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4737_ = lean_unsigned_to_nat(0u);
v___x_4738_ = 0;
v___x_4739_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_4740_ = lean_box(0);
v___x_4741_ = lean_box(0);
v___x_4742_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_4743_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_4744_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
lean_ctor_set(v___x_4744_, 1, v___x_4742_);
lean_ctor_set(v___x_4744_, 2, v___x_4741_);
lean_ctor_set(v___x_4744_, 3, v___x_4740_);
lean_ctor_set(v___x_4744_, 4, v___x_4739_);
lean_ctor_set(v___x_4744_, 5, v___x_4737_);
lean_ctor_set_uint8(v___x_4744_, sizeof(void*)*6, v___x_4738_);
lean_ctor_set_uint8(v___x_4744_, sizeof(void*)*6 + 1, v___x_4738_);
lean_ctor_set_uint8(v___x_4744_, sizeof(void*)*6 + 2, v___x_4738_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_4745_, lean_object* v_client_4746_, lean_object* v_extensions_4747_, lean_object* v_inst_4748_, lean_object* v_inst_4749_, lean_object* v_handler_4750_, lean_object* v_x_4751_){
_start:
{
if (lean_obj_tag(v_x_4751_) == 0)
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4761_; 
lean_dec(v_handler_4750_);
lean_dec_ref(v_inst_4749_);
lean_dec_ref(v_inst_4748_);
lean_dec(v_extensions_4747_);
lean_dec(v_client_4746_);
lean_dec_ref(v_config_4745_);
v_a_4753_ = lean_ctor_get(v_x_4751_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v_x_4751_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4755_ = v_x_4751_;
v_isShared_4756_ = v_isSharedCheck_4761_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v_x_4751_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4761_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
lean_object* v___x_4759_; 
v___x_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4759_, 0, v___x_4758_);
return v___x_4759_;
}
}
}
else
{
lean_object* v_a_4762_; uint8_t v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; uint8_t v_enableKeepAlive_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v_a_4762_ = lean_ctor_get(v_x_4751_, 0);
lean_inc(v_a_4762_);
lean_dec_ref_known(v_x_4751_, 1);
v___x_4763_ = 0;
v___x_4764_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_4765_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_4766_ = lean_box(0);
v___x_4767_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_4768_ = l_Std_Http_Config_toH1Config(v_config_4745_);
v_enableKeepAlive_4769_ = lean_ctor_get_uint8(v___x_4768_, sizeof(void*)*18);
v___x_4770_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_4770_, 0, v___x_4764_);
lean_ctor_set(v___x_4770_, 1, v___x_4767_);
lean_ctor_set(v___x_4770_, 2, v___x_4768_);
lean_ctor_set(v___x_4770_, 3, v___x_4765_);
lean_ctor_set(v___x_4770_, 4, v___x_4766_);
lean_ctor_set(v___x_4770_, 5, v___x_4766_);
lean_ctor_set_uint8(v___x_4770_, sizeof(void*)*6, v_enableKeepAlive_4769_);
lean_ctor_set_uint8(v___x_4770_, sizeof(void*)*6 + 1, v___x_4763_);
lean_ctor_set_uint8(v___x_4770_, sizeof(void*)*6 + 2, v___x_4763_);
v___x_4771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4771_, 0, v_client_4746_);
lean_ctor_set(v___x_4771_, 1, v___x_4770_);
lean_ctor_set(v___x_4771_, 2, v_extensions_4747_);
v___x_4772_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_4748_, v_inst_4749_, v___x_4771_, v_config_4745_, v_a_4762_, v_handler_4750_);
return v___x_4772_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_4773_, lean_object* v_client_4774_, lean_object* v_extensions_4775_, lean_object* v_inst_4776_, lean_object* v_inst_4777_, lean_object* v_handler_4778_, lean_object* v_x_4779_, lean_object* v___y_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_4773_, v_client_4774_, v_extensions_4775_, v_inst_4776_, v_inst_4777_, v_handler_4778_, v_x_4779_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_4782_, lean_object* v_inst_4783_, lean_object* v_client_4784_, lean_object* v_handler_4785_, lean_object* v_config_4786_, lean_object* v_extensions_4787_, lean_object* v_a_4788_){
_start:
{
lean_object* v___f_4790_; lean_object* v___x_4791_; uint8_t v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___f_4790_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_4790_, 0, v_config_4786_);
lean_closure_set(v___f_4790_, 1, v_client_4784_);
lean_closure_set(v___f_4790_, 2, v_extensions_4787_);
lean_closure_set(v___f_4790_, 3, v_inst_4782_);
lean_closure_set(v___f_4790_, 4, v_inst_4783_);
lean_closure_set(v___f_4790_, 5, v_handler_4785_);
v___x_4791_ = lean_unsigned_to_nat(0u);
v___x_4792_ = 0;
lean_inc_ref(v_a_4788_);
v___x_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4793_, 0, v_a_4788_);
v___x_4794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4793_);
v___x_4795_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4791_, v___x_4792_, v___x_4794_, v___f_4790_);
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_4796_, lean_object* v_inst_4797_, lean_object* v_client_4798_, lean_object* v_handler_4799_, lean_object* v_config_4800_, lean_object* v_extensions_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_){
_start:
{
lean_object* v_res_4804_; 
v_res_4804_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4796_, v_inst_4797_, v_client_4798_, v_handler_4799_, v_config_4800_, v_extensions_4801_, v_a_4802_);
lean_dec_ref(v_a_4802_);
return v_res_4804_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_4805_, lean_object* v_00_u03c3_4806_, lean_object* v_inst_4807_, lean_object* v_inst_4808_, lean_object* v_client_4809_, lean_object* v_handler_4810_, lean_object* v_config_4811_, lean_object* v_extensions_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v___x_4815_; 
v___x_4815_ = l_Std_Http_Server_serveConnection___redArg(v_inst_4807_, v_inst_4808_, v_client_4809_, v_handler_4810_, v_config_4811_, v_extensions_4812_, v_a_4813_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_4816_, lean_object* v_00_u03c3_4817_, lean_object* v_inst_4818_, lean_object* v_inst_4819_, lean_object* v_client_4820_, lean_object* v_handler_4821_, lean_object* v_config_4822_, lean_object* v_extensions_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_){
_start:
{
lean_object* v_res_4826_; 
v_res_4826_ = l_Std_Http_Server_serveConnection(v_t_4816_, v_00_u03c3_4817_, v_inst_4818_, v_inst_4819_, v_client_4820_, v_handler_4821_, v_config_4822_, v_extensions_4823_, v_a_4824_);
lean_dec_ref(v_a_4824_);
return v_res_4826_;
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
