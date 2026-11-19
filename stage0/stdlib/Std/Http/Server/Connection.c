// Lean compiler output
// Module: Std.Http.Server.Connection
// Imports: public import Std.Async.TCP public import Std.Async.ContextAsync public import Std.Http.Transport public import Std.Http.Transport.Outbox public import Std.Http.Protocol.H1 public import Std.Http.Server.Config public import Std.Http.Server.Handler
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
lean_object* l_Std_Http_Protocol_H1_Message_Head_getSize(uint8_t, lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonad___redArg();
lean_object* l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
lean_object* l_Std_Async_BaseAsync_lift___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Std_Http_Body_instBEqLength_beq(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Stream_closeWithError(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Stream_close(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Std_CloseableChannel_new___redArg(lean_object*);
lean_object* l_Std_Http_Body_mkStream();
lean_object* l_Std_Http_Protocol_H1_Machine_canContinue(uint8_t, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
lean_object* l_Std_Channel_recvSelector___redArg(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
lean_object* l_Std_Async_Selector_sleep(lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ByteArray_mkIterator(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_get_current_time();
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
lean_object* l_Std_Http_Body_Stream_offer(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Std_Http_Protocol_H1_Machine_closeWithError(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentLength;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(uint8_t, lean_object*, lean_object*);
uint8_t l_Std_Http_instBEqMethod_beq(uint8_t, uint8_t);
uint16_t l_Std_Http_Status_toCode(lean_object*);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_rejectOutgoingFraming(uint8_t, lean_object*);
uint8_t l_Std_Http_instBEqStatus_beq(lean_object*, lean_object*);
uint8_t l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_unframeableForHttp10(uint8_t, lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* l_Std_Http_Protocol_H1_instEncodeV11Head(uint8_t);
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object*, lean_object*);
uint8_t l_Std_Http_Protocol_H1_Message_Head_version(uint8_t, lean_object*);
uint8_t l_Std_Http_instBEqVersion_beq(uint8_t, uint8_t);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_DateTime_toHTTPDateString(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_Std_Http_Protocol_H1_Machine_step(uint8_t, lean_object*);
lean_object* l_Std_Http_Internal_Outbox_takeError_x3f___redArg(lean_object*);
lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Http_Internal_Outbox_idleFor_x3f___redArg(lean_object*);
extern lean_object* l_instInhabitedError;
lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_Functor_discard(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Channel_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg(lean_object*);
lean_object* l_Std_Http_Internal_Outbox_push___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_Internal_Outbox_failed___redArg(lean_object*);
lean_object* l_Std_Async_Async_ofTask___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Http_Config_toH1Config(lean_object*);
uint8_t l_Std_Http_Method_isSafe(uint8_t);
lean_object* l_Std_Http_Internal_Outbox_new___redArg(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_keepAliveTimeout_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_keepAliveTimeout_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_keepAlive_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_keepAlive_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_header_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_header_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_request_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_request_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
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
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_idle_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_idle_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_running_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_running_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandoned_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandoned_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_task_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_task_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "UTC"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__1_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__2_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__1(lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5___boxed, .m_arity = 5, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__1_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "the request body is incomplete: "};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_lift___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__2_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__2_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__4_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__6 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__6_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Invalid status line"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__7 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__7_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Invalid header"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__8 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__8_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Timeout"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__9 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__9_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Entity too large"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__10 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__10_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "URI too long"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__11 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__11_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unsupported version"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__12 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__12_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Unsupported transfer coding"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__13 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__13_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unsupported method"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__14 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__14_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Invalid chunk"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__15 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__15_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Connection closed"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__16 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__16_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Bad message"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__17 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__17_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Too many headers"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__18 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__18_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Headers too large"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__19 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__19_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Other error: "};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__20 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__20_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "the request body was discarded after the response was written"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__21 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__21_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "the handler returned the interim status "};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___closed__0_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " as its final response"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(uint16_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "request header timeout"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__1_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__2_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__2_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger(lean_object*, lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "the connection closed before the request body was complete"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__26(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__27___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_keepAliveTimeout_elim___redArg(lean_object* v_t_120_, lean_object* v_keepAliveTimeout_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_120_, v_keepAliveTimeout_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_keepAliveTimeout_elim(lean_object* v_00_u03b2_123_, lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_keepAliveTimeout_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_125_, v_keepAliveTimeout_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim___redArg(lean_object* v_t_129_, lean_object* v_shutdown_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_129_, v_shutdown_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim(lean_object* v_00_u03b2_132_, lean_object* v_motive_133_, lean_object* v_t_134_, lean_object* v_h_135_, lean_object* v_shutdown_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_134_, v_shutdown_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim___redArg(lean_object* v_t_138_, lean_object* v_close_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_138_, v_close_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim(lean_object* v_00_u03b2_141_, lean_object* v_motive_142_, lean_object* v_t_143_, lean_object* v_h_144_, lean_object* v_close_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_143_, v_close_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorIdx___impl(lean_object* v_x_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_obj_tag_nat(v_x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorIdx___impl___boxed(lean_object* v_x_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorIdx___impl(v_x_149_);
lean_dec_ref(v_x_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(lean_object* v_t_151_, lean_object* v_k_152_){
_start:
{
if (lean_obj_tag(v_t_151_) == 1)
{
lean_object* v_deadline_153_; lean_object* v___x_154_; 
v_deadline_153_ = lean_ctor_get(v_t_151_, 0);
lean_inc_ref(v_deadline_153_);
lean_dec_ref_known(v_t_151_, 1);
v___x_154_ = lean_apply_1(v_k_152_, v_deadline_153_);
return v___x_154_;
}
else
{
lean_object* v_remaining_155_; lean_object* v___x_156_; 
v_remaining_155_ = lean_ctor_get(v_t_151_, 0);
lean_inc(v_remaining_155_);
lean_dec_ref(v_t_151_);
v___x_156_ = lean_apply_1(v_k_152_, v_remaining_155_);
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim(lean_object* v_motive_157_, lean_object* v_ctorIdx_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_k_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_159_, v_k_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___boxed(lean_object* v_motive_163_, lean_object* v_ctorIdx_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_k_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim(v_motive_163_, v_ctorIdx_164_, v_t_165_, v_h_166_, v_k_167_);
lean_dec(v_ctorIdx_164_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_keepAlive_elim___redArg(lean_object* v_t_169_, lean_object* v_keepAlive_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_169_, v_keepAlive_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_keepAlive_elim(lean_object* v_motive_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_keepAlive_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_173_, v_keepAlive_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_header_elim___redArg(lean_object* v_t_177_, lean_object* v_header_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_177_, v_header_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_header_elim(lean_object* v_motive_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_header_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_181_, v_header_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_request_elim___redArg(lean_object* v_t_185_, lean_object* v_request_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_185_, v_request_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_request_elim(lean_object* v_motive_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_request_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_189_, v_request_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0(lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
lean_object* v___x_199_; 
lean_dec_ref_known(v_x_197_, 1);
v___x_199_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_199_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v_x_197_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___boxed(lean_object* v_x_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0(v_x_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(lean_object* v_inst_205_, lean_object* v_handler_206_, lean_object* v_error_207_){
_start:
{
lean_object* v_onFailure_209_; lean_object* v___f_210_; lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_onFailure_209_ = lean_ctor_get(v_inst_205_, 2);
lean_inc_ref(v_onFailure_209_);
lean_dec_ref(v_inst_205_);
v___f_210_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___closed__0));
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = 0;
v___x_213_ = lean_apply_3(v_onFailure_209_, v_handler_206_, v_error_207_, lean_box(0));
v___x_214_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_211_, v___x_212_, v___x_213_, v___f_210_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___boxed(lean_object* v_inst_215_, lean_object* v_handler_216_, lean_object* v_error_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_215_, v_handler_216_, v_error_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure(lean_object* v_00_u03c3_220_, lean_object* v_inst_221_, lean_object* v_handler_222_, lean_object* v_error_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_221_, v_handler_222_, v_error_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___boxed(lean_object* v_00_u03c3_226_, lean_object* v_inst_227_, lean_object* v_handler_228_, lean_object* v_error_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure(v_00_u03c3_226_, v_inst_227_, v_handler_228_, v_error_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(lean_object* v_x_232_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v_x_232_);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed(lean_object* v_x_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(v_x_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_254_; 
v_a_246_ = lean_ctor_get(v_x_244_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_x_244_);
if (v_isSharedCheck_254_ == 0)
{
v___x_248_ = v_x_244_;
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v_x_244_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_253_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; 
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
}
else
{
lean_object* v___x_255_; 
lean_dec_ref_known(v_x_244_, 1);
v___x_255_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1));
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed(lean_object* v_x_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(v_x_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(lean_object* v_inst_259_, lean_object* v_handler_260_, lean_object* v___f_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_a_264_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v_x_262_, 1);
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = 0;
v___x_267_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_259_, v_handler_260_, v_a_264_);
v___x_268_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_265_, v___x_266_, v___x_267_, v___f_261_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; 
lean_dec_ref(v___f_261_);
lean_dec(v_handler_260_);
lean_dec_ref(v_inst_259_);
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v_x_262_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed(lean_object* v_inst_270_, lean_object* v_handler_271_, lean_object* v___f_272_, lean_object* v_x_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(v_inst_270_, v_handler_271_, v___f_272_, v_x_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(lean_object* v_x_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_278_, 0, v_x_276_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed(lean_object* v_x_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(v_x_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(uint8_t v_x_284_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_286_, 0, v_x_284_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed(lean_object* v_x_289_, lean_object* v___y_290_){
_start:
{
uint8_t v_x_3201__boxed_291_; lean_object* v_res_292_; 
v_x_3201__boxed_291_ = lean_unbox(v_x_289_);
v_res_292_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(v_x_3201__boxed_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(lean_object* v_x_293_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_x_293_);
v___x_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed(lean_object* v_x_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(v_x_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object* v_x_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__1));
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object* v_x_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(v_x_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object* v_x_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__1));
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object* v_x_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(v_x_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object* v_x_325_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_337_; 
v_a_329_ = lean_ctor_get(v_x_325_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_325_);
if (v_isSharedCheck_337_ == 0)
{
v___x_331_ = v_x_325_;
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v_x_325_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_337_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_336_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
}
else
{
lean_object* v_a_338_; 
v_a_338_ = lean_ctor_get(v_x_325_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v_x_325_, 1);
if (lean_obj_tag(v_a_338_) == 1)
{
lean_object* v_val_339_; 
v_val_339_ = lean_ctor_get(v_a_338_, 0);
lean_inc(v_val_339_);
lean_dec_ref_known(v_a_338_, 1);
if (lean_obj_tag(v_val_339_) == 0)
{
lean_object* v___x_340_; 
v___x_340_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__1));
return v___x_340_;
}
else
{
lean_dec(v_val_339_);
goto v___jp_327_;
}
}
else
{
lean_dec(v_a_338_);
goto v___jp_327_;
}
}
v___jp_327_:
{
lean_object* v___x_328_; 
v___x_328_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___closed__1));
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object* v_x_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v_x_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object* v___f_344_, lean_object* v_response_345_, lean_object* v___x_346_, lean_object* v___f_347_, lean_object* v_requestBody_348_, lean_object* v___f_349_, lean_object* v_responseBody_350_, lean_object* v_inst_351_, lean_object* v___f_352_, lean_object* v_____r_353_, lean_object* v_selectables_354_){
_start:
{
lean_object* v_selectables_357_; lean_object* v_selectables_363_; lean_object* v_selectables_369_; 
if (lean_obj_tag(v_responseBody_350_) == 1)
{
lean_object* v_val_374_; lean_object* v_recvSelector_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_selectables_378_; 
v_val_374_ = lean_ctor_get(v_responseBody_350_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v_responseBody_350_, 1);
v_recvSelector_375_ = lean_ctor_get(v_inst_351_, 3);
lean_inc_ref(v_recvSelector_375_);
lean_dec_ref(v_inst_351_);
v___x_376_ = lean_apply_1(v_recvSelector_375_, v_val_374_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___f_352_);
v_selectables_378_ = lean_array_push(v_selectables_354_, v___x_377_);
v_selectables_369_ = v_selectables_378_;
goto v___jp_368_;
}
else
{
lean_dec_ref(v___f_352_);
lean_dec_ref(v_inst_351_);
lean_dec(v_responseBody_350_);
v_selectables_369_ = v_selectables_354_;
goto v___jp_368_;
}
v___jp_356_:
{
lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = 0;
v___x_360_ = l_Std_Async_Selectable_one___redArg(v_selectables_357_);
v___x_361_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_358_, v___x_359_, v___x_360_, v___f_344_);
return v___x_361_;
}
v___jp_362_:
{
if (lean_obj_tag(v_response_345_) == 1)
{
lean_object* v_val_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_selectables_367_; 
v_val_364_ = lean_ctor_get(v_response_345_, 0);
lean_inc(v_val_364_);
lean_dec_ref_known(v_response_345_, 1);
v___x_365_ = l_Std_Channel_recvSelector___redArg(v___x_346_, v_val_364_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___f_347_);
v_selectables_367_ = lean_array_push(v_selectables_363_, v___x_366_);
v_selectables_357_ = v_selectables_367_;
goto v___jp_356_;
}
else
{
lean_dec_ref(v___f_347_);
lean_dec_ref(v___x_346_);
lean_dec(v_response_345_);
v_selectables_357_ = v_selectables_363_;
goto v___jp_356_;
}
}
v___jp_368_:
{
if (lean_obj_tag(v_requestBody_348_) == 1)
{
lean_object* v_val_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_selectables_373_; 
v_val_370_ = lean_ctor_get(v_requestBody_348_, 0);
lean_inc(v_val_370_);
lean_dec_ref_known(v_requestBody_348_, 1);
v___x_371_ = l_Std_Http_Body_Stream_interestSelector(v_val_370_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___f_349_);
v_selectables_373_ = lean_array_push(v_selectables_369_, v___x_372_);
v_selectables_363_ = v_selectables_373_;
goto v___jp_362_;
}
else
{
lean_dec_ref(v___f_349_);
lean_dec(v_requestBody_348_);
v_selectables_363_ = v_selectables_369_;
goto v___jp_362_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object* v___f_379_, lean_object* v_response_380_, lean_object* v___x_381_, lean_object* v___f_382_, lean_object* v_requestBody_383_, lean_object* v___f_384_, lean_object* v_responseBody_385_, lean_object* v_inst_386_, lean_object* v___f_387_, lean_object* v_____r_388_, lean_object* v_selectables_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_379_, v_response_380_, v___x_381_, v___f_382_, v_requestBody_383_, v___f_384_, v_responseBody_385_, v_inst_386_, v___f_387_, v_____r_388_, v_selectables_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object* v___f_392_, lean_object* v_selectables_393_, lean_object* v___f_394_, lean_object* v_x_395_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref(v___f_394_);
lean_dec_ref(v_selectables_393_);
lean_dec_ref(v___f_392_);
v_a_397_ = lean_ctor_get(v_x_395_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v_x_395_);
if (v_isSharedCheck_405_ == 0)
{
v___x_399_ = v_x_395_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v_x_395_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_404_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; 
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_a_406_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v_x_395_, 1);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v_a_406_);
lean_ctor_set(v___x_407_, 1, v___f_392_);
v___x_408_ = lean_array_push(v_selectables_393_, v___x_407_);
v___x_409_ = lean_box(0);
v___x_410_ = lean_apply_3(v___f_394_, v___x_409_, v___x_408_, lean_box(0));
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object* v___f_411_, lean_object* v_selectables_412_, lean_object* v___f_413_, lean_object* v_x_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(v___f_411_, v_selectables_412_, v___f_413_, v_x_414_);
return v_res_416_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_unsigned_to_nat(1000000000u);
v___x_418_ = lean_nat_to_int(v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_unsigned_to_nat(1000u);
v___x_420_ = lean_nat_to_int(v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(1000000u);
v___x_422_ = lean_nat_to_int(v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(lean_object* v_deadline_423_, lean_object* v___f_424_, lean_object* v_x_425_){
_start:
{
if (lean_obj_tag(v_x_425_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v___f_424_);
v_a_427_ = lean_ctor_get(v_x_425_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_x_425_);
if (v_isSharedCheck_435_ == 0)
{
v___x_429_ = v_x_425_;
v_isShared_430_ = v_isSharedCheck_435_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v_x_425_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_435_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_434_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; 
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
}
else
{
lean_object* v_a_436_; lean_object* v_second_437_; lean_object* v_nano_438_; lean_object* v_second_439_; lean_object* v_nano_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_nanos_445_; lean_object* v___x_446_; lean_object* v_nanos_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v_second_450_; lean_object* v_nano_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v_millis_456_; lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_a_436_ = lean_ctor_get(v_x_425_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v_x_425_, 1);
v_second_437_ = lean_ctor_get(v_a_436_, 0);
lean_inc(v_second_437_);
v_nano_438_ = lean_ctor_get(v_a_436_, 1);
lean_inc(v_nano_438_);
lean_dec(v_a_436_);
v_second_439_ = lean_ctor_get(v_deadline_423_, 0);
v_nano_440_ = lean_ctor_get(v_deadline_423_, 1);
v___x_441_ = lean_int_neg(v_second_437_);
lean_dec(v_second_437_);
v___x_442_ = lean_int_neg(v_nano_438_);
lean_dec(v_nano_438_);
v___x_443_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_444_ = lean_int_mul(v_second_439_, v___x_443_);
v_nanos_445_ = lean_int_add(v___x_444_, v_nano_440_);
lean_dec(v___x_444_);
v___x_446_ = lean_int_mul(v___x_441_, v___x_443_);
lean_dec(v___x_441_);
v_nanos_447_ = lean_int_add(v___x_446_, v___x_442_);
lean_dec(v___x_442_);
lean_dec(v___x_446_);
v___x_448_ = lean_int_add(v_nanos_445_, v_nanos_447_);
lean_dec(v_nanos_447_);
lean_dec(v_nanos_445_);
v___x_449_ = l_Std_Time_Duration_ofNanoseconds(v___x_448_);
lean_dec(v___x_448_);
v_second_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_second_450_);
v_nano_451_ = lean_ctor_get(v___x_449_, 1);
lean_inc(v_nano_451_);
lean_dec_ref(v___x_449_);
v___x_452_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__1);
v___x_453_ = lean_int_mul(v_second_450_, v___x_452_);
lean_dec(v_second_450_);
v___x_454_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_455_ = lean_int_ediv(v_nano_451_, v___x_454_);
lean_dec(v_nano_451_);
v_millis_456_ = lean_int_add(v___x_453_, v___x_455_);
lean_dec(v___x_455_);
lean_dec(v___x_453_);
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = 0;
v___x_459_ = l_Std_Async_Selector_sleep(v_millis_456_);
lean_dec(v_millis_456_);
v___x_460_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_457_, v___x_458_, v___x_459_, v___f_424_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___boxed(lean_object* v_deadline_461_, lean_object* v___f_462_, lean_object* v_x_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12(v_deadline_461_, v___f_462_, v_x_463_);
lean_dec_ref(v_deadline_461_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__13(lean_object* v_token_466_, lean_object* v___f_467_, lean_object* v_x_468_){
_start:
{
lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = 0;
v___x_472_ = l_Std_CancellationToken_getCancellationReason(v_token_466_);
v___x_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
v___x_475_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_470_, v___x_471_, v___x_474_, v___f_467_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__13___boxed(lean_object* v_token_476_, lean_object* v___f_477_, lean_object* v_x_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__13(v_token_476_, v___f_477_, v_x_478_);
return v_res_480_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = l_instInhabitedError;
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_config_494_, lean_object* v_handler_495_, lean_object* v_sources_496_){
_start:
{
lean_object* v___y_499_; uint8_t v___y_500_; lean_object* v___y_501_; lean_object* v_val_502_; lean_object* v_socket_505_; lean_object* v_timer_506_; lean_object* v_expect_507_; lean_object* v_response_508_; lean_object* v_responseBody_509_; lean_object* v_requestBody_510_; lean_object* v_connectionContext_511_; lean_object* v___f_512_; lean_object* v___f_513_; lean_object* v___f_514_; lean_object* v___f_515_; lean_object* v___f_516_; lean_object* v___f_517_; lean_object* v___f_518_; lean_object* v___f_519_; lean_object* v___f_520_; lean_object* v___x_521_; lean_object* v___f_522_; lean_object* v_selectables_524_; lean_object* v___y_563_; lean_object* v___y_579_; 
v_socket_505_ = lean_ctor_get(v_sources_496_, 0);
lean_inc(v_socket_505_);
v_timer_506_ = lean_ctor_get(v_sources_496_, 1);
lean_inc(v_timer_506_);
v_expect_507_ = lean_ctor_get(v_sources_496_, 2);
lean_inc(v_expect_507_);
v_response_508_ = lean_ctor_get(v_sources_496_, 3);
lean_inc_n(v_response_508_, 2);
v_responseBody_509_ = lean_ctor_get(v_sources_496_, 4);
lean_inc_n(v_responseBody_509_, 2);
v_requestBody_510_ = lean_ctor_get(v_sources_496_, 5);
lean_inc_n(v_requestBody_510_, 2);
v_connectionContext_511_ = lean_ctor_get(v_sources_496_, 6);
lean_inc_ref(v_connectionContext_511_);
lean_dec_ref(v_sources_496_);
v___f_512_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0));
v___f_513_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1));
v___f_514_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_514_, 0, v_inst_492_);
lean_closure_set(v___f_514_, 1, v_handler_495_);
lean_closure_set(v___f_514_, 2, v___f_513_);
v___f_515_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2));
v___f_516_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3));
v___f_517_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4));
v___f_518_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5));
v___f_519_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6));
v___f_520_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7));
v___x_521_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8);
lean_inc_ref(v_inst_493_);
lean_inc_ref(v___f_514_);
v___f_522_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed), 12, 9);
lean_closure_set(v___f_522_, 0, v___f_514_);
lean_closure_set(v___f_522_, 1, v_response_508_);
lean_closure_set(v___f_522_, 2, v___x_521_);
lean_closure_set(v___f_522_, 3, v___f_515_);
lean_closure_set(v___f_522_, 4, v_requestBody_510_);
lean_closure_set(v___f_522_, 5, v___f_516_);
lean_closure_set(v___f_522_, 6, v_responseBody_509_);
lean_closure_set(v___f_522_, 7, v_inst_493_);
lean_closure_set(v___f_522_, 8, v___f_517_);
if (lean_obj_tag(v_expect_507_) == 0)
{
lean_object* v_defaultPayloadBytes_582_; 
v_defaultPayloadBytes_582_ = lean_ctor_get(v_config_494_, 9);
lean_inc(v_defaultPayloadBytes_582_);
v___y_579_ = v_defaultPayloadBytes_582_;
goto v___jp_578_;
}
else
{
lean_object* v_val_583_; 
v_val_583_ = lean_ctor_get(v_expect_507_, 0);
lean_inc(v_val_583_);
lean_dec_ref_known(v_expect_507_, 1);
v___y_579_ = v_val_583_;
goto v___jp_578_;
}
v___jp_498_:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v_val_502_);
v___x_504_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_499_, v___y_500_, v___x_503_, v___y_501_);
return v___x_504_;
}
v___jp_523_:
{
if (lean_obj_tag(v_timer_506_) == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec_ref(v___f_522_);
v___x_525_ = lean_box(0);
v___x_526_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_514_, v_response_508_, v___x_521_, v___f_515_, v_requestBody_510_, v___f_516_, v_responseBody_509_, v_inst_493_, v___f_517_, v___x_525_, v_selectables_524_);
return v___x_526_;
}
else
{
lean_object* v_val_527_; 
lean_dec_ref(v___f_514_);
lean_dec(v_requestBody_510_);
lean_dec(v_responseBody_509_);
lean_dec(v_response_508_);
lean_dec_ref(v_inst_493_);
v_val_527_ = lean_ctor_get(v_timer_506_, 0);
lean_inc(v_val_527_);
lean_dec_ref_known(v_timer_506_, 1);
switch(lean_obj_tag(v_val_527_))
{
case 0:
{
lean_object* v_remaining_528_; lean_object* v___f_529_; lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_remaining_528_ = lean_ctor_get(v_val_527_, 0);
lean_inc(v_remaining_528_);
lean_dec_ref_known(v_val_527_, 1);
v___f_529_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_529_, 0, v___f_518_);
lean_closure_set(v___f_529_, 1, v_selectables_524_);
lean_closure_set(v___f_529_, 2, v___f_522_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = 0;
v___x_532_ = l_Std_Async_Selector_sleep(v_remaining_528_);
lean_dec(v_remaining_528_);
v___x_533_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_530_, v___x_531_, v___x_532_, v___f_529_);
return v___x_533_;
}
case 1:
{
lean_object* v_deadline_534_; lean_object* v___f_535_; lean_object* v___f_536_; lean_object* v___x_537_; uint8_t v___x_538_; lean_object* v___x_539_; 
v_deadline_534_ = lean_ctor_get(v_val_527_, 0);
lean_inc_ref(v_deadline_534_);
lean_dec_ref_known(v_val_527_, 1);
v___f_535_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_535_, 0, v___f_519_);
lean_closure_set(v___f_535_, 1, v_selectables_524_);
lean_closure_set(v___f_535_, 2, v___f_522_);
v___f_536_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___boxed), 4, 2);
lean_closure_set(v___f_536_, 0, v_deadline_534_);
lean_closure_set(v___f_536_, 1, v___f_535_);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = 0;
v___x_539_ = lean_get_current_time();
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 1);
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
v___y_499_ = v___x_537_;
v___y_500_ = v___x_538_;
v___y_501_ = v___f_536_;
v_val_502_ = v___x_545_;
goto v___jp_498_;
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
v_a_548_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_539_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_539_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set_tag(v___x_550_, 0);
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
v___y_499_ = v___x_537_;
v___y_500_ = v___x_538_;
v___y_501_ = v___f_536_;
v_val_502_ = v___x_553_;
goto v___jp_498_;
}
}
}
}
default: 
{
lean_object* v_timeout_556_; lean_object* v___f_557_; lean_object* v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_timeout_556_ = lean_ctor_get(v_val_527_, 0);
lean_inc(v_timeout_556_);
lean_dec_ref_known(v_val_527_, 1);
v___f_557_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_557_, 0, v___f_519_);
lean_closure_set(v___f_557_, 1, v_selectables_524_);
lean_closure_set(v___f_557_, 2, v___f_522_);
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = 0;
v___x_560_ = l_Std_Async_Selector_sleep(v_timeout_556_);
lean_dec(v_timeout_556_);
v___x_561_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_558_, v___x_559_, v___x_560_, v___f_557_);
return v___x_561_;
}
}
}
}
v___jp_562_:
{
lean_object* v_token_564_; lean_object* v___f_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_selectables_570_; 
v_token_564_ = lean_ctor_get(v_connectionContext_511_, 1);
lean_inc_ref_n(v_token_564_, 2);
lean_dec_ref(v_connectionContext_511_);
v___f_565_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__13___boxed), 4, 2);
lean_closure_set(v___f_565_, 0, v_token_564_);
lean_closure_set(v___f_565_, 1, v___f_520_);
v___x_566_ = l_Std_CancellationToken_selector(v_token_564_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v___f_565_);
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_mk_empty_array_with_capacity(v___x_568_);
v_selectables_570_ = lean_array_push(v___x_569_, v___x_567_);
if (lean_obj_tag(v_socket_505_) == 1)
{
lean_object* v_val_571_; lean_object* v_recvSelector_572_; uint64_t v_expectedBytes_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_selectables_577_; 
v_val_571_ = lean_ctor_get(v_socket_505_, 0);
lean_inc(v_val_571_);
lean_dec_ref_known(v_socket_505_, 1);
v_recvSelector_572_ = lean_ctor_get(v_inst_491_, 2);
lean_inc_ref(v_recvSelector_572_);
lean_dec_ref(v_inst_491_);
v_expectedBytes_573_ = lean_uint64_of_nat(v___y_563_);
lean_dec(v___y_563_);
v___x_574_ = lean_box_uint64(v_expectedBytes_573_);
v___x_575_ = lean_apply_2(v_recvSelector_572_, v_val_571_, v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___f_512_);
v_selectables_577_ = lean_array_push(v_selectables_570_, v___x_576_);
v_selectables_524_ = v_selectables_577_;
goto v___jp_523_;
}
else
{
lean_dec(v___y_563_);
lean_dec(v_socket_505_);
lean_dec_ref(v_inst_491_);
v_selectables_524_ = v_selectables_570_;
goto v___jp_523_;
}
}
v___jp_578_:
{
lean_object* v_maximumRecvSize_580_; uint8_t v___x_581_; 
v_maximumRecvSize_580_ = lean_ctor_get(v_config_494_, 8);
lean_inc(v_maximumRecvSize_580_);
lean_dec_ref(v_config_494_);
v___x_581_ = lean_nat_dec_le(v___y_579_, v_maximumRecvSize_580_);
if (v___x_581_ == 0)
{
lean_dec(v___y_579_);
v___y_563_ = v_maximumRecvSize_580_;
goto v___jp_562_;
}
else
{
lean_dec(v_maximumRecvSize_580_);
v___y_563_ = v___y_579_;
goto v___jp_562_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_config_587_, lean_object* v_handler_588_, lean_object* v_sources_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_584_, v_inst_585_, v_inst_586_, v_config_587_, v_handler_588_, v_sources_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object* v_00_u03b1_592_, lean_object* v_00_u03c3_593_, lean_object* v_00_u03b2_594_, lean_object* v_inst_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_config_598_, lean_object* v_handler_599_, lean_object* v_sources_600_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_595_, v_inst_596_, v_inst_597_, v_config_598_, v_handler_599_, v_sources_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object* v_00_u03b1_603_, lean_object* v_00_u03c3_604_, lean_object* v_00_u03b2_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_config_609_, lean_object* v_handler_610_, lean_object* v_sources_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(v_00_u03b1_603_, v_00_u03c3_604_, v_00_u03b2_605_, v_inst_606_, v_inst_607_, v_inst_608_, v_config_609_, v_handler_610_, v_sources_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(lean_object* v_machine_614_, lean_object* v_x_615_){
_start:
{
lean_object* v___y_618_; uint8_t v___y_619_; 
if (lean_obj_tag(v_x_615_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v_machine_614_);
v_a_624_ = lean_ctor_get(v_x_615_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_632_ == 0)
{
v___x_626_ = v_x_615_;
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v_x_615_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_631_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___y_635_; uint8_t v___x_641_; 
v_a_633_ = lean_ctor_get(v_x_615_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v_x_615_, 1);
v___x_641_ = lean_unbox(v_a_633_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_box(40);
v___y_635_ = v___x_642_;
goto v___jp_634_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = lean_box(0);
v___y_635_ = v___x_643_;
goto v___jp_634_;
}
v___jp_634_:
{
uint8_t v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_636_ = 0;
lean_inc(v___y_635_);
v___x_637_ = l_Std_Http_Protocol_H1_Machine_canContinue(v___x_636_, v_machine_614_, v___y_635_);
v___x_638_ = lean_unbox(v_a_633_);
lean_dec(v_a_633_);
if (v___x_638_ == 0)
{
uint8_t v___x_639_; 
v___x_639_ = 1;
v___y_618_ = v___x_637_;
v___y_619_ = v___x_639_;
goto v___jp_617_;
}
else
{
uint8_t v___x_640_; 
v___x_640_ = 0;
v___y_618_ = v___x_637_;
v___y_619_ = v___x_640_;
goto v___jp_617_;
}
}
}
v___jp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_620_ = lean_box(v___y_619_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___y_618_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object* v_machine_644_, lean_object* v_x_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(v_machine_644_, v_x_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t v___y_648_){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_box(v___y_648_);
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
uint8_t v___y_1377__boxed_655_; lean_object* v_res_656_; 
v___y_1377__boxed_655_ = lean_unbox(v___y_653_);
v_res_656_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_1377__boxed_655_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object* v_x_657_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; 
v_a_658_ = lean_ctor_get(v_x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v_x_657_, 1);
v___x_659_ = lean_task_pure(v_a_658_);
return v___x_659_;
}
else
{
lean_object* v_a_660_; 
v_a_660_ = lean_ctor_get(v_x_657_, 0);
lean_inc_ref(v_a_660_);
lean_dec_ref_known(v_x_657_, 1);
return v_a_660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object* v_a_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_662_) == 0)
{
uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_dec_ref_known(v_x_662_, 1);
v___x_664_ = 0;
v___x_665_ = lean_box(0);
v___x_666_ = lean_box(v___x_664_);
v___x_667_ = l_Std_Channel_send___redArg(v_a_661_, v___x_666_);
lean_dec_ref(v___x_667_);
return v___x_665_;
}
else
{
lean_object* v_a_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_a_668_ = lean_ctor_get(v_x_662_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v_x_662_, 1);
v___x_669_ = lean_box(0);
v___x_670_ = l_Std_Channel_send___redArg(v_a_661_, v_a_668_);
lean_dec_ref(v___x_670_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object* v_a_671_, lean_object* v_x_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(v_a_671_, v_x_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t v___x_675_, lean_object* v_x_676_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = lean_box(v___x_675_);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object* v___x_681_, lean_object* v_x_682_, lean_object* v___y_683_){
_start:
{
uint8_t v___x_1421__boxed_684_; lean_object* v_res_685_; 
v___x_1421__boxed_684_ = lean_unbox(v___x_681_);
v_res_685_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_1421__boxed_684_, v_x_682_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object* v_connectionContext_686_, uint8_t v___x_687_, lean_object* v_a_688_, lean_object* v___f_689_, lean_object* v___f_690_, lean_object* v___x_691_, uint8_t v___x_692_, lean_object* v___f_693_, lean_object* v_x_694_){
_start:
{
if (lean_obj_tag(v_x_694_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
lean_dec_ref(v___f_693_);
lean_dec(v___x_691_);
lean_dec_ref(v___f_690_);
lean_dec_ref(v___f_689_);
lean_dec_ref(v_a_688_);
lean_dec_ref(v_connectionContext_686_);
v_a_696_ = lean_ctor_get(v_x_694_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_704_ == 0)
{
v___x_698_ = v_x_694_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v_x_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_703_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
}
else
{
lean_object* v_a_705_; lean_object* v_token_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_a_705_ = lean_ctor_get(v_x_694_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v_x_694_, 1);
v_token_706_ = lean_ctor_get(v_connectionContext_686_, 1);
lean_inc_ref(v_token_706_);
lean_dec_ref(v_connectionContext_686_);
v___x_707_ = lean_box(v___x_687_);
v___x_708_ = l_Std_Channel_recvSelector___redArg(v___x_707_, v_a_688_);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v___f_689_);
v___x_710_ = l_Std_CancellationToken_selector(v_token_706_);
lean_inc_ref(v___f_690_);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___f_690_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_a_705_);
lean_ctor_set(v___x_712_, 1, v___f_690_);
v___x_713_ = lean_unsigned_to_nat(3u);
v___x_714_ = lean_mk_empty_array_with_capacity(v___x_713_);
v___x_715_ = lean_array_push(v___x_714_, v___x_709_);
v___x_716_ = lean_array_push(v___x_715_, v___x_711_);
v___x_717_ = lean_array_push(v___x_716_, v___x_712_);
v___x_718_ = l_Std_Async_Selectable_one___redArg(v___x_717_);
v___x_719_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_691_, v___x_692_, v___x_718_, v___f_693_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object* v_connectionContext_720_, lean_object* v___x_721_, lean_object* v_a_722_, lean_object* v___f_723_, lean_object* v___f_724_, lean_object* v___x_725_, lean_object* v___x_726_, lean_object* v___f_727_, lean_object* v_x_728_, lean_object* v___y_729_){
_start:
{
uint8_t v___x_1436__boxed_730_; uint8_t v___x_1441__boxed_731_; lean_object* v_res_732_; 
v___x_1436__boxed_730_ = lean_unbox(v___x_721_);
v___x_1441__boxed_731_ = lean_unbox(v___x_726_);
v_res_732_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_720_, v___x_1436__boxed_730_, v_a_722_, v___f_723_, v___f_724_, v___x_725_, v___x_1441__boxed_731_, v___f_727_, v_x_728_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object* v_config_733_, lean_object* v___x_734_, uint8_t v___x_735_, lean_object* v___f_736_, lean_object* v_x_737_){
_start:
{
if (lean_obj_tag(v_x_737_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v___f_736_);
lean_dec(v___x_734_);
v_a_739_ = lean_ctor_get(v_x_737_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v_x_737_);
if (v_isSharedCheck_747_ == 0)
{
v___x_741_ = v_x_737_;
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v_x_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_746_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; 
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
}
else
{
lean_object* v_lingeringTimeout_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec_ref_known(v_x_737_, 1);
v_lingeringTimeout_748_ = lean_ctor_get(v_config_733_, 4);
v___x_749_ = l_Std_Async_Selector_sleep(v_lingeringTimeout_748_);
v___x_750_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_734_, v___x_735_, v___x_749_, v___f_736_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object* v_config_751_, lean_object* v___x_752_, lean_object* v___x_753_, lean_object* v___f_754_, lean_object* v_x_755_, lean_object* v___y_756_){
_start:
{
uint8_t v___x_1510__boxed_757_; lean_object* v_res_758_; 
v___x_1510__boxed_757_ = lean_unbox(v___x_753_);
v_res_758_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_751_, v___x_752_, v___x_1510__boxed_757_, v___f_754_, v_x_755_);
lean_dec_ref(v_config_751_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object* v_connectionContext_762_, uint8_t v___x_763_, lean_object* v_a_764_, lean_object* v___f_765_, lean_object* v___x_766_, lean_object* v___f_767_, lean_object* v_config_768_, lean_object* v___f_769_, lean_object* v_x_770_){
_start:
{
if (lean_obj_tag(v_x_770_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v___f_769_);
lean_dec_ref(v_config_768_);
lean_dec_ref(v___f_767_);
lean_dec(v___x_766_);
lean_dec_ref(v___f_765_);
lean_dec_ref(v_a_764_);
lean_dec_ref(v_connectionContext_762_);
v_a_772_ = lean_ctor_get(v_x_770_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_x_770_);
if (v_isSharedCheck_780_ == 0)
{
v___x_774_ = v_x_770_;
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v_x_770_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_779_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; 
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_798_; 
v_a_781_ = lean_ctor_get(v_x_770_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v_x_770_);
if (v_isSharedCheck_798_ == 0)
{
v___x_783_ = v_x_770_;
v_isShared_784_ = v_isSharedCheck_798_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v_x_770_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_798_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
uint8_t v___x_785_; lean_object* v___f_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_785_ = 0;
v___f_786_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0));
v___x_787_ = lean_box(v___x_763_);
v___x_788_ = lean_box(v___x_785_);
lean_inc_n(v___x_766_, 3);
v___f_789_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed), 10, 8);
lean_closure_set(v___f_789_, 0, v_connectionContext_762_);
lean_closure_set(v___f_789_, 1, v___x_787_);
lean_closure_set(v___f_789_, 2, v_a_764_);
lean_closure_set(v___f_789_, 3, v___f_765_);
lean_closure_set(v___f_789_, 4, v___f_786_);
lean_closure_set(v___f_789_, 5, v___x_766_);
lean_closure_set(v___f_789_, 6, v___x_788_);
lean_closure_set(v___f_789_, 7, v___f_767_);
v___x_790_ = lean_box(v___x_785_);
v___f_791_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_791_, 0, v_config_768_);
lean_closure_set(v___f_791_, 1, v___x_766_);
lean_closure_set(v___f_791_, 2, v___x_790_);
lean_closure_set(v___f_791_, 3, v___f_789_);
v___x_792_ = l_BaseIO_chainTask___redArg(v_a_781_, v___f_769_, v___x_766_, v___x_785_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_792_);
v___x_794_ = v___x_783_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_797_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
v___x_796_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_766_, v___x_785_, v___x_795_, v___f_791_);
return v___x_796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object* v_connectionContext_799_, lean_object* v___x_800_, lean_object* v_a_801_, lean_object* v___f_802_, lean_object* v___x_803_, lean_object* v___f_804_, lean_object* v_config_805_, lean_object* v___f_806_, lean_object* v_x_807_, lean_object* v___y_808_){
_start:
{
uint8_t v___x_1550__boxed_809_; lean_object* v_res_810_; 
v___x_1550__boxed_809_ = lean_unbox(v___x_800_);
v_res_810_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v_connectionContext_799_, v___x_1550__boxed_809_, v_a_801_, v___f_802_, v___x_803_, v___f_804_, v_config_805_, v___f_806_, v_x_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object* v_inst_811_, lean_object* v_handler_812_, lean_object* v_head_813_, lean_object* v_connectionContext_814_, uint8_t v___x_815_, lean_object* v___f_816_, lean_object* v___f_817_, lean_object* v_config_818_, lean_object* v___f_819_, lean_object* v_x_820_){
_start:
{
if (lean_obj_tag(v_x_820_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_830_; 
lean_dec_ref(v___f_819_);
lean_dec_ref(v_config_818_);
lean_dec_ref(v___f_817_);
lean_dec_ref(v___f_816_);
lean_dec_ref(v_connectionContext_814_);
lean_dec_ref(v_head_813_);
lean_dec(v_handler_812_);
lean_dec_ref(v_inst_811_);
v_a_822_ = lean_ctor_get(v_x_820_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v_x_820_);
if (v_isSharedCheck_830_ == 0)
{
v___x_824_ = v_x_820_;
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v_x_820_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_829_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; 
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_851_; 
v_a_831_ = lean_ctor_get(v_x_820_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v_x_820_);
if (v_isSharedCheck_851_ == 0)
{
v___x_833_ = v_x_820_;
v_isShared_834_ = v_isSharedCheck_851_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v_x_820_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_851_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_onContinue_835_; lean_object* v___f_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___f_840_; uint8_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v_onContinue_835_ = lean_ctor_get(v_inst_811_, 3);
lean_inc_ref(v_onContinue_835_);
lean_dec_ref(v_inst_811_);
lean_inc(v_a_831_);
v___f_836_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_836_, 0, v_a_831_);
v___x_837_ = lean_apply_2(v_onContinue_835_, v_handler_812_, v_head_813_);
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_box(v___x_815_);
v___f_840_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_840_, 0, v_connectionContext_814_);
lean_closure_set(v___f_840_, 1, v___x_839_);
lean_closure_set(v___f_840_, 2, v_a_831_);
lean_closure_set(v___f_840_, 3, v___f_816_);
lean_closure_set(v___f_840_, 4, v___x_838_);
lean_closure_set(v___f_840_, 5, v___f_817_);
lean_closure_set(v___f_840_, 6, v_config_818_);
lean_closure_set(v___f_840_, 7, v___f_836_);
v___x_841_ = 0;
v___x_842_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_842_, 0, lean_box(0));
lean_closure_set(v___x_842_, 1, v___x_837_);
v___x_843_ = lean_io_as_task(v___x_842_, v___x_838_);
v___x_844_ = 1;
v___x_845_ = lean_task_bind(v___x_843_, v___f_819_, v___x_838_, v___x_844_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_845_);
v___x_847_ = v___x_833_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_850_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
v___x_849_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_838_, v___x_841_, v___x_848_, v___f_840_);
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object* v_inst_852_, lean_object* v_handler_853_, lean_object* v_head_854_, lean_object* v_connectionContext_855_, lean_object* v___x_856_, lean_object* v___f_857_, lean_object* v___f_858_, lean_object* v_config_859_, lean_object* v___f_860_, lean_object* v_x_861_, lean_object* v___y_862_){
_start:
{
uint8_t v___x_1633__boxed_863_; lean_object* v_res_864_; 
v___x_1633__boxed_863_ = lean_unbox(v___x_856_);
v_res_864_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_852_, v_handler_853_, v_head_854_, v_connectionContext_855_, v___x_1633__boxed_863_, v___f_857_, v___f_858_, v_config_859_, v___f_860_, v_x_861_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object* v_inst_867_, lean_object* v_handler_868_, lean_object* v_machine_869_, lean_object* v_head_870_, lean_object* v_config_871_, lean_object* v_connectionContext_872_){
_start:
{
lean_object* v___f_874_; lean_object* v___f_875_; lean_object* v___f_876_; uint8_t v___x_877_; lean_object* v___x_878_; lean_object* v___f_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___f_874_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_874_, 0, v_machine_869_);
v___f_875_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0));
v___f_876_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1));
v___x_877_ = 0;
v___x_878_ = lean_box(v___x_877_);
v___f_879_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_879_, 0, v_inst_867_);
lean_closure_set(v___f_879_, 1, v_handler_868_);
lean_closure_set(v___f_879_, 2, v_head_870_);
lean_closure_set(v___f_879_, 3, v_connectionContext_872_);
lean_closure_set(v___f_879_, 4, v___x_878_);
lean_closure_set(v___f_879_, 5, v___f_875_);
lean_closure_set(v___f_879_, 6, v___f_874_);
lean_closure_set(v___f_879_, 7, v_config_871_);
lean_closure_set(v___f_879_, 8, v___f_876_);
v___x_880_ = lean_box(0);
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = l_Std_CloseableChannel_new___redArg(v___x_880_);
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
v___x_885_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_881_, v___x_877_, v___x_884_, v___f_879_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object* v_inst_886_, lean_object* v_handler_887_, lean_object* v_machine_888_, lean_object* v_head_889_, lean_object* v_config_890_, lean_object* v_connectionContext_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_886_, v_handler_887_, v_machine_888_, v_head_889_, v_config_890_, v_connectionContext_891_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object* v_00_u03c3_894_, lean_object* v_inst_895_, lean_object* v_handler_896_, lean_object* v_machine_897_, lean_object* v_head_898_, lean_object* v_config_899_, lean_object* v_connectionContext_900_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_895_, v_handler_896_, v_machine_897_, v_head_898_, v_config_899_, v_connectionContext_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object* v_00_u03c3_903_, lean_object* v_inst_904_, lean_object* v_handler_905_, lean_object* v_machine_906_, lean_object* v_head_907_, lean_object* v_config_908_, lean_object* v_connectionContext_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(v_00_u03c3_903_, v_inst_904_, v_handler_905_, v_machine_906_, v_head_907_, v_config_908_, v_connectionContext_909_);
return v_res_911_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v_x_912_){
_start:
{
lean_object* v_fst_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_fst_913_ = lean_ctor_get(v_x_912_, 0);
v___x_914_ = l_Std_Http_Header_Name_contentLength;
v___x_915_ = lean_string_dec_eq(v_fst_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = l_Std_Http_Header_Name_transferEncoding;
v___x_917_ = lean_string_dec_eq(v_fst_913_, v___x_916_);
return v___x_917_;
}
else
{
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v_x_918_){
_start:
{
uint8_t v_res_919_; lean_object* v_r_920_; 
v_res_919_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v_x_918_);
lean_dec_ref(v_x_918_);
v_r_920_ = lean_box(v_res_919_);
return v_r_920_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___y_921_, lean_object* v_____r_922_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_924_ = lean_box(0);
v___x_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_925_, 0, v___y_921_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___y_928_, lean_object* v_____r_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___y_928_, v_____r_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v___f_932_, lean_object* v_x_933_){
_start:
{
if (lean_obj_tag(v_x_933_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_943_; 
lean_dec_ref(v___f_932_);
v_a_935_ = lean_ctor_get(v_x_933_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v_x_933_);
if (v_isSharedCheck_943_ == 0)
{
v___x_937_ = v_x_933_;
v_isShared_938_ = v_isSharedCheck_943_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v_x_933_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_943_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_942_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_945_; 
v_a_944_ = lean_ctor_get(v_x_933_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v_x_933_, 1);
v___x_945_ = lean_apply_2(v___f_932_, v_a_944_, lean_box(0));
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v___f_946_, lean_object* v_x_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v___f_946_, v_x_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_close_950_, lean_object* v_body_951_, lean_object* v___f_952_, lean_object* v___f_953_, lean_object* v_x_954_){
_start:
{
if (lean_obj_tag(v_x_954_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_964_; 
lean_dec_ref(v___f_953_);
lean_dec_ref(v___f_952_);
lean_dec(v_body_951_);
lean_dec_ref(v_close_950_);
v_a_956_ = lean_ctor_get(v_x_954_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_x_954_);
if (v_isSharedCheck_964_ == 0)
{
v___x_958_ = v_x_954_;
v_isShared_959_ = v_isSharedCheck_964_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v_x_954_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_964_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_963_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
}
else
{
lean_object* v_a_965_; uint8_t v___x_966_; 
v_a_965_ = lean_ctor_get(v_x_954_, 0);
lean_inc(v_a_965_);
lean_dec_ref_known(v_x_954_, 1);
v___x_966_ = lean_unbox(v_a_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
lean_dec_ref(v___f_953_);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_apply_2(v_close_950_, v_body_951_, lean_box(0));
v___x_969_ = lean_unbox(v_a_965_);
lean_dec(v_a_965_);
v___x_970_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_967_, v___x_969_, v___x_968_, v___f_952_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec(v_a_965_);
lean_dec_ref(v___f_952_);
lean_dec(v_body_951_);
lean_dec_ref(v_close_950_);
v___x_971_ = lean_box(0);
v___x_972_ = lean_apply_2(v___f_953_, v___x_971_, lean_box(0));
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_close_973_, lean_object* v_body_974_, lean_object* v___f_975_, lean_object* v___f_976_, lean_object* v_x_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_close_973_, v_body_974_, v___f_975_, v___f_976_, v_x_977_);
return v_res_979_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_980_, lean_object* v_x_981_){
_start:
{
lean_object* v_fst_982_; uint8_t v___x_983_; 
v_fst_982_ = lean_ctor_get(v_x_981_, 0);
v___x_983_ = lean_string_dec_eq(v_fst_982_, v___x_980_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_984_, lean_object* v_x_985_){
_start:
{
uint8_t v_res_986_; lean_object* v_r_987_; 
v_res_986_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_984_, v_x_985_);
lean_dec_ref(v_x_985_);
lean_dec_ref(v___x_984_);
v_r_987_ = lean_box(v_res_986_);
return v_r_987_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object* v___x_988_, lean_object* v_x1_989_, lean_object* v_x2_990_){
_start:
{
lean_object* v_fst_991_; uint8_t v___x_992_; 
v_fst_991_ = lean_ctor_get(v_x2_990_, 0);
v___x_992_ = lean_string_dec_eq(v_fst_991_, v___x_988_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
v___x_993_ = lean_array_push(v_x1_989_, v_x2_990_);
return v___x_993_;
}
else
{
lean_dec_ref(v_x2_990_);
return v_x1_989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed(lean_object* v___x_994_, lean_object* v_x1_995_, lean_object* v_x2_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(v___x_994_, v_x1_995_, v_x2_996_);
lean_dec_ref(v___x_994_);
return v_res_997_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___f_1018_; 
v___x_1017_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1018_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1018_, 0, v___x_1017_);
return v___f_1018_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___f_1020_; 
v___x_1019_ = l_Std_Http_Header_Name_transferEncoding;
v___f_1020_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_1020_, 0, v___x_1019_);
return v___f_1020_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___f_1024_; 
v___x_1023_ = l_Std_Http_Header_Name_contentLength;
v___f_1024_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1024_, 0, v___x_1023_);
return v___f_1024_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___f_1026_; 
v___x_1025_ = l_Std_Http_Header_Name_contentLength;
v___f_1026_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_1026_, 0, v___x_1025_);
return v___f_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object* v_body_1027_, lean_object* v_close_1028_, lean_object* v_isClosed_1029_, lean_object* v_line_1030_, lean_object* v___f_1031_, lean_object* v_machine_1032_, lean_object* v_x_1033_){
_start:
{
lean_object* v___y_1036_; uint8_t v_omitBody_1037_; lean_object* v___y_1050_; uint8_t v___y_1054_; uint8_t v___y_1055_; lean_object* v_reader_1056_; lean_object* v_writer_1057_; lean_object* v_config_1058_; lean_object* v_events_1059_; lean_object* v_error_1060_; lean_object* v_date_1061_; uint8_t v_keepAlive_1062_; uint8_t v_pullBodyStalled_1063_; uint8_t v___y_1064_; uint8_t v___y_1132_; lean_object* v___y_1133_; uint8_t v___y_1134_; uint8_t v___y_1154_; lean_object* v___y_1155_; uint8_t v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1162_; uint8_t v___y_1163_; lean_object* v___y_1164_; uint16_t v___y_1165_; lean_object* v___y_1166_; uint8_t v___y_1185_; uint8_t v___y_1186_; lean_object* v_val_1187_; uint8_t v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; uint8_t v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; uint8_t v___y_1211_; uint8_t v___y_1212_; uint8_t v___y_1213_; uint8_t v___y_1214_; lean_object* v___y_1218_; uint8_t v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; uint8_t v___y_1229_; uint8_t v___y_1230_; uint8_t v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1236_; uint8_t v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; uint8_t v___y_1248_; uint8_t v___y_1249_; uint8_t v___y_1250_; uint8_t v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1271_; uint8_t v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; uint8_t v___y_1283_; uint8_t v___y_1284_; uint8_t v___y_1285_; uint8_t v___y_1286_; lean_object* v___y_1287_; uint8_t v___y_1301_; lean_object* v___y_1302_; uint8_t v___y_1303_; uint8_t v___y_1304_; lean_object* v___y_1305_; uint8_t v___y_1310_; lean_object* v___y_1311_; uint8_t v___y_1312_; lean_object* v___y_1313_; uint8_t v___y_1314_; uint16_t v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; uint8_t v___y_1328_; uint8_t v___y_1329_; uint8_t v___y_1330_; uint8_t v___y_1331_; uint8_t v___y_1349_; lean_object* v___y_1350_; uint8_t v___y_1351_; uint8_t v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; uint8_t v___y_1363_; uint8_t v___y_1364_; uint8_t v___y_1365_; uint8_t v___y_1366_; lean_object* v___y_1367_; uint8_t v___y_1376_; lean_object* v___y_1377_; uint8_t v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; uint8_t v___y_1389_; uint8_t v___y_1390_; uint8_t v___y_1391_; uint8_t v___y_1392_; uint8_t v___y_1393_; uint8_t v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1398_; uint8_t v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; uint8_t v___y_1410_; uint8_t v___y_1411_; uint8_t v___y_1412_; uint8_t v___y_1413_; lean_object* v___y_1428_; lean_object* v_reader_1429_; lean_object* v_userData_1430_; lean_object* v_outputData_1431_; lean_object* v_state_1432_; lean_object* v_knownSize_1433_; lean_object* v_messageHead_1434_; uint8_t v_userClosedBody_1435_; uint8_t v_omitBody_1436_; lean_object* v_userDataBytes_1437_; lean_object* v_config_1438_; lean_object* v_events_1439_; lean_object* v_error_1440_; lean_object* v_date_1441_; uint8_t v_keepAlive_1442_; uint8_t v_pullBodyStalled_1443_; 
if (lean_obj_tag(v_x_1033_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1480_; 
lean_dec_ref(v_machine_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_line_1030_);
lean_dec_ref(v_isClosed_1029_);
lean_dec_ref(v_close_1028_);
lean_dec(v_body_1027_);
v_a_1472_ = lean_ctor_get(v_x_1033_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_x_1033_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1474_ = v_x_1033_;
v_isShared_1475_ = v_isSharedCheck_1480_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v_x_1033_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1480_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; 
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
}
else
{
lean_object* v_a_1481_; 
v_a_1481_ = lean_ctor_get(v_x_1033_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v_x_1033_, 1);
if (lean_obj_tag(v_a_1481_) == 1)
{
lean_object* v_writer_1482_; lean_object* v_reader_1483_; lean_object* v_config_1484_; lean_object* v_events_1485_; lean_object* v_error_1486_; lean_object* v_date_1487_; uint8_t v_keepAlive_1488_; uint8_t v_pullBodyStalled_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1511_; 
v_writer_1482_ = lean_ctor_get(v_machine_1032_, 1);
v_reader_1483_ = lean_ctor_get(v_machine_1032_, 0);
v_config_1484_ = lean_ctor_get(v_machine_1032_, 2);
v_events_1485_ = lean_ctor_get(v_machine_1032_, 3);
v_error_1486_ = lean_ctor_get(v_machine_1032_, 4);
v_date_1487_ = lean_ctor_get(v_machine_1032_, 5);
v_keepAlive_1488_ = lean_ctor_get_uint8(v_machine_1032_, sizeof(void*)*6);
v_pullBodyStalled_1489_ = lean_ctor_get_uint8(v_machine_1032_, sizeof(void*)*6 + 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_machine_1032_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1491_ = v_machine_1032_;
v_isShared_1492_ = v_isSharedCheck_1511_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_date_1487_);
lean_inc(v_error_1486_);
lean_inc(v_events_1485_);
lean_inc(v_config_1484_);
lean_inc(v_writer_1482_);
lean_inc(v_reader_1483_);
lean_dec(v_machine_1032_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1511_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v_userData_1493_; lean_object* v_outputData_1494_; lean_object* v_state_1495_; lean_object* v_messageHead_1496_; uint8_t v_userClosedBody_1497_; uint8_t v_omitBody_1498_; lean_object* v_userDataBytes_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1509_; 
v_userData_1493_ = lean_ctor_get(v_writer_1482_, 0);
v_outputData_1494_ = lean_ctor_get(v_writer_1482_, 1);
v_state_1495_ = lean_ctor_get(v_writer_1482_, 2);
v_messageHead_1496_ = lean_ctor_get(v_writer_1482_, 4);
v_userClosedBody_1497_ = lean_ctor_get_uint8(v_writer_1482_, sizeof(void*)*6);
v_omitBody_1498_ = lean_ctor_get_uint8(v_writer_1482_, sizeof(void*)*6 + 1);
v_userDataBytes_1499_ = lean_ctor_get(v_writer_1482_, 5);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_writer_1482_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v_writer_1482_, 3);
lean_dec(v_unused_1510_);
v___x_1501_ = v_writer_1482_;
v_isShared_1502_ = v_isSharedCheck_1509_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_userDataBytes_1499_);
lean_inc(v_messageHead_1496_);
lean_inc(v_state_1495_);
lean_inc(v_outputData_1494_);
lean_inc(v_userData_1493_);
lean_dec(v_writer_1482_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1509_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
lean_inc(v_userDataBytes_1499_);
lean_inc(v_messageHead_1496_);
lean_inc_ref(v_a_1481_);
lean_inc(v_state_1495_);
lean_inc_ref(v_outputData_1494_);
lean_inc_ref(v_userData_1493_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 3, v_a_1481_);
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_userData_1493_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_outputData_1494_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_state_1495_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_a_1481_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_messageHead_1496_);
lean_ctor_set(v_reuseFailAlloc_1508_, 5, v_userDataBytes_1499_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*6, v_userClosedBody_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*6 + 1, v_omitBody_1498_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
lean_inc(v_date_1487_);
lean_inc(v_error_1486_);
lean_inc_ref(v_events_1485_);
lean_inc_ref(v_config_1484_);
lean_inc_ref(v_reader_1483_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v___x_1504_);
v___x_1506_ = v___x_1491_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_reader_1483_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_config_1484_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_events_1485_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v_error_1486_);
lean_ctor_set(v_reuseFailAlloc_1507_, 5, v_date_1487_);
lean_ctor_set_uint8(v_reuseFailAlloc_1507_, sizeof(void*)*6, v_keepAlive_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1507_, sizeof(void*)*6 + 1, v_pullBodyStalled_1489_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
v___y_1428_ = v___x_1506_;
v_reader_1429_ = v_reader_1483_;
v_userData_1430_ = v_userData_1493_;
v_outputData_1431_ = v_outputData_1494_;
v_state_1432_ = v_state_1495_;
v_knownSize_1433_ = v_a_1481_;
v_messageHead_1434_ = v_messageHead_1496_;
v_userClosedBody_1435_ = v_userClosedBody_1497_;
v_omitBody_1436_ = v_omitBody_1498_;
v_userDataBytes_1437_ = v_userDataBytes_1499_;
v_config_1438_ = v_config_1484_;
v_events_1439_ = v_events_1485_;
v_error_1440_ = v_error_1486_;
v_date_1441_ = v_date_1487_;
v_keepAlive_1442_ = v_keepAlive_1488_;
v_pullBodyStalled_1443_ = v_pullBodyStalled_1489_;
goto v___jp_1427_;
}
}
}
}
}
else
{
lean_object* v_writer_1512_; lean_object* v_reader_1513_; lean_object* v_config_1514_; lean_object* v_events_1515_; lean_object* v_error_1516_; lean_object* v_date_1517_; uint8_t v_keepAlive_1518_; uint8_t v_pullBodyStalled_1519_; lean_object* v_userData_1520_; lean_object* v_outputData_1521_; lean_object* v_state_1522_; lean_object* v_knownSize_1523_; lean_object* v_messageHead_1524_; uint8_t v_userClosedBody_1525_; uint8_t v_omitBody_1526_; lean_object* v_userDataBytes_1527_; 
lean_dec(v_a_1481_);
v_writer_1512_ = lean_ctor_get(v_machine_1032_, 1);
v_reader_1513_ = lean_ctor_get(v_machine_1032_, 0);
lean_inc_ref(v_reader_1513_);
v_config_1514_ = lean_ctor_get(v_machine_1032_, 2);
lean_inc_ref(v_config_1514_);
v_events_1515_ = lean_ctor_get(v_machine_1032_, 3);
lean_inc_ref(v_events_1515_);
v_error_1516_ = lean_ctor_get(v_machine_1032_, 4);
lean_inc(v_error_1516_);
v_date_1517_ = lean_ctor_get(v_machine_1032_, 5);
lean_inc(v_date_1517_);
v_keepAlive_1518_ = lean_ctor_get_uint8(v_machine_1032_, sizeof(void*)*6);
v_pullBodyStalled_1519_ = lean_ctor_get_uint8(v_machine_1032_, sizeof(void*)*6 + 1);
v_userData_1520_ = lean_ctor_get(v_writer_1512_, 0);
lean_inc_ref(v_userData_1520_);
v_outputData_1521_ = lean_ctor_get(v_writer_1512_, 1);
lean_inc_ref(v_outputData_1521_);
v_state_1522_ = lean_ctor_get(v_writer_1512_, 2);
lean_inc(v_state_1522_);
v_knownSize_1523_ = lean_ctor_get(v_writer_1512_, 3);
lean_inc(v_knownSize_1523_);
v_messageHead_1524_ = lean_ctor_get(v_writer_1512_, 4);
lean_inc(v_messageHead_1524_);
v_userClosedBody_1525_ = lean_ctor_get_uint8(v_writer_1512_, sizeof(void*)*6);
v_omitBody_1526_ = lean_ctor_get_uint8(v_writer_1512_, sizeof(void*)*6 + 1);
v_userDataBytes_1527_ = lean_ctor_get(v_writer_1512_, 5);
lean_inc(v_userDataBytes_1527_);
v___y_1428_ = v_machine_1032_;
v_reader_1429_ = v_reader_1513_;
v_userData_1430_ = v_userData_1520_;
v_outputData_1431_ = v_outputData_1521_;
v_state_1432_ = v_state_1522_;
v_knownSize_1433_ = v_knownSize_1523_;
v_messageHead_1434_ = v_messageHead_1524_;
v_userClosedBody_1435_ = v_userClosedBody_1525_;
v_omitBody_1436_ = v_omitBody_1526_;
v_userDataBytes_1437_ = v_userDataBytes_1527_;
v_config_1438_ = v_config_1514_;
v_events_1439_ = v_events_1515_;
v_error_1440_ = v_error_1516_;
v_date_1441_ = v_date_1517_;
v_keepAlive_1442_ = v_keepAlive_1518_;
v_pullBodyStalled_1443_ = v_pullBodyStalled_1519_;
goto v___jp_1427_;
}
}
v___jp_1035_:
{
if (v_omitBody_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec_ref(v_isClosed_1029_);
lean_dec_ref(v_close_1028_);
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_body_1027_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___y_1036_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
else
{
lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___f_1042_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1042_, 0, v___y_1036_);
lean_inc_ref(v___f_1042_);
v___f_1043_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1043_, 0, v___f_1042_);
lean_inc(v_body_1027_);
v___f_1044_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_1044_, 0, v_close_1028_);
lean_closure_set(v___f_1044_, 1, v_body_1027_);
lean_closure_set(v___f_1044_, 2, v___f_1043_);
lean_closure_set(v___f_1044_, 3, v___f_1042_);
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = 0;
v___x_1047_ = lean_apply_2(v_isClosed_1029_, v_body_1027_, lean_box(0));
v___x_1048_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1045_, v___x_1046_, v___x_1047_, v___f_1044_);
return v___x_1048_;
}
}
v___jp_1049_:
{
lean_object* v_writer_1051_; uint8_t v_omitBody_1052_; 
v_writer_1051_ = lean_ctor_get(v___y_1050_, 1);
v_omitBody_1052_ = lean_ctor_get_uint8(v_writer_1051_, sizeof(void*)*6 + 1);
v___y_1036_ = v___y_1050_;
v_omitBody_1037_ = v_omitBody_1052_;
goto v___jp_1035_;
}
v___jp_1053_:
{
lean_object* v_userData_1065_; lean_object* v_outputData_1066_; lean_object* v_state_1067_; lean_object* v_knownSize_1068_; uint8_t v_userClosedBody_1069_; uint8_t v_omitBody_1070_; lean_object* v_userDataBytes_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1129_; 
v_userData_1065_ = lean_ctor_get(v_writer_1057_, 0);
v_outputData_1066_ = lean_ctor_get(v_writer_1057_, 1);
v_state_1067_ = lean_ctor_get(v_writer_1057_, 2);
v_knownSize_1068_ = lean_ctor_get(v_writer_1057_, 3);
v_userClosedBody_1069_ = lean_ctor_get_uint8(v_writer_1057_, sizeof(void*)*6);
v_omitBody_1070_ = lean_ctor_get_uint8(v_writer_1057_, sizeof(void*)*6 + 1);
v_userDataBytes_1071_ = lean_ctor_get(v_writer_1057_, 5);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_writer_1057_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v_writer_1057_, 4);
lean_dec(v_unused_1130_);
v___x_1073_ = v_writer_1057_;
v_isShared_1074_ = v_isSharedCheck_1129_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_userDataBytes_1071_);
lean_inc(v_knownSize_1068_);
lean_inc(v_state_1067_);
lean_inc(v_outputData_1066_);
lean_inc(v_userData_1065_);
lean_dec(v_writer_1057_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1129_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
lean_inc_ref(v_line_1030_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 4, v_line_1030_);
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_userData_1065_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_outputData_1066_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v_state_1067_);
lean_ctor_set(v_reuseFailAlloc_1128_, 3, v_knownSize_1068_);
lean_ctor_set(v_reuseFailAlloc_1128_, 4, v_line_1030_);
lean_ctor_set(v_reuseFailAlloc_1128_, 5, v_userDataBytes_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, sizeof(void*)*6, v_userClosedBody_1069_);
lean_ctor_set_uint8(v_reuseFailAlloc_1128_, sizeof(void*)*6 + 1, v_omitBody_1070_);
v___x_1076_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v_machine_1077_; lean_object* v_machine_1078_; lean_object* v_writer_1079_; lean_object* v_reader_1080_; lean_object* v_config_1081_; lean_object* v_events_1082_; lean_object* v_error_1083_; lean_object* v_date_1084_; uint8_t v_keepAlive_1085_; uint8_t v_pullBodyStalled_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1127_; 
v_machine_1077_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_machine_1077_, 0, v_reader_1056_);
lean_ctor_set(v_machine_1077_, 1, v___x_1076_);
lean_ctor_set(v_machine_1077_, 2, v_config_1058_);
lean_ctor_set(v_machine_1077_, 3, v_events_1059_);
lean_ctor_set(v_machine_1077_, 4, v_error_1060_);
lean_ctor_set(v_machine_1077_, 5, v_date_1061_);
lean_ctor_set_uint8(v_machine_1077_, sizeof(void*)*6, v_keepAlive_1062_);
lean_ctor_set_uint8(v_machine_1077_, sizeof(void*)*6 + 1, v_pullBodyStalled_1063_);
v_machine_1078_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___y_1055_, v_machine_1077_, v_line_1030_);
lean_dec_ref(v_line_1030_);
v_writer_1079_ = lean_ctor_get(v_machine_1078_, 1);
v_reader_1080_ = lean_ctor_get(v_machine_1078_, 0);
v_config_1081_ = lean_ctor_get(v_machine_1078_, 2);
v_events_1082_ = lean_ctor_get(v_machine_1078_, 3);
v_error_1083_ = lean_ctor_get(v_machine_1078_, 4);
v_date_1084_ = lean_ctor_get(v_machine_1078_, 5);
v_keepAlive_1085_ = lean_ctor_get_uint8(v_machine_1078_, sizeof(void*)*6);
v_pullBodyStalled_1086_ = lean_ctor_get_uint8(v_machine_1078_, sizeof(void*)*6 + 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_machine_1078_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1088_ = v_machine_1078_;
v_isShared_1089_ = v_isSharedCheck_1127_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_date_1084_);
lean_inc(v_error_1083_);
lean_inc(v_events_1082_);
lean_inc(v_config_1081_);
lean_inc(v_writer_1079_);
lean_inc(v_reader_1080_);
lean_dec(v_machine_1078_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1127_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_userData_1090_; lean_object* v_outputData_1091_; lean_object* v_knownSize_1092_; lean_object* v_messageHead_1093_; uint8_t v_userClosedBody_1094_; uint8_t v_omitBody_1095_; lean_object* v_userDataBytes_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1125_; 
v_userData_1090_ = lean_ctor_get(v_writer_1079_, 0);
v_outputData_1091_ = lean_ctor_get(v_writer_1079_, 1);
v_knownSize_1092_ = lean_ctor_get(v_writer_1079_, 3);
v_messageHead_1093_ = lean_ctor_get(v_writer_1079_, 4);
v_userClosedBody_1094_ = lean_ctor_get_uint8(v_writer_1079_, sizeof(void*)*6);
v_omitBody_1095_ = lean_ctor_get_uint8(v_writer_1079_, sizeof(void*)*6 + 1);
v_userDataBytes_1096_ = lean_ctor_get(v_writer_1079_, 5);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_writer_1079_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v_writer_1079_, 2);
lean_dec(v_unused_1126_);
v___x_1098_ = v_writer_1079_;
v_isShared_1099_ = v_isSharedCheck_1125_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_userDataBytes_1096_);
lean_inc(v_messageHead_1093_);
lean_inc(v_knownSize_1092_);
lean_inc(v_outputData_1091_);
lean_inc(v_userData_1090_);
lean_dec(v_writer_1079_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1125_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1100_ = lean_box(2);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 2, v___x_1100_);
v___x_1102_ = v___x_1098_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_userData_1090_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_outputData_1091_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_knownSize_1092_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_messageHead_1093_);
lean_ctor_set(v_reuseFailAlloc_1124_, 5, v_userDataBytes_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*6, v_userClosedBody_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*6 + 1, v_omitBody_1095_);
v___x_1102_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
if (v___y_1064_ == 0)
{
lean_object* v_machine_1104_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1102_);
v_machine_1104_ = v___x_1088_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_reader_1080_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_config_1081_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_events_1082_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_error_1083_);
lean_ctor_set(v_reuseFailAlloc_1105_, 5, v_date_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*6, v_keepAlive_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*6 + 1, v_pullBodyStalled_1086_);
v_machine_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
v___y_1036_ = v_machine_1104_;
v_omitBody_1037_ = v_omitBody_1095_;
goto v___jp_1035_;
}
}
else
{
lean_object* v_input_1106_; lean_object* v_messageHead_1107_; lean_object* v_messageCount_1108_; lean_object* v_bodyBytesRead_1109_; lean_object* v_headerBytesRead_1110_; uint8_t v_peerClosed_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1122_; 
v_input_1106_ = lean_ctor_get(v_reader_1080_, 1);
v_messageHead_1107_ = lean_ctor_get(v_reader_1080_, 2);
v_messageCount_1108_ = lean_ctor_get(v_reader_1080_, 3);
v_bodyBytesRead_1109_ = lean_ctor_get(v_reader_1080_, 4);
v_headerBytesRead_1110_ = lean_ctor_get(v_reader_1080_, 5);
v_peerClosed_1111_ = lean_ctor_get_uint8(v_reader_1080_, sizeof(void*)*6);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_reader_1080_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v_reader_1080_, 0);
lean_dec(v_unused_1123_);
v___x_1113_ = v_reader_1080_;
v_isShared_1114_ = v_isSharedCheck_1122_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_headerBytesRead_1110_);
lean_inc(v_bodyBytesRead_1109_);
lean_inc(v_messageCount_1108_);
lean_inc(v_messageHead_1107_);
lean_inc(v_input_1106_);
lean_dec(v_reader_1080_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1122_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1115_ = lean_box(6);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1115_);
v___x_1117_ = v___x_1113_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_input_1106_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_messageHead_1107_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_messageCount_1108_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_bodyBytesRead_1109_);
lean_ctor_set(v_reuseFailAlloc_1121_, 5, v_headerBytesRead_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1121_, sizeof(void*)*6, v_peerClosed_1111_);
v___x_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
lean_ctor_set_uint8(v___x_1117_, sizeof(void*)*6 + 1, v___y_1064_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 1, v___x_1102_);
lean_ctor_set(v___x_1088_, 0, v___x_1117_);
v___x_1119_ = v___x_1088_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_config_1081_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_events_1082_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_error_1083_);
lean_ctor_set(v_reuseFailAlloc_1120_, 5, v_date_1084_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*6, v___y_1054_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*6 + 1, v___y_1054_);
v___y_1036_ = v___x_1119_;
v_omitBody_1037_ = v_omitBody_1095_;
goto v___jp_1035_;
}
}
}
}
}
}
}
}
}
}
v___jp_1131_:
{
lean_object* v_reader_1135_; lean_object* v_messageHead_1136_; lean_object* v_writer_1137_; lean_object* v_config_1138_; lean_object* v_events_1139_; lean_object* v_error_1140_; lean_object* v_date_1141_; uint8_t v_keepAlive_1142_; uint8_t v_pullBodyStalled_1143_; uint8_t v_method_1144_; uint8_t v___x_1145_; uint8_t v___x_1146_; 
v_reader_1135_ = lean_ctor_get(v___y_1133_, 0);
lean_inc_ref(v_reader_1135_);
v_messageHead_1136_ = lean_ctor_get(v_reader_1135_, 2);
v_writer_1137_ = lean_ctor_get(v___y_1133_, 1);
lean_inc_ref(v_writer_1137_);
v_config_1138_ = lean_ctor_get(v___y_1133_, 2);
lean_inc_ref(v_config_1138_);
v_events_1139_ = lean_ctor_get(v___y_1133_, 3);
lean_inc_ref(v_events_1139_);
v_error_1140_ = lean_ctor_get(v___y_1133_, 4);
lean_inc(v_error_1140_);
v_date_1141_ = lean_ctor_get(v___y_1133_, 5);
lean_inc(v_date_1141_);
v_keepAlive_1142_ = lean_ctor_get_uint8(v___y_1133_, sizeof(void*)*6);
v_pullBodyStalled_1143_ = lean_ctor_get_uint8(v___y_1133_, sizeof(void*)*6 + 1);
lean_dec_ref(v___y_1133_);
v_method_1144_ = lean_ctor_get_uint8(v_messageHead_1136_, sizeof(void*)*2);
v___x_1145_ = 5;
v___x_1146_ = l_Std_Http_instBEqMethod_beq(v_method_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
v___y_1054_ = v___y_1134_;
v___y_1055_ = v___y_1132_;
v_reader_1056_ = v_reader_1135_;
v_writer_1057_ = v_writer_1137_;
v_config_1058_ = v_config_1138_;
v_events_1059_ = v_events_1139_;
v_error_1060_ = v_error_1140_;
v_date_1061_ = v_date_1141_;
v_keepAlive_1062_ = v_keepAlive_1142_;
v_pullBodyStalled_1063_ = v_pullBodyStalled_1143_;
v___y_1064_ = v___x_1146_;
goto v___jp_1053_;
}
else
{
lean_object* v_status_1147_; uint16_t v___x_1148_; uint16_t v___x_1149_; uint8_t v___x_1150_; 
v_status_1147_ = lean_ctor_get(v_line_1030_, 0);
v___x_1148_ = 200;
v___x_1149_ = l_Std_Http_Status_toCode(v_status_1147_);
v___x_1150_ = lean_uint16_dec_le(v___x_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
v___y_1054_ = v___y_1134_;
v___y_1055_ = v___y_1132_;
v_reader_1056_ = v_reader_1135_;
v_writer_1057_ = v_writer_1137_;
v_config_1058_ = v_config_1138_;
v_events_1059_ = v_events_1139_;
v_error_1060_ = v_error_1140_;
v_date_1061_ = v_date_1141_;
v_keepAlive_1062_ = v_keepAlive_1142_;
v_pullBodyStalled_1063_ = v_pullBodyStalled_1143_;
v___y_1064_ = v___x_1150_;
goto v___jp_1053_;
}
else
{
uint16_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = 300;
v___x_1152_ = lean_uint16_dec_lt(v___x_1149_, v___x_1151_);
v___y_1054_ = v___y_1134_;
v___y_1055_ = v___y_1132_;
v_reader_1056_ = v_reader_1135_;
v_writer_1057_ = v_writer_1137_;
v_config_1058_ = v_config_1138_;
v_events_1059_ = v_events_1139_;
v_error_1060_ = v_error_1140_;
v_date_1061_ = v_date_1141_;
v_keepAlive_1062_ = v_keepAlive_1142_;
v_pullBodyStalled_1063_ = v_pullBodyStalled_1143_;
v___y_1064_ = v___x_1152_;
goto v___jp_1053_;
}
}
}
v___jp_1153_:
{
uint8_t v___x_1156_; 
v___x_1156_ = 0;
v___y_1132_ = v___y_1154_;
v___y_1133_ = v___y_1155_;
v___y_1134_ = v___x_1156_;
goto v___jp_1131_;
}
v___jp_1157_:
{
lean_object* v___x_1160_; 
v___x_1160_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_rejectOutgoingFraming(v___y_1158_, v___y_1159_);
v___y_1050_ = v___x_1160_;
goto v___jp_1049_;
}
v___jp_1161_:
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_unsigned_to_nat(204u);
v___x_1168_ = lean_nat_dec_eq(v___y_1166_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_unsigned_to_nat(304u);
v___x_1170_ = lean_nat_dec_eq(v___y_1166_, v___x_1169_);
lean_dec(v___y_1166_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_box(9);
v___x_1172_ = l_Std_Http_instBEqStatus_beq(v___y_1162_, v___x_1171_);
lean_dec(v___y_1162_);
if (v___x_1172_ == 0)
{
lean_object* v_reader_1173_; lean_object* v_messageHead_1174_; uint8_t v_method_1175_; uint8_t v___x_1176_; uint8_t v___x_1177_; 
v_reader_1173_ = lean_ctor_get(v___y_1164_, 0);
v_messageHead_1174_ = lean_ctor_get(v_reader_1173_, 2);
v_method_1175_ = lean_ctor_get_uint8(v_messageHead_1174_, sizeof(void*)*2);
v___x_1176_ = 9;
v___x_1177_ = l_Std_Http_instBEqMethod_beq(v_method_1175_, v___x_1176_);
if (v___x_1177_ == 0)
{
uint8_t v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = 5;
v___x_1179_ = l_Std_Http_instBEqMethod_beq(v_method_1175_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_dec_ref(v_line_1030_);
v___y_1158_ = v___y_1163_;
v___y_1159_ = v___y_1164_;
goto v___jp_1157_;
}
else
{
uint16_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = 200;
v___x_1181_ = lean_uint16_dec_le(v___x_1180_, v___y_1165_);
if (v___x_1181_ == 0)
{
lean_dec_ref(v_line_1030_);
v___y_1158_ = v___y_1163_;
v___y_1159_ = v___y_1164_;
goto v___jp_1157_;
}
else
{
uint16_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = 300;
v___x_1183_ = lean_uint16_dec_lt(v___y_1165_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_dec_ref(v_line_1030_);
v___y_1158_ = v___y_1163_;
v___y_1159_ = v___y_1164_;
goto v___jp_1157_;
}
else
{
v___y_1154_ = v___y_1163_;
v___y_1155_ = v___y_1164_;
goto v___jp_1153_;
}
}
}
}
else
{
v___y_1154_ = v___y_1163_;
v___y_1155_ = v___y_1164_;
goto v___jp_1153_;
}
}
else
{
v___y_1154_ = v___y_1163_;
v___y_1155_ = v___y_1164_;
goto v___jp_1153_;
}
}
else
{
lean_dec(v___y_1162_);
v___y_1154_ = v___y_1163_;
v___y_1155_ = v___y_1164_;
goto v___jp_1153_;
}
}
else
{
lean_dec(v___y_1166_);
lean_dec(v___y_1162_);
v___y_1154_ = v___y_1163_;
v___y_1155_ = v___y_1164_;
goto v___jp_1153_;
}
}
v___jp_1184_:
{
uint8_t v___x_1188_; 
v___x_1188_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_unframeableForHttp10(v___y_1185_, v_val_1187_, v_line_1030_);
if (v___x_1188_ == 0)
{
v___y_1132_ = v___y_1185_;
v___y_1133_ = v_val_1187_;
v___y_1134_ = v___y_1186_;
goto v___jp_1131_;
}
else
{
lean_object* v_status_1189_; uint16_t v___x_1190_; lean_object* v_code_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_status_1189_ = lean_ctor_get(v_line_1030_, 0);
v___x_1190_ = l_Std_Http_Status_toCode(v_status_1189_);
v_code_1191_ = lean_uint16_to_nat(v___x_1190_);
v___x_1192_ = lean_unsigned_to_nat(100u);
v___x_1193_ = lean_nat_dec_le(v___x_1192_, v_code_1191_);
if (v___x_1193_ == 0)
{
lean_inc(v_status_1189_);
v___y_1162_ = v_status_1189_;
v___y_1163_ = v___y_1185_;
v___y_1164_ = v_val_1187_;
v___y_1165_ = v___x_1190_;
v___y_1166_ = v_code_1191_;
goto v___jp_1161_;
}
else
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = lean_unsigned_to_nat(200u);
v___x_1195_ = lean_nat_dec_lt(v_code_1191_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_inc(v_status_1189_);
v___y_1162_ = v_status_1189_;
v___y_1163_ = v___y_1185_;
v___y_1164_ = v_val_1187_;
v___y_1165_ = v___x_1190_;
v___y_1166_ = v_code_1191_;
goto v___jp_1161_;
}
else
{
v___y_1154_ = v___y_1185_;
v___y_1155_ = v_val_1187_;
goto v___jp_1153_;
}
}
}
}
v___jp_1196_:
{
if (lean_obj_tag(v___y_1199_) == 0)
{
lean_dec_ref(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1198_);
v___y_1185_ = v___y_1200_;
v___y_1186_ = v___y_1211_;
v_val_1187_ = v___y_1201_;
goto v___jp_1184_;
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_dec_ref(v___y_1201_);
v___x_1215_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1215_, 0, v___y_1208_);
lean_ctor_set(v___x_1215_, 1, v___y_1204_);
lean_ctor_set(v___x_1215_, 2, v___y_1203_);
lean_ctor_set(v___x_1215_, 3, v___y_1199_);
lean_ctor_set(v___x_1215_, 4, v___y_1205_);
lean_ctor_set(v___x_1215_, 5, v___y_1207_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*6, v___y_1213_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*6 + 1, v___y_1212_);
v___x_1216_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1216_, 0, v___y_1210_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
lean_ctor_set(v___x_1216_, 2, v___y_1202_);
lean_ctor_set(v___x_1216_, 3, v___y_1209_);
lean_ctor_set(v___x_1216_, 4, v___y_1206_);
lean_ctor_set(v___x_1216_, 5, v___y_1198_);
lean_ctor_set_uint8(v___x_1216_, sizeof(void*)*6, v___y_1197_);
lean_ctor_set_uint8(v___x_1216_, sizeof(void*)*6 + 1, v___y_1214_);
v___y_1185_ = v___y_1200_;
v___y_1186_ = v___y_1211_;
v_val_1187_ = v___x_1216_;
goto v___jp_1184_;
}
}
v___jp_1217_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1233_, 0, v___y_1226_);
lean_ctor_set(v___x_1233_, 1, v___y_1232_);
lean_ctor_set(v___x_1233_, 2, v___y_1221_);
lean_ctor_set(v___x_1233_, 3, v___y_1222_);
lean_ctor_set(v___x_1233_, 4, v___y_1223_);
lean_ctor_set(v___x_1233_, 5, v___y_1225_);
lean_ctor_set_uint8(v___x_1233_, sizeof(void*)*6, v___y_1230_);
lean_ctor_set_uint8(v___x_1233_, sizeof(void*)*6 + 1, v___y_1229_);
v___x_1234_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1234_, 0, v___y_1228_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
lean_ctor_set(v___x_1234_, 2, v___y_1220_);
lean_ctor_set(v___x_1234_, 3, v___y_1227_);
lean_ctor_set(v___x_1234_, 4, v___y_1224_);
lean_ctor_set(v___x_1234_, 5, v___y_1218_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*6, v___y_1219_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*6 + 1, v___y_1231_);
v___y_1036_ = v___x_1234_;
v_omitBody_1037_ = v___y_1229_;
goto v___jp_1035_;
}
v___jp_1235_:
{
lean_object* v_message_1253_; lean_object* v___x_1254_; lean_object* v___x_2335__overap_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_message_1253_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1250_, v_line_1030_, v___y_1252_);
v___x_1254_ = l_ByteArray_empty;
v___x_2335__overap_1255_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1250_);
v___x_1256_ = lean_apply_2(v___x_2335__overap_1255_, v___x_1254_, v_message_1253_);
v___x_1257_ = l_ByteArray_isEmpty(v___x_1256_);
if (v___x_1257_ == 0)
{
lean_object* v_data_1258_; lean_object* v_size_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1269_; 
v_data_1258_ = lean_ctor_get(v___y_1240_, 0);
v_size_1259_ = lean_ctor_get(v___y_1240_, 1);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___y_1240_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1261_ = v___y_1240_;
v_isShared_1262_ = v_isSharedCheck_1269_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_size_1259_);
lean_inc(v_data_1258_);
lean_dec(v___y_1240_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1269_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
lean_inc_ref(v___x_1256_);
v___x_1263_ = lean_array_push(v_data_1258_, v___x_1256_);
v___x_1264_ = lean_byte_array_size(v___x_1256_);
lean_dec_ref(v___x_1256_);
v___x_1265_ = lean_nat_add(v_size_1259_, v___x_1264_);
lean_dec(v_size_1259_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1265_);
lean_ctor_set(v___x_1261_, 0, v___x_1263_);
v___x_1267_ = v___x_1261_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
v___y_1218_ = v___y_1236_;
v___y_1219_ = v___y_1237_;
v___y_1220_ = v___y_1238_;
v___y_1221_ = v___y_1239_;
v___y_1222_ = v___y_1241_;
v___y_1223_ = v___y_1242_;
v___y_1224_ = v___y_1243_;
v___y_1225_ = v___y_1244_;
v___y_1226_ = v___y_1245_;
v___y_1227_ = v___y_1246_;
v___y_1228_ = v___y_1247_;
v___y_1229_ = v___y_1248_;
v___y_1230_ = v___y_1249_;
v___y_1231_ = v___y_1251_;
v___y_1232_ = v___x_1267_;
goto v___jp_1217_;
}
}
}
else
{
lean_dec_ref(v___x_1256_);
v___y_1218_ = v___y_1236_;
v___y_1219_ = v___y_1237_;
v___y_1220_ = v___y_1238_;
v___y_1221_ = v___y_1239_;
v___y_1222_ = v___y_1241_;
v___y_1223_ = v___y_1242_;
v___y_1224_ = v___y_1243_;
v___y_1225_ = v___y_1244_;
v___y_1226_ = v___y_1245_;
v___y_1227_ = v___y_1246_;
v___y_1228_ = v___y_1247_;
v___y_1229_ = v___y_1248_;
v___y_1230_ = v___y_1249_;
v___y_1231_ = v___y_1251_;
v___y_1232_ = v___y_1240_;
goto v___jp_1217_;
}
}
v___jp_1270_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_array_get_size(v___y_1287_);
v___x_1290_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1291_ = lean_nat_dec_lt(v___x_1288_, v___x_1289_);
if (v___x_1291_ == 0)
{
v___y_1236_ = v___y_1271_;
v___y_1237_ = v___y_1272_;
v___y_1238_ = v___y_1273_;
v___y_1239_ = v___y_1274_;
v___y_1240_ = v___y_1275_;
v___y_1241_ = v___y_1276_;
v___y_1242_ = v___y_1277_;
v___y_1243_ = v___y_1278_;
v___y_1244_ = v___y_1279_;
v___y_1245_ = v___y_1280_;
v___y_1246_ = v___y_1281_;
v___y_1247_ = v___y_1282_;
v___y_1248_ = v___y_1283_;
v___y_1249_ = v___y_1284_;
v___y_1250_ = v___y_1285_;
v___y_1251_ = v___y_1286_;
v___y_1252_ = v___y_1287_;
goto v___jp_1235_;
}
else
{
lean_object* v___f_1292_; size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___f_1292_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10);
v___x_1293_ = ((size_t)0ULL);
v___x_1294_ = lean_usize_of_nat(v___x_1289_);
lean_inc_ref(v___y_1287_);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1290_, v___f_1292_, v___y_1287_, v___x_1293_, v___x_1294_);
v___x_1296_ = lean_unbox(v___x_1295_);
lean_dec(v___x_1295_);
if (v___x_1296_ == 0)
{
v___y_1236_ = v___y_1271_;
v___y_1237_ = v___y_1272_;
v___y_1238_ = v___y_1273_;
v___y_1239_ = v___y_1274_;
v___y_1240_ = v___y_1275_;
v___y_1241_ = v___y_1276_;
v___y_1242_ = v___y_1277_;
v___y_1243_ = v___y_1278_;
v___y_1244_ = v___y_1279_;
v___y_1245_ = v___y_1280_;
v___y_1246_ = v___y_1281_;
v___y_1247_ = v___y_1282_;
v___y_1248_ = v___y_1283_;
v___y_1249_ = v___y_1284_;
v___y_1250_ = v___y_1285_;
v___y_1251_ = v___y_1286_;
v___y_1252_ = v___y_1287_;
goto v___jp_1235_;
}
else
{
lean_object* v___f_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___f_1297_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11);
v___x_1298_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1290_, v___f_1297_, v___y_1287_, v___x_1293_, v___x_1294_, v___x_1298_);
v___y_1236_ = v___y_1271_;
v___y_1237_ = v___y_1272_;
v___y_1238_ = v___y_1273_;
v___y_1239_ = v___y_1274_;
v___y_1240_ = v___y_1275_;
v___y_1241_ = v___y_1276_;
v___y_1242_ = v___y_1277_;
v___y_1243_ = v___y_1278_;
v___y_1244_ = v___y_1279_;
v___y_1245_ = v___y_1280_;
v___y_1246_ = v___y_1281_;
v___y_1247_ = v___y_1282_;
v___y_1248_ = v___y_1283_;
v___y_1249_ = v___y_1284_;
v___y_1250_ = v___y_1285_;
v___y_1251_ = v___y_1286_;
v___y_1252_ = v___x_1299_;
goto v___jp_1235_;
}
}
}
v___jp_1300_:
{
lean_object* v___x_1306_; 
lean_inc_ref(v___y_1305_);
v___x_1306_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___y_1303_, v___y_1305_, v___y_1302_, v___y_1301_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v___x_1307_; 
lean_dec_ref(v_line_1030_);
v___x_1307_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_rejectOutgoingFraming(v___y_1303_, v___y_1305_);
v___y_1050_ = v___x_1307_;
goto v___jp_1049_;
}
else
{
lean_object* v_val_1308_; 
lean_dec_ref(v___y_1305_);
v_val_1308_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v___x_1306_, 1);
v___y_1185_ = v___y_1303_;
v___y_1186_ = v___y_1304_;
v_val_1187_ = v_val_1308_;
goto v___jp_1184_;
}
}
v___jp_1309_:
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = lean_unsigned_to_nat(204u);
v___x_1333_ = lean_nat_dec_eq(v___y_1317_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = lean_unsigned_to_nat(304u);
v___x_1335_ = lean_nat_dec_eq(v___y_1317_, v___x_1334_);
lean_dec(v___y_1317_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_box(9);
v___x_1337_ = l_Std_Http_instBEqStatus_beq(v___y_1326_, v___x_1336_);
lean_dec(v___y_1326_);
if (v___x_1337_ == 0)
{
lean_object* v_messageHead_1338_; uint8_t v_method_1339_; uint8_t v___x_1340_; uint8_t v___x_1341_; 
v_messageHead_1338_ = lean_ctor_get(v___y_1327_, 2);
v_method_1339_ = lean_ctor_get_uint8(v_messageHead_1338_, sizeof(void*)*2);
v___x_1340_ = 9;
v___x_1341_ = l_Std_Http_instBEqMethod_beq(v_method_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
uint8_t v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = 5;
v___x_1343_ = l_Std_Http_instBEqMethod_beq(v_method_1339_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_dec_ref(v___y_1327_);
lean_dec_ref(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1311_);
v___y_1301_ = v___y_1312_;
v___y_1302_ = v___y_1313_;
v___y_1303_ = v___y_1314_;
v___y_1304_ = v___y_1328_;
v___y_1305_ = v___y_1316_;
goto v___jp_1300_;
}
else
{
uint16_t v___x_1344_; uint8_t v___x_1345_; 
v___x_1344_ = 200;
v___x_1345_ = lean_uint16_dec_le(v___x_1344_, v___y_1315_);
if (v___x_1345_ == 0)
{
lean_dec_ref(v___y_1327_);
lean_dec_ref(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1311_);
v___y_1301_ = v___y_1312_;
v___y_1302_ = v___y_1313_;
v___y_1303_ = v___y_1314_;
v___y_1304_ = v___y_1328_;
v___y_1305_ = v___y_1316_;
goto v___jp_1300_;
}
else
{
uint16_t v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = 300;
v___x_1347_ = lean_uint16_dec_lt(v___y_1315_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_dec_ref(v___y_1327_);
lean_dec_ref(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1311_);
v___y_1301_ = v___y_1312_;
v___y_1302_ = v___y_1313_;
v___y_1303_ = v___y_1314_;
v___y_1304_ = v___y_1328_;
v___y_1305_ = v___y_1316_;
goto v___jp_1300_;
}
else
{
v___y_1197_ = v___y_1310_;
v___y_1198_ = v___y_1311_;
v___y_1199_ = v___y_1313_;
v___y_1200_ = v___y_1314_;
v___y_1201_ = v___y_1316_;
v___y_1202_ = v___y_1318_;
v___y_1203_ = v___y_1319_;
v___y_1204_ = v___y_1320_;
v___y_1205_ = v___y_1321_;
v___y_1206_ = v___y_1322_;
v___y_1207_ = v___y_1323_;
v___y_1208_ = v___y_1324_;
v___y_1209_ = v___y_1325_;
v___y_1210_ = v___y_1327_;
v___y_1211_ = v___y_1328_;
v___y_1212_ = v___y_1329_;
v___y_1213_ = v___y_1330_;
v___y_1214_ = v___y_1331_;
goto v___jp_1196_;
}
}
}
}
else
{
v___y_1197_ = v___y_1310_;
v___y_1198_ = v___y_1311_;
v___y_1199_ = v___y_1313_;
v___y_1200_ = v___y_1314_;
v___y_1201_ = v___y_1316_;
v___y_1202_ = v___y_1318_;
v___y_1203_ = v___y_1319_;
v___y_1204_ = v___y_1320_;
v___y_1205_ = v___y_1321_;
v___y_1206_ = v___y_1322_;
v___y_1207_ = v___y_1323_;
v___y_1208_ = v___y_1324_;
v___y_1209_ = v___y_1325_;
v___y_1210_ = v___y_1327_;
v___y_1211_ = v___y_1328_;
v___y_1212_ = v___y_1329_;
v___y_1213_ = v___y_1330_;
v___y_1214_ = v___y_1331_;
goto v___jp_1196_;
}
}
else
{
v___y_1197_ = v___y_1310_;
v___y_1198_ = v___y_1311_;
v___y_1199_ = v___y_1313_;
v___y_1200_ = v___y_1314_;
v___y_1201_ = v___y_1316_;
v___y_1202_ = v___y_1318_;
v___y_1203_ = v___y_1319_;
v___y_1204_ = v___y_1320_;
v___y_1205_ = v___y_1321_;
v___y_1206_ = v___y_1322_;
v___y_1207_ = v___y_1323_;
v___y_1208_ = v___y_1324_;
v___y_1209_ = v___y_1325_;
v___y_1210_ = v___y_1327_;
v___y_1211_ = v___y_1328_;
v___y_1212_ = v___y_1329_;
v___y_1213_ = v___y_1330_;
v___y_1214_ = v___y_1331_;
goto v___jp_1196_;
}
}
else
{
lean_dec(v___y_1326_);
v___y_1197_ = v___y_1310_;
v___y_1198_ = v___y_1311_;
v___y_1199_ = v___y_1313_;
v___y_1200_ = v___y_1314_;
v___y_1201_ = v___y_1316_;
v___y_1202_ = v___y_1318_;
v___y_1203_ = v___y_1319_;
v___y_1204_ = v___y_1320_;
v___y_1205_ = v___y_1321_;
v___y_1206_ = v___y_1322_;
v___y_1207_ = v___y_1323_;
v___y_1208_ = v___y_1324_;
v___y_1209_ = v___y_1325_;
v___y_1210_ = v___y_1327_;
v___y_1211_ = v___y_1328_;
v___y_1212_ = v___y_1329_;
v___y_1213_ = v___y_1330_;
v___y_1214_ = v___y_1331_;
goto v___jp_1196_;
}
}
else
{
lean_dec(v___y_1326_);
lean_dec(v___y_1317_);
v___y_1197_ = v___y_1310_;
v___y_1198_ = v___y_1311_;
v___y_1199_ = v___y_1313_;
v___y_1200_ = v___y_1314_;
v___y_1201_ = v___y_1316_;
v___y_1202_ = v___y_1318_;
v___y_1203_ = v___y_1319_;
v___y_1204_ = v___y_1320_;
v___y_1205_ = v___y_1321_;
v___y_1206_ = v___y_1322_;
v___y_1207_ = v___y_1323_;
v___y_1208_ = v___y_1324_;
v___y_1209_ = v___y_1325_;
v___y_1210_ = v___y_1327_;
v___y_1211_ = v___y_1328_;
v___y_1212_ = v___y_1329_;
v___y_1213_ = v___y_1330_;
v___y_1214_ = v___y_1331_;
goto v___jp_1196_;
}
}
v___jp_1348_:
{
lean_object* v_status_1368_; uint16_t v___x_1369_; lean_object* v_code_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_status_1368_ = lean_ctor_get(v_line_1030_, 0);
v___x_1369_ = l_Std_Http_Status_toCode(v_status_1368_);
v_code_1370_ = lean_uint16_to_nat(v___x_1369_);
v___x_1371_ = lean_unsigned_to_nat(100u);
v___x_1372_ = lean_nat_dec_le(v___x_1371_, v_code_1370_);
if (v___x_1372_ == 0)
{
lean_inc(v_status_1368_);
v___y_1310_ = v___y_1349_;
v___y_1311_ = v___y_1350_;
v___y_1312_ = v___y_1351_;
v___y_1313_ = v___y_1367_;
v___y_1314_ = v___y_1352_;
v___y_1315_ = v___x_1369_;
v___y_1316_ = v___y_1353_;
v___y_1317_ = v_code_1370_;
v___y_1318_ = v___y_1354_;
v___y_1319_ = v___y_1355_;
v___y_1320_ = v___y_1356_;
v___y_1321_ = v___y_1357_;
v___y_1322_ = v___y_1358_;
v___y_1323_ = v___y_1359_;
v___y_1324_ = v___y_1360_;
v___y_1325_ = v___y_1361_;
v___y_1326_ = v_status_1368_;
v___y_1327_ = v___y_1362_;
v___y_1328_ = v___y_1363_;
v___y_1329_ = v___y_1364_;
v___y_1330_ = v___y_1365_;
v___y_1331_ = v___y_1366_;
goto v___jp_1309_;
}
else
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = lean_unsigned_to_nat(200u);
v___x_1374_ = lean_nat_dec_lt(v_code_1370_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_inc(v_status_1368_);
v___y_1310_ = v___y_1349_;
v___y_1311_ = v___y_1350_;
v___y_1312_ = v___y_1351_;
v___y_1313_ = v___y_1367_;
v___y_1314_ = v___y_1352_;
v___y_1315_ = v___x_1369_;
v___y_1316_ = v___y_1353_;
v___y_1317_ = v_code_1370_;
v___y_1318_ = v___y_1354_;
v___y_1319_ = v___y_1355_;
v___y_1320_ = v___y_1356_;
v___y_1321_ = v___y_1357_;
v___y_1322_ = v___y_1358_;
v___y_1323_ = v___y_1359_;
v___y_1324_ = v___y_1360_;
v___y_1325_ = v___y_1361_;
v___y_1326_ = v_status_1368_;
v___y_1327_ = v___y_1362_;
v___y_1328_ = v___y_1363_;
v___y_1329_ = v___y_1364_;
v___y_1330_ = v___y_1365_;
v___y_1331_ = v___y_1366_;
goto v___jp_1309_;
}
else
{
v___y_1197_ = v___y_1349_;
v___y_1198_ = v___y_1350_;
v___y_1199_ = v___y_1367_;
v___y_1200_ = v___y_1352_;
v___y_1201_ = v___y_1353_;
v___y_1202_ = v___y_1354_;
v___y_1203_ = v___y_1355_;
v___y_1204_ = v___y_1356_;
v___y_1205_ = v___y_1357_;
v___y_1206_ = v___y_1358_;
v___y_1207_ = v___y_1359_;
v___y_1208_ = v___y_1360_;
v___y_1209_ = v___y_1361_;
v___y_1210_ = v___y_1362_;
v___y_1211_ = v___y_1363_;
v___y_1212_ = v___y_1364_;
v___y_1213_ = v___y_1365_;
v___y_1214_ = v___y_1366_;
goto v___jp_1196_;
}
}
}
v___jp_1375_:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_box(0);
v___y_1349_ = v___y_1376_;
v___y_1350_ = v___y_1377_;
v___y_1351_ = v___y_1393_;
v___y_1352_ = v___y_1378_;
v___y_1353_ = v___y_1379_;
v___y_1354_ = v___y_1380_;
v___y_1355_ = v___y_1381_;
v___y_1356_ = v___y_1382_;
v___y_1357_ = v___y_1383_;
v___y_1358_ = v___y_1384_;
v___y_1359_ = v___y_1385_;
v___y_1360_ = v___y_1386_;
v___y_1361_ = v___y_1387_;
v___y_1362_ = v___y_1388_;
v___y_1363_ = v___y_1389_;
v___y_1364_ = v___y_1390_;
v___y_1365_ = v___y_1391_;
v___y_1366_ = v___y_1392_;
v___y_1367_ = v___x_1394_;
goto v___jp_1348_;
}
v___jp_1395_:
{
uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1414_ = 1;
v___x_1415_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1414_, v_line_1030_);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_array_get_size(v___x_1415_);
v___x_1418_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1419_ = lean_nat_dec_lt(v___x_1416_, v___x_1417_);
if (v___x_1419_ == 0)
{
lean_dec_ref(v___x_1415_);
lean_dec_ref(v___f_1031_);
v___y_1376_ = v___y_1396_;
v___y_1377_ = v___y_1397_;
v___y_1378_ = v___y_1399_;
v___y_1379_ = v___y_1400_;
v___y_1380_ = v___y_1401_;
v___y_1381_ = v___y_1402_;
v___y_1382_ = v___y_1403_;
v___y_1383_ = v___y_1404_;
v___y_1384_ = v___y_1405_;
v___y_1385_ = v___y_1406_;
v___y_1386_ = v___y_1407_;
v___y_1387_ = v___y_1408_;
v___y_1388_ = v___y_1409_;
v___y_1389_ = v___y_1410_;
v___y_1390_ = v___y_1411_;
v___y_1391_ = v___y_1412_;
v___y_1392_ = v___y_1413_;
v___y_1393_ = v___x_1419_;
goto v___jp_1375_;
}
else
{
size_t v___x_1420_; size_t v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = lean_usize_of_nat(v___x_1417_);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1418_, v___f_1031_, v___x_1415_, v___x_1420_, v___x_1421_);
v___x_1423_ = lean_unbox(v___x_1422_);
if (v___x_1423_ == 0)
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_unbox(v___x_1422_);
lean_dec(v___x_1422_);
v___y_1376_ = v___y_1396_;
v___y_1377_ = v___y_1397_;
v___y_1378_ = v___y_1399_;
v___y_1379_ = v___y_1400_;
v___y_1380_ = v___y_1401_;
v___y_1381_ = v___y_1402_;
v___y_1382_ = v___y_1403_;
v___y_1383_ = v___y_1404_;
v___y_1384_ = v___y_1405_;
v___y_1385_ = v___y_1406_;
v___y_1386_ = v___y_1407_;
v___y_1387_ = v___y_1408_;
v___y_1388_ = v___y_1409_;
v___y_1389_ = v___y_1410_;
v___y_1390_ = v___y_1411_;
v___y_1391_ = v___y_1412_;
v___y_1392_ = v___y_1413_;
v___y_1393_ = v___x_1424_;
goto v___jp_1375_;
}
else
{
lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1425_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_1414_, v_line_1030_, v___y_1398_);
v___x_1426_ = lean_unbox(v___x_1422_);
lean_dec(v___x_1422_);
v___y_1349_ = v___y_1396_;
v___y_1350_ = v___y_1397_;
v___y_1351_ = v___x_1426_;
v___y_1352_ = v___y_1399_;
v___y_1353_ = v___y_1400_;
v___y_1354_ = v___y_1401_;
v___y_1355_ = v___y_1402_;
v___y_1356_ = v___y_1403_;
v___y_1357_ = v___y_1404_;
v___y_1358_ = v___y_1405_;
v___y_1359_ = v___y_1406_;
v___y_1360_ = v___y_1407_;
v___y_1361_ = v___y_1408_;
v___y_1362_ = v___y_1409_;
v___y_1363_ = v___y_1410_;
v___y_1364_ = v___y_1411_;
v___y_1365_ = v___y_1412_;
v___y_1366_ = v___y_1413_;
v___y_1367_ = v___x_1425_;
goto v___jp_1348_;
}
}
}
v___jp_1427_:
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = lean_box(1);
v___x_1445_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1432_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_dec(v_date_1441_);
lean_dec(v_error_1440_);
lean_dec_ref(v_events_1439_);
lean_dec_ref(v_config_1438_);
lean_dec(v_userDataBytes_1437_);
lean_dec(v_messageHead_1434_);
lean_dec(v_knownSize_1433_);
lean_dec(v_state_1432_);
lean_dec_ref(v_outputData_1431_);
lean_dec_ref(v_userData_1430_);
lean_dec_ref(v_reader_1429_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v_line_1030_);
v___y_1036_ = v___y_1428_;
v_omitBody_1037_ = v_omitBody_1436_;
goto v___jp_1035_;
}
else
{
lean_object* v_status_1446_; uint8_t v___x_1447_; uint8_t v___x_1448_; uint16_t v___x_1449_; uint16_t v___x_1450_; uint8_t v___x_1451_; 
v_status_1446_ = lean_ctor_get(v_line_1030_, 0);
v___x_1447_ = 0;
v___x_1448_ = 0;
v___x_1449_ = 100;
v___x_1450_ = l_Std_Http_Status_toCode(v_status_1446_);
v___x_1451_ = lean_uint16_dec_le(v___x_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_dec(v_knownSize_1433_);
v___y_1396_ = v_keepAlive_1442_;
v___y_1397_ = v_date_1441_;
v___y_1398_ = v___x_1451_;
v___y_1399_ = v___x_1447_;
v___y_1400_ = v___y_1428_;
v___y_1401_ = v_config_1438_;
v___y_1402_ = v_state_1432_;
v___y_1403_ = v_outputData_1431_;
v___y_1404_ = v_messageHead_1434_;
v___y_1405_ = v_error_1440_;
v___y_1406_ = v_userDataBytes_1437_;
v___y_1407_ = v_userData_1430_;
v___y_1408_ = v_events_1439_;
v___y_1409_ = v_reader_1429_;
v___y_1410_ = v___x_1448_;
v___y_1411_ = v_omitBody_1436_;
v___y_1412_ = v_userClosedBody_1435_;
v___y_1413_ = v_pullBodyStalled_1443_;
goto v___jp_1395_;
}
else
{
uint16_t v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = 200;
v___x_1453_ = lean_uint16_dec_lt(v___x_1450_, v___x_1452_);
if (v___x_1453_ == 0)
{
lean_dec(v_knownSize_1433_);
v___y_1396_ = v_keepAlive_1442_;
v___y_1397_ = v_date_1441_;
v___y_1398_ = v___x_1453_;
v___y_1399_ = v___x_1447_;
v___y_1400_ = v___y_1428_;
v___y_1401_ = v_config_1438_;
v___y_1402_ = v_state_1432_;
v___y_1403_ = v_outputData_1431_;
v___y_1404_ = v_messageHead_1434_;
v___y_1405_ = v_error_1440_;
v___y_1406_ = v_userDataBytes_1437_;
v___y_1407_ = v_userData_1430_;
v___y_1408_ = v_events_1439_;
v___y_1409_ = v_reader_1429_;
v___y_1410_ = v___x_1448_;
v___y_1411_ = v_omitBody_1436_;
v___y_1412_ = v_userClosedBody_1435_;
v___y_1413_ = v_pullBodyStalled_1443_;
goto v___jp_1395_;
}
else
{
lean_object* v_messageHead_1454_; uint8_t v___x_1455_; uint8_t v___x_1456_; uint8_t v___x_1457_; 
lean_dec_ref(v___f_1031_);
v_messageHead_1454_ = lean_ctor_get(v_reader_1429_, 2);
v___x_1455_ = l_Std_Http_Protocol_H1_Message_Head_version(v___x_1447_, v_messageHead_1454_);
v___x_1456_ = 1;
v___x_1457_ = l_Std_Http_instBEqVersion_beq(v___x_1455_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_dec(v_date_1441_);
lean_dec(v_error_1440_);
lean_dec_ref(v_events_1439_);
lean_dec_ref(v_config_1438_);
lean_dec(v_userDataBytes_1437_);
lean_dec(v_messageHead_1434_);
lean_dec(v_knownSize_1433_);
lean_dec(v_state_1432_);
lean_dec_ref(v_outputData_1431_);
lean_dec_ref(v_userData_1430_);
lean_dec_ref(v_reader_1429_);
lean_dec_ref(v_line_1030_);
v___y_1050_ = v___y_1428_;
goto v___jp_1049_;
}
else
{
uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
lean_dec_ref(v___y_1428_);
v___x_1458_ = 1;
v___x_1459_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1458_, v_line_1030_);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_array_get_size(v___x_1459_);
v___x_1462_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1463_ = lean_nat_dec_lt(v___x_1460_, v___x_1461_);
if (v___x_1463_ == 0)
{
v___y_1271_ = v_date_1441_;
v___y_1272_ = v_keepAlive_1442_;
v___y_1273_ = v_config_1438_;
v___y_1274_ = v_state_1432_;
v___y_1275_ = v_outputData_1431_;
v___y_1276_ = v_knownSize_1433_;
v___y_1277_ = v_messageHead_1434_;
v___y_1278_ = v_error_1440_;
v___y_1279_ = v_userDataBytes_1437_;
v___y_1280_ = v_userData_1430_;
v___y_1281_ = v_events_1439_;
v___y_1282_ = v_reader_1429_;
v___y_1283_ = v_omitBody_1436_;
v___y_1284_ = v_userClosedBody_1435_;
v___y_1285_ = v___x_1458_;
v___y_1286_ = v_pullBodyStalled_1443_;
v___y_1287_ = v___x_1459_;
goto v___jp_1270_;
}
else
{
lean_object* v___f_1464_; size_t v___x_1465_; size_t v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___f_1464_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13);
v___x_1465_ = ((size_t)0ULL);
v___x_1466_ = lean_usize_of_nat(v___x_1461_);
lean_inc_ref(v___x_1459_);
v___x_1467_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1462_, v___f_1464_, v___x_1459_, v___x_1465_, v___x_1466_);
v___x_1468_ = lean_unbox(v___x_1467_);
lean_dec(v___x_1467_);
if (v___x_1468_ == 0)
{
v___y_1271_ = v_date_1441_;
v___y_1272_ = v_keepAlive_1442_;
v___y_1273_ = v_config_1438_;
v___y_1274_ = v_state_1432_;
v___y_1275_ = v_outputData_1431_;
v___y_1276_ = v_knownSize_1433_;
v___y_1277_ = v_messageHead_1434_;
v___y_1278_ = v_error_1440_;
v___y_1279_ = v_userDataBytes_1437_;
v___y_1280_ = v_userData_1430_;
v___y_1281_ = v_events_1439_;
v___y_1282_ = v_reader_1429_;
v___y_1283_ = v_omitBody_1436_;
v___y_1284_ = v_userClosedBody_1435_;
v___y_1285_ = v___x_1458_;
v___y_1286_ = v_pullBodyStalled_1443_;
v___y_1287_ = v___x_1459_;
goto v___jp_1270_;
}
else
{
lean_object* v___f_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___f_1469_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14);
v___x_1470_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___x_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1462_, v___f_1469_, v___x_1459_, v___x_1465_, v___x_1466_, v___x_1470_);
v___y_1271_ = v_date_1441_;
v___y_1272_ = v_keepAlive_1442_;
v___y_1273_ = v_config_1438_;
v___y_1274_ = v_state_1432_;
v___y_1275_ = v_outputData_1431_;
v___y_1276_ = v_knownSize_1433_;
v___y_1277_ = v_messageHead_1434_;
v___y_1278_ = v_error_1440_;
v___y_1279_ = v_userDataBytes_1437_;
v___y_1280_ = v_userData_1430_;
v___y_1281_ = v_events_1439_;
v___y_1282_ = v_reader_1429_;
v___y_1283_ = v_omitBody_1436_;
v___y_1284_ = v_userClosedBody_1435_;
v___y_1285_ = v___x_1458_;
v___y_1286_ = v_pullBodyStalled_1443_;
v___y_1287_ = v___x_1471_;
goto v___jp_1270_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object* v_body_1528_, lean_object* v_close_1529_, lean_object* v_isClosed_1530_, lean_object* v_line_1531_, lean_object* v___f_1532_, lean_object* v_machine_1533_, lean_object* v_x_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(v_body_1528_, v_close_1529_, v_isClosed_1530_, v_line_1531_, v___f_1532_, v_machine_1533_, v_x_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1538_, lean_object* v_machine_1539_, lean_object* v_res_1540_){
_start:
{
lean_object* v_close_1542_; lean_object* v_isClosed_1543_; lean_object* v_getKnownSize_1544_; lean_object* v_line_1545_; lean_object* v_body_1546_; lean_object* v___f_1547_; lean_object* v___f_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_close_1542_ = lean_ctor_get(v_inst_1538_, 1);
lean_inc_ref(v_close_1542_);
v_isClosed_1543_ = lean_ctor_get(v_inst_1538_, 2);
lean_inc_ref(v_isClosed_1543_);
v_getKnownSize_1544_ = lean_ctor_get(v_inst_1538_, 5);
lean_inc_ref(v_getKnownSize_1544_);
lean_dec_ref(v_inst_1538_);
v_line_1545_ = lean_ctor_get(v_res_1540_, 0);
lean_inc_ref(v_line_1545_);
v_body_1546_ = lean_ctor_get(v_res_1540_, 1);
lean_inc_n(v_body_1546_, 2);
lean_dec_ref(v_res_1540_);
v___f_1547_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___closed__0));
v___f_1548_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed), 8, 6);
lean_closure_set(v___f_1548_, 0, v_body_1546_);
lean_closure_set(v___f_1548_, 1, v_close_1542_);
lean_closure_set(v___f_1548_, 2, v_isClosed_1543_);
lean_closure_set(v___f_1548_, 3, v_line_1545_);
lean_closure_set(v___f_1548_, 4, v___f_1547_);
lean_closure_set(v___f_1548_, 5, v_machine_1539_);
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = 0;
v___x_1551_ = lean_apply_2(v_getKnownSize_1544_, v_body_1546_, lean_box(0));
v___x_1552_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1549_, v___x_1550_, v___x_1551_, v___f_1548_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1553_, lean_object* v_machine_1554_, lean_object* v_res_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1553_, v_machine_1554_, v_res_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1558_, lean_object* v_inst_1559_, lean_object* v_machine_1560_, lean_object* v_res_1561_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1559_, v_machine_1560_, v_res_1561_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1564_, lean_object* v_inst_1565_, lean_object* v_machine_1566_, lean_object* v_res_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1564_, v_inst_1565_, v_machine_1566_, v_res_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl___redArg(lean_object* v_x_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_obj_tag_nat(v_x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl___redArg___boxed(lean_object* v_x_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl___redArg(v_x_1572_);
lean_dec(v_x_1572_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl(lean_object* v_00_u03b2_1574_, lean_object* v_x_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_obj_tag_nat(v_x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl___boxed(lean_object* v_00_u03b2_1577_, lean_object* v_x_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl(v_00_u03b2_1577_, v_x_1578_);
lean_dec(v_x_1578_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(lean_object* v_t_1580_, lean_object* v_k_1581_){
_start:
{
if (lean_obj_tag(v_t_1580_) == 0)
{
return v_k_1581_;
}
else
{
lean_object* v_task_1582_; lean_object* v___x_1583_; 
v_task_1582_ = lean_ctor_get(v_t_1580_, 0);
lean_inc_ref(v_task_1582_);
lean_dec(v_t_1580_);
v___x_1583_ = lean_apply_1(v_k_1581_, v_task_1582_);
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim(lean_object* v_00_u03b2_1584_, lean_object* v_motive_1585_, lean_object* v_ctorIdx_1586_, lean_object* v_t_1587_, lean_object* v_h_1588_, lean_object* v_k_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1587_, v_k_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___boxed(lean_object* v_00_u03b2_1591_, lean_object* v_motive_1592_, lean_object* v_ctorIdx_1593_, lean_object* v_t_1594_, lean_object* v_h_1595_, lean_object* v_k_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim(v_00_u03b2_1591_, v_motive_1592_, v_ctorIdx_1593_, v_t_1594_, v_h_1595_, v_k_1596_);
lean_dec(v_ctorIdx_1593_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_idle_elim___redArg(lean_object* v_t_1598_, lean_object* v_idle_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1598_, v_idle_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_idle_elim(lean_object* v_00_u03b2_1601_, lean_object* v_motive_1602_, lean_object* v_t_1603_, lean_object* v_h_1604_, lean_object* v_idle_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1603_, v_idle_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_running_elim___redArg(lean_object* v_t_1607_, lean_object* v_running_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1607_, v_running_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_running_elim(lean_object* v_00_u03b2_1610_, lean_object* v_motive_1611_, lean_object* v_t_1612_, lean_object* v_h_1613_, lean_object* v_running_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1612_, v_running_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandoned_elim___redArg(lean_object* v_t_1616_, lean_object* v_abandoned_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1616_, v_abandoned_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandoned_elim(lean_object* v_00_u03b2_1619_, lean_object* v_motive_1620_, lean_object* v_t_1621_, lean_object* v_h_1622_, lean_object* v_abandoned_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1621_, v_abandoned_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg(lean_object* v_x_1625_){
_start:
{
if (lean_obj_tag(v_x_1625_) == 1)
{
uint8_t v___x_1626_; 
v___x_1626_ = 1;
return v___x_1626_;
}
else
{
uint8_t v___x_1627_; 
v___x_1627_ = 0;
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg___boxed(lean_object* v_x_1628_){
_start:
{
uint8_t v_res_1629_; lean_object* v_r_1630_; 
v_res_1629_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg(v_x_1628_);
lean_dec(v_x_1628_);
v_r_1630_ = lean_box(v_res_1629_);
return v_r_1630_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning(lean_object* v_00_u03b2_1631_, lean_object* v_x_1632_){
_start:
{
uint8_t v___x_1633_; 
v___x_1633_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg(v_x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___boxed(lean_object* v_00_u03b2_1634_, lean_object* v_x_1635_){
_start:
{
uint8_t v_res_1636_; lean_object* v_r_1637_; 
v_res_1636_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning(v_00_u03b2_1634_, v_x_1635_);
lean_dec(v_x_1635_);
v_r_1637_ = lean_box(v_res_1636_);
return v_r_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon___redArg(lean_object* v_x_1638_){
_start:
{
if (lean_obj_tag(v_x_1638_) == 1)
{
lean_object* v_task_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_task_1639_ = lean_ctor_get(v_x_1638_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_x_1638_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v_x_1638_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_task_1639_);
lean_dec(v_x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 2);
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_task_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
else
{
return v_x_1638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon(lean_object* v_00_u03b2_1647_, lean_object* v_x_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon___redArg(v_x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_task_x3f___redArg(lean_object* v_x_1650_){
_start:
{
switch(lean_obj_tag(v_x_1650_))
{
case 0:
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_box(0);
return v___x_1651_;
}
case 1:
{
lean_object* v_task_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
v_task_1652_ = lean_ctor_get(v_x_1650_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_x_1650_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v_x_1650_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_task_1652_);
lean_dec(v_x_1650_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_task_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
default: 
{
lean_object* v_task_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_task_1660_ = lean_ctor_get(v_x_1650_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_x_1650_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v_x_1650_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_task_1660_);
lean_dec(v_x_1650_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set_tag(v___x_1662_, 1);
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_task_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_task_x3f(lean_object* v_00_u03b2_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_task_x3f___redArg(v_x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0(lean_object* v_x_1671_, lean_object* v_x_1672_){
_start:
{
if (lean_obj_tag(v_x_1671_) == 0)
{
if (lean_obj_tag(v_x_1672_) == 0)
{
uint8_t v___x_1673_; 
v___x_1673_ = 1;
return v___x_1673_;
}
else
{
uint8_t v___x_1674_; 
v___x_1674_ = 0;
return v___x_1674_;
}
}
else
{
if (lean_obj_tag(v_x_1672_) == 0)
{
uint8_t v___x_1675_; 
v___x_1675_ = 0;
return v___x_1675_;
}
else
{
lean_object* v_val_1676_; lean_object* v_val_1677_; uint8_t v___x_1678_; 
v_val_1676_ = lean_ctor_get(v_x_1671_, 0);
v_val_1677_ = lean_ctor_get(v_x_1672_, 0);
v___x_1678_ = lean_int_dec_eq(v_val_1676_, v_val_1677_);
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0___boxed(lean_object* v_x_1679_, lean_object* v_x_1680_){
_start:
{
uint8_t v_res_1681_; lean_object* v_r_1682_; 
v_res_1681_ = l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0(v_x_1679_, v_x_1680_);
lean_dec(v_x_1680_);
lean_dec(v_x_1679_);
v_r_1682_ = lean_box(v_res_1681_);
return v_r_1682_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__2(lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_nat_to_int(v_a_1683_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__3(lean_object* v_a_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Rat_ofInt(v_a_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0(lean_object* v_tz_1687_, lean_object* v___x_1688_, lean_object* v_second_1689_, lean_object* v_nano_1690_, lean_object* v_x_1691_){
_start:
{
lean_object* v_offset_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v_nanos_1696_; lean_object* v___x_1697_; lean_object* v_nanos_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_offset_1692_ = lean_ctor_get(v_tz_1687_, 0);
v___x_1693_ = lean_nat_to_int(v___x_1688_);
v___x_1694_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_1695_ = lean_int_mul(v_second_1689_, v___x_1694_);
v_nanos_1696_ = lean_int_add(v___x_1695_, v_nano_1690_);
lean_dec(v___x_1695_);
v___x_1697_ = lean_int_mul(v_offset_1692_, v___x_1694_);
v_nanos_1698_ = lean_int_add(v___x_1697_, v___x_1693_);
lean_dec(v___x_1693_);
lean_dec(v___x_1697_);
v___x_1699_ = lean_int_add(v_nanos_1696_, v_nanos_1698_);
lean_dec(v_nanos_1698_);
lean_dec(v_nanos_1696_);
v___x_1700_ = l_Std_Time_Duration_ofNanoseconds(v___x_1699_);
lean_dec(v___x_1699_);
v___x_1701_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___boxed(lean_object* v_tz_1702_, lean_object* v___x_1703_, lean_object* v_second_1704_, lean_object* v_nano_1705_, lean_object* v_x_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0(v_tz_1702_, v___x_1703_, v_second_1704_, v_nano_1705_, v_x_1706_);
lean_dec(v_nano_1705_);
lean_dec(v_second_1704_);
lean_dec_ref(v_tz_1702_);
return v_res_1707_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = lean_unsigned_to_nat(0u);
v___x_1709_ = lean_nat_to_int(v___x_1708_);
return v___x_1709_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__2));
v___x_1714_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0);
v___x_1715_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_1714_, v___x_1713_, v___x_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(lean_object* v_config_1716_, lean_object* v_state_1717_){
_start:
{
uint8_t v_generateDate_1719_; 
v_generateDate_1719_ = lean_ctor_get_uint8(v_config_1716_, sizeof(void*)*26 + 1);
if (v_generateDate_1719_ == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_state_1717_);
return v___x_1720_;
}
else
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_get_current_time();
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1786_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1786_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1786_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_second_1726_; lean_object* v_nano_1727_; lean_object* v_machine_1728_; lean_object* v_requestStream_1729_; lean_object* v_timer_1730_; lean_object* v_response_1731_; lean_object* v_respStream_1732_; lean_object* v_inputWanted_1733_; lean_object* v_handler_1734_; lean_object* v_pendingHead_1735_; lean_object* v_dateSecond_1736_; uint8_t v_requestEnded_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v_second_1726_ = lean_ctor_get(v_a_1722_, 0);
v_nano_1727_ = lean_ctor_get(v_a_1722_, 1);
v_machine_1728_ = lean_ctor_get(v_state_1717_, 0);
lean_inc_ref(v_machine_1728_);
v_requestStream_1729_ = lean_ctor_get(v_state_1717_, 1);
v_timer_1730_ = lean_ctor_get(v_state_1717_, 2);
v_response_1731_ = lean_ctor_get(v_state_1717_, 3);
v_respStream_1732_ = lean_ctor_get(v_state_1717_, 4);
v_inputWanted_1733_ = lean_ctor_get(v_state_1717_, 5);
v_handler_1734_ = lean_ctor_get(v_state_1717_, 6);
v_pendingHead_1735_ = lean_ctor_get(v_state_1717_, 7);
v_dateSecond_1736_ = lean_ctor_get(v_state_1717_, 8);
v_requestEnded_1737_ = lean_ctor_get_uint8(v_state_1717_, sizeof(void*)*9);
lean_inc(v_second_1726_);
v___x_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_second_1726_);
v___x_1739_ = l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0(v_dateSecond_1736_, v___x_1738_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1773_; 
lean_inc(v_pendingHead_1735_);
lean_inc(v_handler_1734_);
lean_inc(v_inputWanted_1733_);
lean_inc(v_respStream_1732_);
lean_inc_ref(v_response_1731_);
lean_inc_ref(v_timer_1730_);
lean_inc_ref(v_requestStream_1729_);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_state_1717_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; lean_object* v_unused_1775_; lean_object* v_unused_1776_; lean_object* v_unused_1777_; lean_object* v_unused_1778_; lean_object* v_unused_1779_; lean_object* v_unused_1780_; lean_object* v_unused_1781_; lean_object* v_unused_1782_; 
v_unused_1774_ = lean_ctor_get(v_state_1717_, 8);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v_state_1717_, 7);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_state_1717_, 6);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_state_1717_, 5);
lean_dec(v_unused_1777_);
v_unused_1778_ = lean_ctor_get(v_state_1717_, 4);
lean_dec(v_unused_1778_);
v_unused_1779_ = lean_ctor_get(v_state_1717_, 3);
lean_dec(v_unused_1779_);
v_unused_1780_ = lean_ctor_get(v_state_1717_, 2);
lean_dec(v_unused_1780_);
v_unused_1781_ = lean_ctor_get(v_state_1717_, 1);
lean_dec(v_unused_1781_);
v_unused_1782_ = lean_ctor_get(v_state_1717_, 0);
lean_dec(v_unused_1782_);
v___x_1741_ = v_state_1717_;
v_isShared_1742_ = v_isSharedCheck_1773_;
goto v_resetjp_1740_;
}
else
{
lean_dec(v_state_1717_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1773_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v_reader_1745_; lean_object* v_writer_1746_; lean_object* v_config_1747_; lean_object* v_events_1748_; lean_object* v_error_1749_; uint8_t v_keepAlive_1750_; uint8_t v_pullBodyStalled_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1771_; 
v___x_1743_ = lean_unsigned_to_nat(0u);
v___x_1744_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3);
v_reader_1745_ = lean_ctor_get(v_machine_1728_, 0);
v_writer_1746_ = lean_ctor_get(v_machine_1728_, 1);
v_config_1747_ = lean_ctor_get(v_machine_1728_, 2);
v_events_1748_ = lean_ctor_get(v_machine_1728_, 3);
v_error_1749_ = lean_ctor_get(v_machine_1728_, 4);
v_keepAlive_1750_ = lean_ctor_get_uint8(v_machine_1728_, sizeof(void*)*6);
v_pullBodyStalled_1751_ = lean_ctor_get_uint8(v_machine_1728_, sizeof(void*)*6 + 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_machine_1728_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v_machine_1728_, 5);
lean_dec(v_unused_1772_);
v___x_1753_ = v_machine_1728_;
v_isShared_1754_ = v_isSharedCheck_1771_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_error_1749_);
lean_inc(v_events_1748_);
lean_inc(v_config_1747_);
lean_inc(v_writer_1746_);
lean_inc(v_reader_1745_);
lean_dec(v_machine_1728_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1771_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v_tz_1755_; lean_object* v___f_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
v_tz_1755_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_1744_, v_a_1722_);
lean_inc(v_nano_1727_);
lean_inc(v_second_1726_);
lean_inc_ref(v_tz_1755_);
v___f_1756_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1756_, 0, v_tz_1755_);
lean_closure_set(v___f_1756_, 1, v___x_1743_);
lean_closure_set(v___f_1756_, 2, v_second_1726_);
lean_closure_set(v___f_1756_, 3, v_nano_1727_);
v___x_1757_ = lean_mk_thunk(v___f_1756_);
v___x_1758_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v_a_1722_);
lean_ctor_set(v___x_1758_, 2, v___x_1744_);
lean_ctor_set(v___x_1758_, 3, v_tz_1755_);
v___x_1759_ = l_Std_Time_DateTime_toHTTPDateString(v___x_1758_);
v___x_1760_ = l_Std_Http_Header_Value_ofString_x21(v___x_1759_);
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 5, v___x_1761_);
v___x_1763_ = v___x_1753_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_reader_1745_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_writer_1746_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_config_1747_);
lean_ctor_set(v_reuseFailAlloc_1770_, 3, v_events_1748_);
lean_ctor_set(v_reuseFailAlloc_1770_, 4, v_error_1749_);
lean_ctor_set(v_reuseFailAlloc_1770_, 5, v___x_1761_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*6, v_keepAlive_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*6 + 1, v_pullBodyStalled_1751_);
v___x_1763_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1765_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 8, v___x_1738_);
lean_ctor_set(v___x_1741_, 0, v___x_1763_);
v___x_1765_ = v___x_1741_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_requestStream_1729_);
lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_timer_1730_);
lean_ctor_set(v_reuseFailAlloc_1769_, 3, v_response_1731_);
lean_ctor_set(v_reuseFailAlloc_1769_, 4, v_respStream_1732_);
lean_ctor_set(v_reuseFailAlloc_1769_, 5, v_inputWanted_1733_);
lean_ctor_set(v_reuseFailAlloc_1769_, 6, v_handler_1734_);
lean_ctor_set(v_reuseFailAlloc_1769_, 7, v_pendingHead_1735_);
lean_ctor_set(v_reuseFailAlloc_1769_, 8, v___x_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*9, v_requestEnded_1737_);
v___x_1765_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1767_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1765_);
v___x_1767_ = v___x_1724_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
}
else
{
lean_object* v___x_1784_; 
lean_dec_ref_known(v___x_1738_, 1);
lean_dec_ref(v_machine_1728_);
lean_dec(v_a_1722_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v_state_1717_);
v___x_1784_ = v___x_1724_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_state_1717_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v_state_1717_);
v_a_1787_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1721_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1721_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___boxed(lean_object* v_config_1795_, lean_object* v_state_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(v_config_1795_, v_state_1796_);
lean_dec_ref(v_config_1795_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate(lean_object* v_00_u03b2_1799_, lean_object* v_config_1800_, lean_object* v_state_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(v_config_1800_, v_state_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___boxed(lean_object* v_00_u03b2_1804_, lean_object* v_config_1805_, lean_object* v_state_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate(v_00_u03b2_1804_, v_config_1805_, v_state_1806_);
lean_dec_ref(v_config_1805_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__1(lean_object* v_a_1809_){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_nat_to_int(v_a_1809_);
v___x_1811_ = l_Rat_ofInt(v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0(lean_object* v_x_1812_, lean_object* v_x_1813_){
_start:
{
if (lean_obj_tag(v_x_1812_) == 0)
{
if (lean_obj_tag(v_x_1813_) == 0)
{
uint8_t v___x_1814_; 
v___x_1814_ = 1;
return v___x_1814_;
}
else
{
uint8_t v___x_1815_; 
v___x_1815_ = 0;
return v___x_1815_;
}
}
else
{
if (lean_obj_tag(v_x_1813_) == 0)
{
uint8_t v___x_1816_; 
v___x_1816_ = 0;
return v___x_1816_;
}
else
{
lean_object* v_val_1817_; lean_object* v_val_1818_; uint8_t v___x_1819_; 
v_val_1817_ = lean_ctor_get(v_x_1812_, 0);
v_val_1818_ = lean_ctor_get(v_x_1813_, 0);
v___x_1819_ = l_Std_Http_Body_instBEqLength_beq(v_val_1817_, v_val_1818_);
return v___x_1819_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0___boxed(lean_object* v_x_1820_, lean_object* v_x_1821_){
_start:
{
uint8_t v_res_1822_; lean_object* v_r_1823_; 
v_res_1822_ = l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0(v_x_1820_, v_x_1821_);
lean_dec(v_x_1821_);
lean_dec(v_x_1820_);
v_r_1823_ = lean_box(v_res_1822_);
return v_r_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__0(lean_object* v___y_1824_){
_start:
{
if (lean_obj_tag(v___y_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1825_ = lean_ctor_get(v___y_1824_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___y_1824_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___y_1824_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___y_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1841_; 
v_a_1833_ = lean_ctor_get(v___y_1824_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___y_1824_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1835_ = v___y_1824_;
v_isShared_1836_ = v_isSharedCheck_1841_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___y_1824_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1841_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v_fst_1837_; lean_object* v___x_1839_; 
v_fst_1837_ = lean_ctor_get(v_a_1833_, 0);
lean_inc(v_fst_1837_);
lean_dec(v_a_1833_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v_fst_1837_);
v___x_1839_ = v___x_1835_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_fst_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1(lean_object* v_mutex_1842_, lean_object* v_x_1843_){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = lean_io_basemutex_unlock(v_mutex_1842_);
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1___boxed(lean_object* v_mutex_1848_, lean_object* v_x_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1(v_mutex_1848_, v_x_1849_);
lean_dec(v_x_1849_);
lean_dec(v_mutex_1848_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2(lean_object* v_k_1852_, lean_object* v_ref_1853_, lean_object* v_x_1854_){
_start:
{
if (lean_obj_tag(v_x_1854_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_ref_1853_);
lean_dec_ref(v_k_1852_);
v_a_1856_ = lean_ctor_get(v_x_1854_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_x_1854_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1858_ = v_x_1854_;
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v_x_1854_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1864_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
return v___x_1862_;
}
}
}
else
{
lean_object* v___x_1865_; 
lean_dec_ref_known(v_x_1854_, 1);
v___x_1865_ = lean_apply_2(v_k_1852_, v_ref_1853_, lean_box(0));
return v___x_1865_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2___boxed(lean_object* v_k_1866_, lean_object* v_ref_1867_, lean_object* v_x_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2(v_k_1866_, v_ref_1867_, v_x_1868_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3(lean_object* v_mutex_1871_, lean_object* v___f_1872_){
_start:
{
lean_object* v___x_1874_; uint8_t v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1874_ = lean_unsigned_to_nat(0u);
v___x_1875_ = 0;
v___x_1876_ = lean_io_basemutex_lock(v_mutex_1871_);
v___x_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
v___x_1879_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1874_, v___x_1875_, v___x_1878_, v___f_1872_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3___boxed(lean_object* v_mutex_1880_, lean_object* v___f_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3(v_mutex_1880_, v___f_1881_);
lean_dec(v_mutex_1880_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(lean_object* v_mutex_1885_, lean_object* v_k_1886_){
_start:
{
lean_object* v_ref_1888_; lean_object* v_mutex_1889_; lean_object* v___f_1890_; lean_object* v___f_1891_; lean_object* v___f_1892_; lean_object* v___f_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___y_1898_; 
v_ref_1888_ = lean_ctor_get(v_mutex_1885_, 0);
lean_inc(v_ref_1888_);
v_mutex_1889_ = lean_ctor_get(v_mutex_1885_, 1);
lean_inc_n(v_mutex_1889_, 2);
lean_dec_ref(v_mutex_1885_);
v___f_1890_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___closed__0));
v___f_1891_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1891_, 0, v_mutex_1889_);
v___f_1892_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1892_, 0, v_k_1886_);
lean_closure_set(v___f_1892_, 1, v_ref_1888_);
v___f_1893_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1893_, 0, v_mutex_1889_);
lean_closure_set(v___f_1893_, 1, v___f_1892_);
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = 0;
v___x_1896_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1893_, v___f_1891_, v___x_1894_, v___x_1895_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1900_; 
v_a_1900_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1896_, 1);
if (lean_obj_tag(v_a_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
v_a_1901_ = lean_ctor_get(v_a_1900_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_a_1900_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v_a_1900_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v_a_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
v___y_1898_ = v___x_1906_;
goto v___jp_1897_;
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1917_; 
v_a_1909_ = lean_ctor_get(v_a_1900_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_a_1900_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1911_ = v_a_1900_;
v_isShared_1912_ = v_isSharedCheck_1917_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v_a_1900_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1917_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v_fst_1913_; lean_object* v___x_1915_; 
v_fst_1913_ = lean_ctor_get(v_a_1909_, 0);
lean_inc(v_fst_1913_);
lean_dec(v_a_1909_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v_fst_1913_);
v___x_1915_ = v___x_1911_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_fst_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
v___y_1898_ = v___x_1915_;
goto v___jp_1897_;
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1926_; 
v_a_1918_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1920_ = v___x_1896_;
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1896_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1922_ = lean_task_map(v___f_1890_, v_a_1918_, v___x_1894_, v___x_1895_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1922_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
v___jp_1897_:
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___y_1898_);
return v___x_1899_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___boxed(lean_object* v_mutex_1927_, lean_object* v_k_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(v_mutex_1927_, v_k_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1(lean_object* v_00_u03b1_1931_, lean_object* v_00_u03b2_1932_, lean_object* v_mutex_1933_, lean_object* v_k_1934_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(v_mutex_1933_, v_k_1934_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___boxed(lean_object* v_00_u03b1_1937_, lean_object* v_00_u03b2_1938_, lean_object* v_mutex_1939_, lean_object* v_k_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1(v_00_u03b1_1937_, v_00_u03b2_1938_, v_mutex_1939_, v_k_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0(lean_object* v_x_1943_){
_start:
{
if (lean_obj_tag(v_x_1943_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1953_; 
v_a_1945_ = lean_ctor_get(v_x_1943_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_x_1943_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1947_ = v_x_1943_;
v_isShared_1948_ = v_isSharedCheck_1953_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v_x_1943_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1953_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1963_; 
v_a_1954_ = lean_ctor_get(v_x_1943_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_x_1943_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1956_ = v_x_1943_;
v_isShared_1957_ = v_isSharedCheck_1963_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v_x_1943_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1963_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v_knownSize_1958_; lean_object* v___x_1960_; 
v_knownSize_1958_ = lean_ctor_get(v_a_1954_, 4);
lean_inc(v_knownSize_1958_);
lean_dec(v_a_1954_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v_knownSize_1958_);
v___x_1960_ = v___x_1956_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_knownSize_1958_);
v___x_1960_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0___boxed(lean_object* v_x_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0(v_x_1964_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1(lean_object* v_reason_1971_, lean_object* v_requestStream_1972_, lean_object* v_x_1973_){
_start:
{
if (lean_obj_tag(v_x_1973_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1983_; 
lean_dec_ref(v_requestStream_1972_);
lean_dec_ref(v_reason_1971_);
v_a_1975_ = lean_ctor_get(v_x_1973_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_x_1973_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1977_ = v_x_1973_;
v_isShared_1978_ = v_isSharedCheck_1983_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v_x_1973_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1983_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v_a_1984_ = lean_ctor_get(v_x_1973_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v_x_1973_, 1);
v___x_1985_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___closed__1));
v___x_1986_ = l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0(v_a_1984_, v___x_1985_);
lean_dec(v_a_1984_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1987_, 0, v_reason_1971_);
v___x_1988_ = l_Std_Http_Body_Stream_closeWithError(v_requestStream_1972_, v___x_1987_);
return v___x_1988_;
}
else
{
lean_object* v___x_1989_; 
lean_dec_ref(v_reason_1971_);
v___x_1989_ = l_Std_Http_Body_Stream_close(v_requestStream_1972_);
return v___x_1989_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___boxed(lean_object* v_reason_1990_, lean_object* v_requestStream_1991_, lean_object* v_x_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1(v_reason_1990_, v_requestStream_1991_, v_x_1992_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2(lean_object* v___x_1995_, uint8_t v_a_1996_, lean_object* v___f_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2000_ = lean_st_ref_get(v___y_1998_);
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
v___x_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
v___x_2003_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1995_, v_a_1996_, v___x_2002_, v___f_1997_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___boxed(lean_object* v___x_2004_, lean_object* v_a_2005_, lean_object* v___f_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
uint8_t v_a_2006__boxed_2009_; lean_object* v_res_2010_; 
v_a_2006__boxed_2009_ = lean_unbox(v_a_2005_);
v_res_2010_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2(v___x_2004_, v_a_2006__boxed_2009_, v___f_2006_, v___y_2007_);
lean_dec(v___y_2007_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3(lean_object* v___f_2011_, lean_object* v_requestStream_2012_, lean_object* v___f_2013_, lean_object* v_x_2014_){
_start:
{
if (lean_obj_tag(v_x_2014_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref(v___f_2013_);
lean_dec_ref(v_requestStream_2012_);
lean_dec_ref(v___f_2011_);
v_a_2016_ = lean_ctor_get(v_x_2014_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_x_2014_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2018_ = v_x_2014_;
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v_x_2014_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
}
}
else
{
lean_object* v_a_2025_; uint8_t v___x_2026_; 
v_a_2025_ = lean_ctor_get(v_x_2014_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v_x_2014_, 1);
v___x_2026_ = lean_unbox(v_a_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___f_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2027_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_2025_);
v___f_2028_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_2028_, 0, v___x_2027_);
lean_closure_set(v___f_2028_, 1, v_a_2025_);
lean_closure_set(v___f_2028_, 2, v___f_2011_);
v___x_2029_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(v_requestStream_2012_, v___f_2028_);
v___x_2030_ = lean_unbox(v_a_2025_);
lean_dec(v_a_2025_);
v___x_2031_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2027_, v___x_2030_, v___x_2029_, v___f_2013_);
return v___x_2031_;
}
else
{
lean_object* v___x_2032_; 
lean_dec(v_a_2025_);
lean_dec_ref(v___f_2013_);
lean_dec_ref(v_requestStream_2012_);
lean_dec_ref(v___f_2011_);
v___x_2032_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_2032_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3___boxed(lean_object* v___f_2033_, lean_object* v_requestStream_2034_, lean_object* v___f_2035_, lean_object* v_x_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3(v___f_2033_, v_requestStream_2034_, v___f_2035_, v_x_2036_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4(uint8_t v___x_2039_, lean_object* v_x_2040_){
_start:
{
uint8_t v___y_2043_; 
if (lean_obj_tag(v_x_2040_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2055_; 
v_a_2047_ = lean_ctor_get(v_x_2040_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_x_2040_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2049_ = v_x_2040_;
v_isShared_2050_ = v_isSharedCheck_2055_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v_x_2040_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2055_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v_ended_2057_; 
v_a_2056_ = lean_ctor_get(v_x_2040_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v_x_2040_, 1);
v_ended_2057_ = lean_ctor_get(v_a_2056_, 3);
lean_inc(v_ended_2057_);
lean_dec(v_a_2056_);
if (lean_obj_tag(v_ended_2057_) == 0)
{
v___y_2043_ = v___x_2039_;
goto v___jp_2042_;
}
else
{
uint8_t v___x_2058_; 
lean_dec_ref_known(v_ended_2057_, 1);
v___x_2058_ = 1;
v___y_2043_ = v___x_2058_;
goto v___jp_2042_;
}
}
v___jp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_box(v___y_2043_);
v___x_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4___boxed(lean_object* v___x_2059_, lean_object* v_x_2060_, lean_object* v___y_2061_){
_start:
{
uint8_t v___x_2080__boxed_2062_; lean_object* v_res_2063_; 
v___x_2080__boxed_2062_ = lean_unbox(v___x_2059_);
v_res_2063_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4(v___x_2080__boxed_2062_, v_x_2060_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5(lean_object* v___x_2064_, uint8_t v___x_2065_, lean_object* v___f_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2069_ = lean_st_ref_get(v___y_2067_);
v___x_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
v___x_2072_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2064_, v___x_2065_, v___x_2071_, v___f_2066_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5___boxed(lean_object* v___x_2073_, lean_object* v___x_2074_, lean_object* v___f_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
uint8_t v___x_2123__boxed_2078_; lean_object* v_res_2079_; 
v___x_2123__boxed_2078_ = lean_unbox(v___x_2074_);
v_res_2079_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5(v___x_2073_, v___x_2123__boxed_2078_, v___f_2075_, v___y_2076_);
lean_dec(v___y_2076_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(lean_object* v_state_2089_, lean_object* v_reason_2090_){
_start:
{
lean_object* v_requestStream_2092_; lean_object* v___f_2093_; lean_object* v___f_2094_; lean_object* v___f_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; lean_object* v___f_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_requestStream_2092_ = lean_ctor_get(v_state_2089_, 1);
lean_inc_ref_n(v_requestStream_2092_, 3);
lean_dec_ref(v_state_2089_);
v___f_2093_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__0));
v___f_2094_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2094_, 0, v_reason_2090_);
lean_closure_set(v___f_2094_, 1, v_requestStream_2092_);
v___f_2095_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2095_, 0, v___f_2093_);
lean_closure_set(v___f_2095_, 1, v_requestStream_2092_);
lean_closure_set(v___f_2095_, 2, v___f_2094_);
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = 0;
v___f_2098_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__2));
v___x_2099_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(v_requestStream_2092_, v___f_2098_);
v___x_2100_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2096_, v___x_2097_, v___x_2099_, v___f_2095_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___boxed(lean_object* v_state_2101_, lean_object* v_reason_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v_state_2101_, v_reason_2102_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream(lean_object* v_00_u03b2_2105_, lean_object* v_state_2106_, lean_object* v_reason_2107_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v_state_2106_, v_reason_2107_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___boxed(lean_object* v_00_u03b2_2110_, lean_object* v_state_2111_, lean_object* v_reason_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream(v_00_u03b2_2110_, v_state_2111_, v_reason_2112_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v___x_2115_, lean_object* v_x_2116_){
_start:
{
if (lean_obj_tag(v_x_2116_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2126_; 
lean_dec_ref(v___x_2115_);
v_a_2118_ = lean_ctor_get(v_x_2116_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_x_2116_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2120_ = v_x_2116_;
v_isShared_2121_ = v_isSharedCheck_2126_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v_x_2116_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2126_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
}
}
else
{
lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2135_; 
v_isSharedCheck_2135_ = !lean_is_exclusive(v_x_2116_);
if (v_isSharedCheck_2135_ == 0)
{
lean_object* v_unused_2136_; 
v_unused_2136_ = lean_ctor_get(v_x_2116_, 0);
lean_dec(v_unused_2136_);
v___x_2128_ = v_x_2116_;
v_isShared_2129_ = v_isSharedCheck_2135_;
goto v_resetjp_2127_;
}
else
{
lean_dec(v_x_2116_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2135_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2115_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2130_);
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2133_; 
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
return v___x_2133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v___x_2137_, lean_object* v_x_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v___x_2137_, v_x_2138_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; lean_object* v_pendingProducer_2145_; lean_object* v_pendingConsumer_2146_; lean_object* v_interestWaiter_2147_; lean_object* v_ended_2148_; lean_object* v_pendingIncomplete_2149_; uint8_t v_closeAfterProducer_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2159_; 
v___x_2144_ = lean_st_ref_take(v___y_2142_);
v_pendingProducer_2145_ = lean_ctor_get(v___x_2144_, 0);
v_pendingConsumer_2146_ = lean_ctor_get(v___x_2144_, 1);
v_interestWaiter_2147_ = lean_ctor_get(v___x_2144_, 2);
v_ended_2148_ = lean_ctor_get(v___x_2144_, 3);
v_pendingIncomplete_2149_ = lean_ctor_get(v___x_2144_, 5);
v_closeAfterProducer_2150_ = lean_ctor_get_uint8(v___x_2144_, sizeof(void*)*6);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; 
v_unused_2160_ = lean_ctor_get(v___x_2144_, 4);
lean_dec(v_unused_2160_);
v___x_2152_ = v___x_2144_;
v_isShared_2153_ = v_isSharedCheck_2159_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_pendingIncomplete_2149_);
lean_inc(v_ended_2148_);
lean_inc(v_interestWaiter_2147_);
lean_inc(v_pendingConsumer_2146_);
lean_inc(v_pendingProducer_2145_);
lean_dec(v___x_2144_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2159_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 4, v___x_2141_);
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_pendingProducer_2145_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_pendingConsumer_2146_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v_interestWaiter_2147_);
lean_ctor_set(v_reuseFailAlloc_2158_, 3, v_ended_2148_);
lean_ctor_set(v_reuseFailAlloc_2158_, 4, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2158_, 5, v_pendingIncomplete_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, sizeof(void*)*6, v_closeAfterProducer_2150_);
v___x_2155_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_st_ref_put(v___y_2142_, v___x_2155_);
v___x_2157_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_2157_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_2161_, v___y_2162_);
lean_dec(v___y_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v___y_2165_, lean_object* v_x_2166_){
_start:
{
if (lean_obj_tag(v_x_2166_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2176_; 
lean_dec_ref(v___y_2165_);
v_a_2168_ = lean_ctor_get(v_x_2166_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_x_2166_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2170_ = v_x_2166_;
v_isShared_2171_ = v_isSharedCheck_2176_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v_x_2166_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2176_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
return v___x_2174_;
}
}
}
else
{
lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2203_; 
v_isSharedCheck_2203_ = !lean_is_exclusive(v_x_2166_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; 
v_unused_2204_ = lean_ctor_get(v_x_2166_, 0);
lean_dec(v_unused_2204_);
v___x_2178_ = v_x_2166_;
v_isShared_2179_ = v_isSharedCheck_2203_;
goto v_resetjp_2177_;
}
else
{
lean_dec(v_x_2166_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2203_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v_machine_2180_; lean_object* v_requestStream_2181_; lean_object* v_timer_2182_; lean_object* v_response_2183_; lean_object* v_respStream_2184_; lean_object* v_handler_2185_; lean_object* v_dateSecond_2186_; uint8_t v_requestEnded_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2200_; 
v_machine_2180_ = lean_ctor_get(v___y_2165_, 0);
v_requestStream_2181_ = lean_ctor_get(v___y_2165_, 1);
v_timer_2182_ = lean_ctor_get(v___y_2165_, 2);
v_response_2183_ = lean_ctor_get(v___y_2165_, 3);
v_respStream_2184_ = lean_ctor_get(v___y_2165_, 4);
v_handler_2185_ = lean_ctor_get(v___y_2165_, 6);
v_dateSecond_2186_ = lean_ctor_get(v___y_2165_, 8);
v_requestEnded_2187_ = lean_ctor_get_uint8(v___y_2165_, sizeof(void*)*9);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___y_2165_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; lean_object* v_unused_2202_; 
v_unused_2201_ = lean_ctor_get(v___y_2165_, 7);
lean_dec(v_unused_2201_);
v_unused_2202_ = lean_ctor_get(v___y_2165_, 5);
lean_dec(v_unused_2202_);
v___x_2189_ = v___y_2165_;
v_isShared_2190_ = v_isSharedCheck_2200_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_dateSecond_2186_);
lean_inc(v_handler_2185_);
lean_inc(v_respStream_2184_);
lean_inc(v_response_2183_);
lean_inc(v_timer_2182_);
lean_inc(v_requestStream_2181_);
lean_inc(v_machine_2180_);
lean_dec(v___y_2165_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2200_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___x_2193_; 
v___x_2191_ = lean_box(0);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 7, v___x_2191_);
lean_ctor_set(v___x_2189_, 5, v___x_2191_);
v___x_2193_ = v___x_2189_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_machine_2180_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_requestStream_2181_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_timer_2182_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v_response_2183_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v_respStream_2184_);
lean_ctor_set(v_reuseFailAlloc_2199_, 5, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2199_, 6, v_handler_2185_);
lean_ctor_set(v_reuseFailAlloc_2199_, 7, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2199_, 8, v_dateSecond_2186_);
lean_ctor_set_uint8(v_reuseFailAlloc_2199_, sizeof(void*)*9, v_requestEnded_2187_);
v___x_2193_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2194_);
v___x_2196_ = v___x_2178_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
return v___x_2197_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v___y_2205_, lean_object* v_x_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v___y_2205_, v_x_2206_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___f_2212_, lean_object* v_x_2213_){
_start:
{
if (lean_obj_tag(v_x_2213_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2223_; 
lean_dec_ref(v___f_2212_);
lean_dec_ref(v___y_2211_);
v_a_2215_ = lean_ctor_get(v_x_2213_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_x_2213_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2217_ = v_x_2213_;
v_isShared_2218_ = v_isSharedCheck_2223_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v_x_2213_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2223_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec_ref_known(v_x_2213_, 1);
v___x_2224_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0));
v___x_2225_ = lean_string_append(v___x_2224_, v___y_2210_);
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = 0;
v___x_2228_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v___y_2211_, v___x_2225_);
v___x_2229_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2226_, v___x_2227_, v___x_2228_, v___f_2212_);
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___f_2232_, lean_object* v_x_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___y_2230_, v___y_2231_, v___f_2232_, v_x_2233_);
lean_dec_ref(v___y_2230_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___y_2236_, lean_object* v_x_2237_){
_start:
{
if (lean_obj_tag(v_x_2237_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2247_; 
lean_dec_ref(v___y_2236_);
v_a_2239_ = lean_ctor_get(v_x_2237_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_x_2237_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2241_ = v_x_2237_;
v_isShared_2242_ = v_isSharedCheck_2247_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v_x_2237_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2247_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
}
}
else
{
lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2273_; 
v_isSharedCheck_2273_ = !lean_is_exclusive(v_x_2237_);
if (v_isSharedCheck_2273_ == 0)
{
lean_object* v_unused_2274_; 
v_unused_2274_ = lean_ctor_get(v_x_2237_, 0);
lean_dec(v_unused_2274_);
v___x_2249_ = v_x_2237_;
v_isShared_2250_ = v_isSharedCheck_2273_;
goto v_resetjp_2248_;
}
else
{
lean_dec(v_x_2237_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2273_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v_machine_2251_; lean_object* v_requestStream_2252_; lean_object* v_timer_2253_; lean_object* v_response_2254_; lean_object* v_respStream_2255_; lean_object* v_inputWanted_2256_; lean_object* v_handler_2257_; lean_object* v_pendingHead_2258_; lean_object* v_dateSecond_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2272_; 
v_machine_2251_ = lean_ctor_get(v___y_2236_, 0);
v_requestStream_2252_ = lean_ctor_get(v___y_2236_, 1);
v_timer_2253_ = lean_ctor_get(v___y_2236_, 2);
v_response_2254_ = lean_ctor_get(v___y_2236_, 3);
v_respStream_2255_ = lean_ctor_get(v___y_2236_, 4);
v_inputWanted_2256_ = lean_ctor_get(v___y_2236_, 5);
v_handler_2257_ = lean_ctor_get(v___y_2236_, 6);
v_pendingHead_2258_ = lean_ctor_get(v___y_2236_, 7);
v_dateSecond_2259_ = lean_ctor_get(v___y_2236_, 8);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___y_2236_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2261_ = v___y_2236_;
v_isShared_2262_ = v_isSharedCheck_2272_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_dateSecond_2259_);
lean_inc(v_pendingHead_2258_);
lean_inc(v_handler_2257_);
lean_inc(v_inputWanted_2256_);
lean_inc(v_respStream_2255_);
lean_inc(v_response_2254_);
lean_inc(v_timer_2253_);
lean_inc(v_requestStream_2252_);
lean_inc(v_machine_2251_);
lean_dec(v___y_2236_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2272_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
uint8_t v___x_2263_; lean_object* v___x_2265_; 
v___x_2263_ = 1;
if (v_isShared_2262_ == 0)
{
v___x_2265_ = v___x_2261_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_machine_2251_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_requestStream_2252_);
lean_ctor_set(v_reuseFailAlloc_2271_, 2, v_timer_2253_);
lean_ctor_set(v_reuseFailAlloc_2271_, 3, v_response_2254_);
lean_ctor_set(v_reuseFailAlloc_2271_, 4, v_respStream_2255_);
lean_ctor_set(v_reuseFailAlloc_2271_, 5, v_inputWanted_2256_);
lean_ctor_set(v_reuseFailAlloc_2271_, 6, v_handler_2257_);
lean_ctor_set(v_reuseFailAlloc_2271_, 7, v_pendingHead_2258_);
lean_ctor_set(v_reuseFailAlloc_2271_, 8, v_dateSecond_2259_);
v___x_2265_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*9, v___x_2263_);
v___x_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2266_);
v___x_2268_ = v___x_2249_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___y_2275_, lean_object* v_x_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___y_2275_, v_x_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v___y_2279_, lean_object* v_config_2280_, lean_object* v_a_2281_, lean_object* v_x_2282_){
_start:
{
if (lean_obj_tag(v_x_2282_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2292_; 
lean_dec_ref(v_a_2281_);
lean_dec_ref(v___y_2279_);
v_a_2284_ = lean_ctor_get(v_x_2282_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_x_2282_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2286_ = v_x_2282_;
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v_x_2282_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
return v___x_2290_;
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2323_; 
v_a_2293_ = lean_ctor_get(v_x_2282_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_x_2282_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2295_ = v_x_2282_;
v_isShared_2296_ = v_isSharedCheck_2323_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v_x_2282_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2323_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v_machine_2297_; lean_object* v_inputWanted_2298_; lean_object* v_handler_2299_; lean_object* v_pendingHead_2300_; lean_object* v_dateSecond_2301_; uint8_t v_requestEnded_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2318_; 
v_machine_2297_ = lean_ctor_get(v___y_2279_, 0);
v_inputWanted_2298_ = lean_ctor_get(v___y_2279_, 5);
v_handler_2299_ = lean_ctor_get(v___y_2279_, 6);
v_pendingHead_2300_ = lean_ctor_get(v___y_2279_, 7);
v_dateSecond_2301_ = lean_ctor_get(v___y_2279_, 8);
v_requestEnded_2302_ = lean_ctor_get_uint8(v___y_2279_, sizeof(void*)*9);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___y_2279_);
if (v_isSharedCheck_2318_ == 0)
{
lean_object* v_unused_2319_; lean_object* v_unused_2320_; lean_object* v_unused_2321_; lean_object* v_unused_2322_; 
v_unused_2319_ = lean_ctor_get(v___y_2279_, 4);
lean_dec(v_unused_2319_);
v_unused_2320_ = lean_ctor_get(v___y_2279_, 3);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v___y_2279_, 2);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v___y_2279_, 1);
lean_dec(v_unused_2322_);
v___x_2304_ = v___y_2279_;
v_isShared_2305_ = v_isSharedCheck_2318_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_dateSecond_2301_);
lean_inc(v_pendingHead_2300_);
lean_inc(v_handler_2299_);
lean_inc(v_inputWanted_2298_);
lean_inc(v_machine_2297_);
lean_dec(v___y_2279_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2318_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v_keepAliveTimeout_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2311_; 
v_keepAliveTimeout_2306_ = lean_ctor_get(v_config_2280_, 5);
lean_inc(v_keepAliveTimeout_2306_);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v_keepAliveTimeout_2306_);
v___x_2308_ = lean_box(0);
v___x_2309_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon___redArg(v_handler_2299_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 6, v___x_2309_);
lean_ctor_set(v___x_2304_, 4, v___x_2308_);
lean_ctor_set(v___x_2304_, 3, v_a_2293_);
lean_ctor_set(v___x_2304_, 2, v___x_2307_);
lean_ctor_set(v___x_2304_, 1, v_a_2281_);
v___x_2311_ = v___x_2304_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_machine_2297_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_a_2281_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2317_, 3, v_a_2293_);
lean_ctor_set(v_reuseFailAlloc_2317_, 4, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2317_, 5, v_inputWanted_2298_);
lean_ctor_set(v_reuseFailAlloc_2317_, 6, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2317_, 7, v_pendingHead_2300_);
lean_ctor_set(v_reuseFailAlloc_2317_, 8, v_dateSecond_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2317_, sizeof(void*)*9, v_requestEnded_2302_);
v___x_2311_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2312_);
v___x_2314_ = v___x_2295_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
return v___x_2315_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v___y_2324_, lean_object* v_config_2325_, lean_object* v_a_2326_, lean_object* v_x_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v___y_2324_, v_config_2325_, v_a_2326_, v_x_2327_);
lean_dec_ref(v_config_2325_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_2330_, lean_object* v_config_2331_, lean_object* v_x_2332_){
_start:
{
if (lean_obj_tag(v_x_2332_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v_config_2331_);
lean_dec_ref(v___y_2330_);
v_a_2334_ = lean_ctor_get(v_x_2332_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_x_2332_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2336_ = v_x_2332_;
v_isShared_2337_ = v_isSharedCheck_2342_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v_x_2332_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2342_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; 
v___x_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
return v___x_2340_;
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2357_; 
v_a_2343_ = lean_ctor_get(v_x_2332_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_x_2332_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2345_ = v_x_2332_;
v_isShared_2346_ = v_isSharedCheck_2357_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v_x_2332_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2357_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___f_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___f_2347_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2347_, 0, v___y_2330_);
lean_closure_set(v___f_2347_, 1, v_config_2331_);
lean_closure_set(v___f_2347_, 2, v_a_2343_);
v___x_2348_ = lean_box(0);
v___x_2349_ = lean_unsigned_to_nat(0u);
v___x_2350_ = 0;
v___x_2351_ = l_Std_CloseableChannel_new___redArg(v___x_2348_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2351_);
v___x_2353_ = v___x_2345_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
v___x_2355_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2349_, v___x_2350_, v___x_2354_, v___f_2347_);
return v___x_2355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_2358_, lean_object* v_config_2359_, lean_object* v_x_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_2358_, v_config_2359_, v_x_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___f_2363_, lean_object* v_____r_2364_){
_start:
{
lean_object* v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = 0;
v___x_2368_ = l_Std_Http_Body_mkStream();
v___x_2369_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2366_, v___x_2367_, v___x_2368_, v___f_2363_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___f_2370_, lean_object* v_____r_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v_res_2373_; 
v_res_2373_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___f_2370_, v_____r_2371_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v___f_2374_, lean_object* v_x_2375_){
_start:
{
if (lean_obj_tag(v_x_2375_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2385_; 
lean_dec_ref(v___f_2374_);
v_a_2377_ = lean_ctor_get(v_x_2375_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_x_2375_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2379_ = v_x_2375_;
v_isShared_2380_ = v_isSharedCheck_2385_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v_x_2375_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2385_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2383_; 
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2387_; 
v_a_2386_ = lean_ctor_get(v_x_2375_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v_x_2375_, 1);
v___x_2387_ = lean_apply_2(v___f_2374_, v_a_2386_, lean_box(0));
return v___x_2387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v___f_2388_, lean_object* v_x_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v___f_2388_, v_x_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_close_2392_, lean_object* v_val_2393_, lean_object* v___f_2394_, lean_object* v___f_2395_, lean_object* v_x_2396_){
_start:
{
if (lean_obj_tag(v_x_2396_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v___f_2395_);
lean_dec_ref(v___f_2394_);
lean_dec(v_val_2393_);
lean_dec_ref(v_close_2392_);
v_a_2398_ = lean_ctor_get(v_x_2396_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_x_2396_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2400_ = v_x_2396_;
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v_x_2396_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2406_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
return v___x_2404_;
}
}
}
else
{
lean_object* v_a_2407_; uint8_t v___x_2408_; 
v_a_2407_ = lean_ctor_get(v_x_2396_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v_x_2396_, 1);
v___x_2408_ = lean_unbox(v_a_2407_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; lean_object* v___x_2412_; 
lean_dec_ref(v___f_2395_);
v___x_2409_ = lean_unsigned_to_nat(0u);
v___x_2410_ = lean_apply_2(v_close_2392_, v_val_2393_, lean_box(0));
v___x_2411_ = lean_unbox(v_a_2407_);
lean_dec(v_a_2407_);
v___x_2412_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2409_, v___x_2411_, v___x_2410_, v___f_2394_);
return v___x_2412_;
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
lean_dec(v_a_2407_);
lean_dec_ref(v___f_2394_);
lean_dec(v_val_2393_);
lean_dec_ref(v_close_2392_);
v___x_2413_ = lean_box(0);
v___x_2414_ = lean_apply_2(v___f_2395_, v___x_2413_, lean_box(0));
return v___x_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_close_2415_, lean_object* v_val_2416_, lean_object* v___f_2417_, lean_object* v___f_2418_, lean_object* v_x_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_close_2415_, v_val_2416_, v___f_2417_, v___f_2418_, v_x_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v___y_2422_, lean_object* v_inst_2423_, lean_object* v___f_2424_, lean_object* v___f_2425_, lean_object* v_x_2426_){
_start:
{
if (lean_obj_tag(v_x_2426_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2436_; 
lean_dec_ref(v___f_2425_);
lean_dec_ref(v___f_2424_);
lean_dec_ref(v_inst_2423_);
lean_dec_ref(v___y_2422_);
v_a_2428_ = lean_ctor_get(v_x_2426_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_x_2426_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2430_ = v_x_2426_;
v_isShared_2431_ = v_isSharedCheck_2436_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v_x_2426_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2436_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
return v___x_2434_;
}
}
}
else
{
lean_object* v_respStream_2437_; 
lean_dec_ref_known(v_x_2426_, 1);
v_respStream_2437_ = lean_ctor_get(v___y_2422_, 4);
lean_inc(v_respStream_2437_);
lean_dec_ref(v___y_2422_);
if (lean_obj_tag(v_respStream_2437_) == 1)
{
lean_object* v_val_2438_; lean_object* v_close_2439_; lean_object* v_isClosed_2440_; lean_object* v___f_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_val_2438_ = lean_ctor_get(v_respStream_2437_, 0);
lean_inc_n(v_val_2438_, 2);
lean_dec_ref_known(v_respStream_2437_, 1);
v_close_2439_ = lean_ctor_get(v_inst_2423_, 1);
lean_inc_ref(v_close_2439_);
v_isClosed_2440_ = lean_ctor_get(v_inst_2423_, 2);
lean_inc_ref(v_isClosed_2440_);
lean_dec_ref(v_inst_2423_);
v___f_2441_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_2441_, 0, v_close_2439_);
lean_closure_set(v___f_2441_, 1, v_val_2438_);
lean_closure_set(v___f_2441_, 2, v___f_2424_);
lean_closure_set(v___f_2441_, 3, v___f_2425_);
v___x_2442_ = lean_unsigned_to_nat(0u);
v___x_2443_ = 0;
v___x_2444_ = lean_apply_2(v_isClosed_2440_, v_val_2438_, lean_box(0));
v___x_2445_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2442_, v___x_2443_, v___x_2444_, v___f_2441_);
return v___x_2445_;
}
else
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_dec(v_respStream_2437_);
lean_dec_ref(v___f_2424_);
lean_dec_ref(v_inst_2423_);
v___x_2446_ = lean_box(0);
v___x_2447_ = lean_apply_2(v___f_2425_, v___x_2446_, lean_box(0));
return v___x_2447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v___y_2448_, lean_object* v_inst_2449_, lean_object* v___f_2450_, lean_object* v___f_2451_, lean_object* v_x_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v___y_2448_, v_inst_2449_, v___f_2450_, v___f_2451_, v_x_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v_requestStream_2455_, lean_object* v_timer_2456_, lean_object* v_response_2457_, lean_object* v_respStream_2458_, lean_object* v_inputWanted_2459_, lean_object* v_handler_2460_, lean_object* v_pendingHead_2461_, lean_object* v_dateSecond_2462_, uint8_t v_requestEnded_2463_, lean_object* v_x_2464_){
_start:
{
if (lean_obj_tag(v_x_2464_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_dateSecond_2462_);
lean_dec(v_pendingHead_2461_);
lean_dec(v_handler_2460_);
lean_dec(v_inputWanted_2459_);
lean_dec(v_respStream_2458_);
lean_dec_ref(v_response_2457_);
lean_dec_ref(v_timer_2456_);
lean_dec_ref(v_requestStream_2455_);
v_a_2466_ = lean_ctor_get(v_x_2464_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_x_2464_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2468_ = v_x_2464_;
v_isShared_2469_ = v_isSharedCheck_2474_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v_x_2464_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2474_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
return v___x_2472_;
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2496_; 
v_a_2475_ = lean_ctor_get(v_x_2464_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_x_2464_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2477_ = v_x_2464_;
v_isShared_2478_ = v_isSharedCheck_2496_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v_x_2464_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2496_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_snd_2479_; uint8_t v___x_2480_; 
v_snd_2479_ = lean_ctor_get(v_a_2475_, 1);
v___x_2480_ = lean_unbox(v_snd_2479_);
if (v___x_2480_ == 0)
{
lean_object* v_fst_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
v_fst_2481_ = lean_ctor_get(v_a_2475_, 0);
lean_inc(v_fst_2481_);
lean_dec(v_a_2475_);
v___x_2482_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2482_, 0, v_fst_2481_);
lean_ctor_set(v___x_2482_, 1, v_requestStream_2455_);
lean_ctor_set(v___x_2482_, 2, v_timer_2456_);
lean_ctor_set(v___x_2482_, 3, v_response_2457_);
lean_ctor_set(v___x_2482_, 4, v_respStream_2458_);
lean_ctor_set(v___x_2482_, 5, v_inputWanted_2459_);
lean_ctor_set(v___x_2482_, 6, v_handler_2460_);
lean_ctor_set(v___x_2482_, 7, v_pendingHead_2461_);
lean_ctor_set(v___x_2482_, 8, v_dateSecond_2462_);
lean_ctor_set_uint8(v___x_2482_, sizeof(void*)*9, v_requestEnded_2463_);
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2482_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v___x_2483_);
v___x_2485_ = v___x_2477_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; 
v___x_2486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
return v___x_2486_;
}
}
else
{
lean_object* v_fst_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
lean_dec(v_pendingHead_2461_);
v_fst_2488_ = lean_ctor_get(v_a_2475_, 0);
lean_inc(v_fst_2488_);
lean_dec(v_a_2475_);
v___x_2489_ = lean_box(0);
v___x_2490_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2490_, 0, v_fst_2488_);
lean_ctor_set(v___x_2490_, 1, v_requestStream_2455_);
lean_ctor_set(v___x_2490_, 2, v_timer_2456_);
lean_ctor_set(v___x_2490_, 3, v_response_2457_);
lean_ctor_set(v___x_2490_, 4, v_respStream_2458_);
lean_ctor_set(v___x_2490_, 5, v_inputWanted_2459_);
lean_ctor_set(v___x_2490_, 6, v_handler_2460_);
lean_ctor_set(v___x_2490_, 7, v___x_2489_);
lean_ctor_set(v___x_2490_, 8, v_dateSecond_2462_);
lean_ctor_set_uint8(v___x_2490_, sizeof(void*)*9, v_requestEnded_2463_);
v___x_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 0, v___x_2491_);
v___x_2493_ = v___x_2477_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; 
v___x_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
return v___x_2494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v_requestStream_2497_, lean_object* v_timer_2498_, lean_object* v_response_2499_, lean_object* v_respStream_2500_, lean_object* v_inputWanted_2501_, lean_object* v_handler_2502_, lean_object* v_pendingHead_2503_, lean_object* v_dateSecond_2504_, lean_object* v_requestEnded_2505_, lean_object* v_x_2506_, lean_object* v___y_2507_){
_start:
{
uint8_t v_requestEnded_boxed_2508_; lean_object* v_res_2509_; 
v_requestEnded_boxed_2508_ = lean_unbox(v_requestEnded_2505_);
v_res_2509_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v_requestStream_2497_, v_timer_2498_, v_response_2499_, v_respStream_2500_, v_inputWanted_2501_, v_handler_2502_, v_pendingHead_2503_, v_dateSecond_2504_, v_requestEnded_boxed_2508_, v_x_2506_);
return v_res_2509_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_2510_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_2511_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___f_2518_; lean_object* v___f_2519_; 
v___x_2517_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1);
v___f_2518_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__4));
v___f_2519_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2519_, 0, v___f_2518_);
lean_closure_set(v___f_2519_, 1, v___x_2517_);
return v___f_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_config_2536_, lean_object* v_inst_2537_, lean_object* v_handler_2538_, lean_object* v_inst_2539_, lean_object* v_connectionContext_2540_, lean_object* v_a_2541_, lean_object* v_x_2542_, lean_object* v___y_2543_){
_start:
{
switch(lean_obj_tag(v_a_2541_))
{
case 0:
{
lean_object* v_head_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2586_; 
lean_dec_ref(v_connectionContext_2540_);
lean_dec_ref(v_inst_2539_);
lean_dec(v_handler_2538_);
lean_dec_ref(v_inst_2537_);
v_head_2545_ = lean_ctor_get(v_a_2541_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_a_2541_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2547_ = v_a_2541_;
v_isShared_2548_ = v_isSharedCheck_2586_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_head_2545_);
lean_dec(v_a_2541_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2586_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_machine_2549_; lean_object* v_requestStream_2550_; lean_object* v_response_2551_; lean_object* v_respStream_2552_; lean_object* v_inputWanted_2553_; lean_object* v_handler_2554_; lean_object* v_dateSecond_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2583_; 
v_machine_2549_ = lean_ctor_get(v___y_2543_, 0);
v_requestStream_2550_ = lean_ctor_get(v___y_2543_, 1);
v_response_2551_ = lean_ctor_get(v___y_2543_, 3);
v_respStream_2552_ = lean_ctor_get(v___y_2543_, 4);
v_inputWanted_2553_ = lean_ctor_get(v___y_2543_, 5);
v_handler_2554_ = lean_ctor_get(v___y_2543_, 6);
v_dateSecond_2555_ = lean_ctor_get(v___y_2543_, 8);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___y_2543_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; lean_object* v_unused_2585_; 
v_unused_2584_ = lean_ctor_get(v___y_2543_, 7);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v___y_2543_, 2);
lean_dec(v_unused_2585_);
v___x_2557_ = v___y_2543_;
v_isShared_2558_ = v_isSharedCheck_2583_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_dateSecond_2555_);
lean_inc(v_handler_2554_);
lean_inc(v_inputWanted_2553_);
lean_inc(v_respStream_2552_);
lean_inc(v_response_2551_);
lean_inc(v_requestStream_2550_);
lean_inc(v_machine_2549_);
lean_dec(v___y_2543_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2583_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v_lingeringTimeout_2559_; lean_object* v___x_2561_; 
v_lingeringTimeout_2559_ = lean_ctor_get(v_config_2536_, 4);
lean_inc(v_lingeringTimeout_2559_);
lean_dec_ref(v_config_2536_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set_tag(v___x_2547_, 2);
lean_ctor_set(v___x_2547_, 0, v_lingeringTimeout_2559_);
v___x_2561_ = v___x_2547_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_lingeringTimeout_2559_);
v___x_2561_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2565_; 
lean_inc(v_head_2545_);
v___x_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2562_, 0, v_head_2545_);
v___x_2563_ = 0;
lean_inc_ref(v_requestStream_2550_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 7, v___x_2562_);
lean_ctor_set(v___x_2557_, 2, v___x_2561_);
v___x_2565_ = v___x_2557_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_machine_2549_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_requestStream_2550_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v___x_2561_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_response_2551_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v_respStream_2552_);
lean_ctor_set(v_reuseFailAlloc_2581_, 5, v_inputWanted_2553_);
lean_ctor_set(v_reuseFailAlloc_2581_, 6, v_handler_2554_);
lean_ctor_set(v_reuseFailAlloc_2581_, 7, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2581_, 8, v_dateSecond_2555_);
v___x_2565_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
uint8_t v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; 
lean_ctor_set_uint8(v___x_2565_, sizeof(void*)*9, v___x_2563_);
v___x_2566_ = 0;
v___x_2567_ = 1;
v___x_2568_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2566_, v_head_2545_, v___x_2567_);
lean_dec(v_head_2545_);
if (lean_obj_tag(v___x_2568_) == 1)
{
lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___f_2573_; lean_object* v___f_2574_; lean_object* v___x_3964__overap_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___f_2569_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2569_, 0, v___x_2565_);
v___f_2570_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2570_, 0, v___x_2568_);
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0);
v___f_2573_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5);
v___f_2574_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__6));
v___x_3964__overap_2575_ = l_Std_Mutex_atomically___redArg(v___x_2572_, v___f_2573_, v___f_2574_, v_requestStream_2550_, v___f_2570_);
v___x_2576_ = lean_apply_1(v___x_3964__overap_2575_, lean_box(0));
v___x_2577_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2571_, v___x_2563_, v___x_2576_, v___f_2569_);
return v___x_2577_;
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec(v___x_2568_);
lean_dec_ref(v_requestStream_2550_);
v___x_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2565_);
v___x_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
return v___x_2580_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref(v_connectionContext_2540_);
lean_dec_ref(v_inst_2539_);
lean_dec(v_handler_2538_);
lean_dec_ref(v_inst_2537_);
lean_dec_ref(v_config_2536_);
v_size_2587_ = lean_ctor_get(v_a_2541_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_a_2541_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2589_ = v_a_2541_;
v_isShared_2590_ = v_isSharedCheck_2614_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_size_2587_);
lean_dec(v_a_2541_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2614_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_machine_2591_; lean_object* v_requestStream_2592_; lean_object* v_timer_2593_; lean_object* v_response_2594_; lean_object* v_respStream_2595_; lean_object* v_handler_2596_; lean_object* v_pendingHead_2597_; lean_object* v_dateSecond_2598_; uint8_t v_requestEnded_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2612_; 
v_machine_2591_ = lean_ctor_get(v___y_2543_, 0);
v_requestStream_2592_ = lean_ctor_get(v___y_2543_, 1);
v_timer_2593_ = lean_ctor_get(v___y_2543_, 2);
v_response_2594_ = lean_ctor_get(v___y_2543_, 3);
v_respStream_2595_ = lean_ctor_get(v___y_2543_, 4);
v_handler_2596_ = lean_ctor_get(v___y_2543_, 6);
v_pendingHead_2597_ = lean_ctor_get(v___y_2543_, 7);
v_dateSecond_2598_ = lean_ctor_get(v___y_2543_, 8);
v_requestEnded_2599_ = lean_ctor_get_uint8(v___y_2543_, sizeof(void*)*9);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___y_2543_);
if (v_isSharedCheck_2612_ == 0)
{
lean_object* v_unused_2613_; 
v_unused_2613_ = lean_ctor_get(v___y_2543_, 5);
lean_dec(v_unused_2613_);
v___x_2601_ = v___y_2543_;
v_isShared_2602_ = v_isSharedCheck_2612_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_dateSecond_2598_);
lean_inc(v_pendingHead_2597_);
lean_inc(v_handler_2596_);
lean_inc(v_respStream_2595_);
lean_inc(v_response_2594_);
lean_inc(v_timer_2593_);
lean_inc(v_requestStream_2592_);
lean_inc(v_machine_2591_);
lean_dec(v___y_2543_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2612_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2590_ == 0)
{
v___x_2604_ = v___x_2589_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_size_2587_);
v___x_2604_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2606_; 
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 5, v___x_2604_);
v___x_2606_ = v___x_2601_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_machine_2591_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_requestStream_2592_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_timer_2593_);
lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_response_2594_);
lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_respStream_2595_);
lean_ctor_set(v_reuseFailAlloc_2610_, 5, v___x_2604_);
lean_ctor_set(v_reuseFailAlloc_2610_, 6, v_handler_2596_);
lean_ctor_set(v_reuseFailAlloc_2610_, 7, v_pendingHead_2597_);
lean_ctor_set(v_reuseFailAlloc_2610_, 8, v_dateSecond_2598_);
lean_ctor_set_uint8(v_reuseFailAlloc_2610_, sizeof(void*)*9, v_requestEnded_2599_);
v___x_2606_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
v___x_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
v___x_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
return v___x_2609_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2615_; lean_object* v___f_2616_; lean_object* v___y_2618_; 
lean_dec_ref(v_connectionContext_2540_);
lean_dec_ref(v_inst_2539_);
lean_dec_ref(v_config_2536_);
v_err_2615_ = lean_ctor_get(v_a_2541_, 0);
lean_inc(v_err_2615_);
lean_dec_ref_known(v_a_2541_, 1);
lean_inc_ref(v___y_2543_);
v___f_2616_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2616_, 0, v___y_2543_);
switch(lean_obj_tag(v_err_2615_))
{
case 0:
{
lean_object* v___x_2625_; 
v___x_2625_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__7));
v___y_2618_ = v___x_2625_;
goto v___jp_2617_;
}
case 1:
{
lean_object* v___x_2626_; 
v___x_2626_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__8));
v___y_2618_ = v___x_2626_;
goto v___jp_2617_;
}
case 2:
{
lean_object* v___x_2627_; 
v___x_2627_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__9));
v___y_2618_ = v___x_2627_;
goto v___jp_2617_;
}
case 3:
{
lean_object* v___x_2628_; 
v___x_2628_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__10));
v___y_2618_ = v___x_2628_;
goto v___jp_2617_;
}
case 4:
{
lean_object* v___x_2629_; 
v___x_2629_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__11));
v___y_2618_ = v___x_2629_;
goto v___jp_2617_;
}
case 5:
{
lean_object* v___x_2630_; 
v___x_2630_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__12));
v___y_2618_ = v___x_2630_;
goto v___jp_2617_;
}
case 6:
{
lean_object* v___x_2631_; 
v___x_2631_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__13));
v___y_2618_ = v___x_2631_;
goto v___jp_2617_;
}
case 7:
{
lean_object* v___x_2632_; 
v___x_2632_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__14));
v___y_2618_ = v___x_2632_;
goto v___jp_2617_;
}
case 8:
{
lean_object* v___x_2633_; 
v___x_2633_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__15));
v___y_2618_ = v___x_2633_;
goto v___jp_2617_;
}
case 9:
{
lean_object* v___x_2634_; 
v___x_2634_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__16));
v___y_2618_ = v___x_2634_;
goto v___jp_2617_;
}
case 10:
{
lean_object* v___x_2635_; 
v___x_2635_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__17));
v___y_2618_ = v___x_2635_;
goto v___jp_2617_;
}
case 11:
{
lean_object* v___x_2636_; 
v___x_2636_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__18));
v___y_2618_ = v___x_2636_;
goto v___jp_2617_;
}
case 12:
{
lean_object* v___x_2637_; 
v___x_2637_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__19));
v___y_2618_ = v___x_2637_;
goto v___jp_2617_;
}
default: 
{
lean_object* v_message_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_message_2638_ = lean_ctor_get(v_err_2615_, 0);
lean_inc_ref(v_message_2638_);
lean_dec_ref_known(v_err_2615_, 1);
v___x_2639_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__20));
v___x_2640_ = lean_string_append(v___x_2639_, v_message_2638_);
lean_dec_ref(v_message_2638_);
v___y_2618_ = v___x_2640_;
goto v___jp_2617_;
}
}
v___jp_2617_:
{
lean_object* v___f_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_inc_ref(v___y_2618_);
v___f_2619_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2619_, 0, v___y_2618_);
lean_closure_set(v___f_2619_, 1, v___y_2543_);
lean_closure_set(v___f_2619_, 2, v___f_2616_);
v___x_2620_ = lean_mk_io_user_error(v___y_2618_);
v___x_2621_ = lean_unsigned_to_nat(0u);
v___x_2622_ = 0;
v___x_2623_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_2537_, v_handler_2538_, v___x_2620_);
v___x_2624_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2621_, v___x_2622_, v___x_2623_, v___f_2619_);
return v___x_2624_;
}
}
case 4:
{
lean_object* v___f_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_dec_ref(v_connectionContext_2540_);
lean_dec_ref(v_inst_2539_);
lean_dec(v_handler_2538_);
lean_dec_ref(v_inst_2537_);
lean_dec_ref(v_config_2536_);
lean_inc_ref(v___y_2543_);
v___f_2641_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2641_, 0, v___y_2543_);
v___x_2642_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__21));
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = 0;
v___x_2645_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v___y_2543_, v___x_2642_);
v___x_2646_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2643_, v___x_2644_, v___x_2645_, v___f_2641_);
return v___x_2646_;
}
case 6:
{
lean_object* v___f_2647_; lean_object* v___f_2648_; lean_object* v___f_2649_; lean_object* v___f_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_dec_ref(v_connectionContext_2540_);
lean_dec(v_handler_2538_);
lean_dec_ref(v_inst_2537_);
lean_inc_ref_n(v___y_2543_, 2);
v___f_2647_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2647_, 0, v___y_2543_);
lean_closure_set(v___f_2647_, 1, v_config_2536_);
v___f_2648_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2648_, 0, v___f_2647_);
lean_inc_ref(v___f_2648_);
v___f_2649_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_2649_, 0, v___f_2648_);
v___f_2650_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 6, 4);
lean_closure_set(v___f_2650_, 0, v___y_2543_);
lean_closure_set(v___f_2650_, 1, v_inst_2539_);
lean_closure_set(v___f_2650_, 2, v___f_2649_);
lean_closure_set(v___f_2650_, 3, v___f_2648_);
v___x_2651_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__21));
v___x_2652_ = lean_unsigned_to_nat(0u);
v___x_2653_ = 0;
v___x_2654_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v___y_2543_, v___x_2651_);
v___x_2655_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2652_, v___x_2653_, v___x_2654_, v___f_2650_);
return v___x_2655_;
}
case 7:
{
lean_object* v_pendingHead_2656_; 
lean_dec_ref(v_inst_2539_);
v_pendingHead_2656_ = lean_ctor_get(v___y_2543_, 7);
if (lean_obj_tag(v_pendingHead_2656_) == 1)
{
lean_object* v_machine_2657_; lean_object* v_requestStream_2658_; lean_object* v_timer_2659_; lean_object* v_response_2660_; lean_object* v_respStream_2661_; lean_object* v_inputWanted_2662_; lean_object* v_handler_2663_; lean_object* v_dateSecond_2664_; uint8_t v_requestEnded_2665_; lean_object* v_val_2666_; lean_object* v___x_2667_; lean_object* v___f_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_inc_ref(v_pendingHead_2656_);
v_machine_2657_ = lean_ctor_get(v___y_2543_, 0);
lean_inc_ref(v_machine_2657_);
v_requestStream_2658_ = lean_ctor_get(v___y_2543_, 1);
lean_inc_ref(v_requestStream_2658_);
v_timer_2659_ = lean_ctor_get(v___y_2543_, 2);
lean_inc_ref(v_timer_2659_);
v_response_2660_ = lean_ctor_get(v___y_2543_, 3);
lean_inc_ref(v_response_2660_);
v_respStream_2661_ = lean_ctor_get(v___y_2543_, 4);
lean_inc(v_respStream_2661_);
v_inputWanted_2662_ = lean_ctor_get(v___y_2543_, 5);
lean_inc(v_inputWanted_2662_);
v_handler_2663_ = lean_ctor_get(v___y_2543_, 6);
lean_inc(v_handler_2663_);
v_dateSecond_2664_ = lean_ctor_get(v___y_2543_, 8);
lean_inc(v_dateSecond_2664_);
v_requestEnded_2665_ = lean_ctor_get_uint8(v___y_2543_, sizeof(void*)*9);
lean_dec_ref(v___y_2543_);
v_val_2666_ = lean_ctor_get(v_pendingHead_2656_, 0);
lean_inc(v_val_2666_);
v___x_2667_ = lean_box(v_requestEnded_2665_);
v___f_2668_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_2668_, 0, v_requestStream_2658_);
lean_closure_set(v___f_2668_, 1, v_timer_2659_);
lean_closure_set(v___f_2668_, 2, v_response_2660_);
lean_closure_set(v___f_2668_, 3, v_respStream_2661_);
lean_closure_set(v___f_2668_, 4, v_inputWanted_2662_);
lean_closure_set(v___f_2668_, 5, v_handler_2663_);
lean_closure_set(v___f_2668_, 6, v_pendingHead_2656_);
lean_closure_set(v___f_2668_, 7, v_dateSecond_2664_);
lean_closure_set(v___f_2668_, 8, v___x_2667_);
v___x_2669_ = lean_unsigned_to_nat(0u);
v___x_2670_ = 0;
v___x_2671_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2537_, v_handler_2538_, v_machine_2657_, v_val_2666_, v_config_2536_, v_connectionContext_2540_);
v___x_2672_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2669_, v___x_2670_, v___x_2671_, v___f_2668_);
return v___x_2672_;
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_dec_ref(v_connectionContext_2540_);
lean_dec(v_handler_2538_);
lean_dec_ref(v_inst_2537_);
lean_dec_ref(v_config_2536_);
v___x_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___y_2543_);
v___x_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
}
default: 
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_dec(v_a_2541_);
lean_dec_ref(v_connectionContext_2540_);
lean_dec_ref(v_inst_2539_);
lean_dec(v_handler_2538_);
lean_dec_ref(v_inst_2537_);
lean_dec_ref(v_config_2536_);
v___x_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___y_2543_);
v___x_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
return v___x_2678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_config_2679_, lean_object* v_inst_2680_, lean_object* v_handler_2681_, lean_object* v_inst_2682_, lean_object* v_connectionContext_2683_, lean_object* v_a_2684_, lean_object* v_x_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_config_2679_, v_inst_2680_, v_handler_2681_, v_inst_2682_, v_connectionContext_2683_, v_a_2684_, v_x_2685_, v___y_2686_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_x_2689_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2691_, 0, v_x_2689_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_x_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_x_2692_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_handler_2698_, lean_object* v_config_2699_, lean_object* v_connectionContext_2700_, lean_object* v_events_2701_, lean_object* v_state_2702_){
_start:
{
lean_object* v___f_2704_; lean_object* v___f_2705_; lean_object* v___x_2706_; size_t v_sz_2707_; size_t v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_3347__overap_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___f_2704_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 9, 5);
lean_closure_set(v___f_2704_, 0, v_config_2699_);
lean_closure_set(v___f_2704_, 1, v_inst_2696_);
lean_closure_set(v___f_2704_, 2, v_handler_2698_);
lean_closure_set(v___f_2704_, 3, v_inst_2697_);
lean_closure_set(v___f_2704_, 4, v_connectionContext_2700_);
v___f_2705_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_2706_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0);
v_sz_2707_ = lean_array_size(v_events_2701_);
v___x_2708_ = ((size_t)0ULL);
v___x_2709_ = lean_unsigned_to_nat(0u);
v___x_2710_ = 0;
v___x_3347__overap_2711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2706_, v_events_2701_, v___f_2704_, v_sz_2707_, v___x_2708_, v_state_2702_);
v___x_2712_ = lean_apply_1(v___x_3347__overap_2711_, lean_box(0));
v___x_2713_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2709_, v___x_2710_, v___x_2712_, v___f_2705_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2714_, lean_object* v_inst_2715_, lean_object* v_handler_2716_, lean_object* v_config_2717_, lean_object* v_connectionContext_2718_, lean_object* v_events_2719_, lean_object* v_state_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2714_, v_inst_2715_, v_handler_2716_, v_config_2717_, v_connectionContext_2718_, v_events_2719_, v_state_2720_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2723_, lean_object* v_00_u03b2_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_handler_2727_, lean_object* v_config_2728_, lean_object* v_connectionContext_2729_, lean_object* v_events_2730_, lean_object* v_state_2731_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2725_, v_inst_2726_, v_handler_2727_, v_config_2728_, v_connectionContext_2729_, v_events_2730_, v_state_2731_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2734_, lean_object* v_00_u03b2_2735_, lean_object* v_inst_2736_, lean_object* v_inst_2737_, lean_object* v_handler_2738_, lean_object* v_config_2739_, lean_object* v_connectionContext_2740_, lean_object* v_events_2741_, lean_object* v_state_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2734_, v_00_u03b2_2735_, v_inst_2736_, v_inst_2737_, v_handler_2738_, v_config_2739_, v_connectionContext_2740_, v_events_2741_, v_state_2742_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2745_){
_start:
{
if (lean_obj_tag(v_x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2747_; 
v_a_2746_ = lean_ctor_get(v_x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v_x_2745_, 1);
v___x_2747_ = lean_task_pure(v_a_2746_);
return v___x_2747_;
}
else
{
lean_object* v_a_2748_; 
v_a_2748_ = lean_ctor_get(v_x_2745_, 0);
lean_inc_ref(v_a_2748_);
lean_dec_ref_known(v_x_2745_, 1);
return v_a_2748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_a_2749_, lean_object* v_machine_2750_, lean_object* v_requestStream_2751_, lean_object* v_timer_2752_, lean_object* v_response_2753_, lean_object* v_respStream_2754_, lean_object* v_inputWanted_2755_, lean_object* v_dateSecond_2756_, uint8_t v_requestEnded_2757_, lean_object* v_x_2758_){
_start:
{
if (lean_obj_tag(v_x_2758_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_dateSecond_2756_);
lean_dec(v_inputWanted_2755_);
lean_dec(v_respStream_2754_);
lean_dec_ref(v_response_2753_);
lean_dec_ref(v_timer_2752_);
lean_dec_ref(v_requestStream_2751_);
lean_dec_ref(v_machine_2750_);
lean_dec_ref(v_a_2749_);
v_a_2760_ = lean_ctor_get(v_x_2758_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_x_2758_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2762_ = v_x_2758_;
v_isShared_2763_ = v_isSharedCheck_2768_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v_x_2758_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2768_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
return v___x_2766_;
}
}
}
else
{
lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2779_; 
v_isSharedCheck_2779_ = !lean_is_exclusive(v_x_2758_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; 
v_unused_2780_ = lean_ctor_get(v_x_2758_, 0);
lean_dec(v_unused_2780_);
v___x_2770_ = v_x_2758_;
v_isShared_2771_ = v_isSharedCheck_2779_;
goto v_resetjp_2769_;
}
else
{
lean_dec(v_x_2758_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2779_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_a_2749_);
v___x_2773_ = lean_box(0);
v___x_2774_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2774_, 0, v_machine_2750_);
lean_ctor_set(v___x_2774_, 1, v_requestStream_2751_);
lean_ctor_set(v___x_2774_, 2, v_timer_2752_);
lean_ctor_set(v___x_2774_, 3, v_response_2753_);
lean_ctor_set(v___x_2774_, 4, v_respStream_2754_);
lean_ctor_set(v___x_2774_, 5, v_inputWanted_2755_);
lean_ctor_set(v___x_2774_, 6, v___x_2772_);
lean_ctor_set(v___x_2774_, 7, v___x_2773_);
lean_ctor_set(v___x_2774_, 8, v_dateSecond_2756_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*9, v_requestEnded_2757_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v___x_2774_);
v___x_2776_ = v___x_2770_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
return v___x_2777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_a_2781_, lean_object* v_machine_2782_, lean_object* v_requestStream_2783_, lean_object* v_timer_2784_, lean_object* v_response_2785_, lean_object* v_respStream_2786_, lean_object* v_inputWanted_2787_, lean_object* v_dateSecond_2788_, lean_object* v_requestEnded_2789_, lean_object* v_x_2790_, lean_object* v___y_2791_){
_start:
{
uint8_t v_requestEnded_boxed_2792_; lean_object* v_res_2793_; 
v_requestEnded_boxed_2792_ = lean_unbox(v_requestEnded_2789_);
v_res_2793_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_a_2781_, v_machine_2782_, v_requestStream_2783_, v_timer_2784_, v_response_2785_, v_respStream_2786_, v_inputWanted_2787_, v_dateSecond_2788_, v_requestEnded_boxed_2792_, v_x_2790_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_machine_2794_, lean_object* v_requestStream_2795_, lean_object* v_timer_2796_, lean_object* v_response_2797_, lean_object* v_respStream_2798_, lean_object* v_inputWanted_2799_, lean_object* v_dateSecond_2800_, uint8_t v_requestEnded_2801_, lean_object* v_toFunctor_2802_, lean_object* v___x_2803_, lean_object* v_x_2804_){
_start:
{
if (lean_obj_tag(v_x_2804_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v___x_2803_);
lean_dec_ref(v_toFunctor_2802_);
lean_dec(v_dateSecond_2800_);
lean_dec(v_inputWanted_2799_);
lean_dec(v_respStream_2798_);
lean_dec_ref(v_response_2797_);
lean_dec_ref(v_timer_2796_);
lean_dec_ref(v_requestStream_2795_);
lean_dec_ref(v_machine_2794_);
v_a_2806_ = lean_ctor_get(v_x_2804_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v_x_2804_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2808_ = v_x_2804_;
v_isShared_2809_ = v_isSharedCheck_2814_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v_x_2804_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2814_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
return v___x_2812_;
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2831_; 
v_a_2815_ = lean_ctor_get(v_x_2804_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_x_2804_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2817_ = v_x_2804_;
v_isShared_2818_ = v_isSharedCheck_2831_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v_x_2804_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2831_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___f_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2819_ = lean_box(v_requestEnded_2801_);
lean_inc_ref(v_response_2797_);
lean_inc(v_a_2815_);
v___f_2820_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 11, 9);
lean_closure_set(v___f_2820_, 0, v_a_2815_);
lean_closure_set(v___f_2820_, 1, v_machine_2794_);
lean_closure_set(v___f_2820_, 2, v_requestStream_2795_);
lean_closure_set(v___f_2820_, 3, v_timer_2796_);
lean_closure_set(v___f_2820_, 4, v_response_2797_);
lean_closure_set(v___f_2820_, 5, v_respStream_2798_);
lean_closure_set(v___f_2820_, 6, v_inputWanted_2799_);
lean_closure_set(v___f_2820_, 7, v_dateSecond_2800_);
lean_closure_set(v___f_2820_, 8, v___x_2819_);
v___x_2821_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2821_, 0, lean_box(0));
lean_closure_set(v___x_2821_, 1, lean_box(0));
lean_closure_set(v___x_2821_, 2, v_toFunctor_2802_);
v___x_2822_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2822_, 0, lean_box(0));
lean_closure_set(v___x_2822_, 1, v_response_2797_);
v___x_2823_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2823_, 0, lean_box(0));
lean_closure_set(v___x_2823_, 1, lean_box(0));
lean_closure_set(v___x_2823_, 2, lean_box(0));
lean_closure_set(v___x_2823_, 3, v___x_2821_);
lean_closure_set(v___x_2823_, 4, v___x_2822_);
v___x_2824_ = 0;
lean_inc(v___x_2803_);
v___x_2825_ = l_BaseIO_chainTask___redArg(v_a_2815_, v___x_2823_, v___x_2803_, v___x_2824_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2825_);
v___x_2827_ = v___x_2817_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
v___x_2829_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2803_, v___x_2824_, v___x_2828_, v___f_2820_);
return v___x_2829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_machine_2832_, lean_object* v_requestStream_2833_, lean_object* v_timer_2834_, lean_object* v_response_2835_, lean_object* v_respStream_2836_, lean_object* v_inputWanted_2837_, lean_object* v_dateSecond_2838_, lean_object* v_requestEnded_2839_, lean_object* v_toFunctor_2840_, lean_object* v___x_2841_, lean_object* v_x_2842_, lean_object* v___y_2843_){
_start:
{
uint8_t v_requestEnded_boxed_2844_; lean_object* v_res_2845_; 
v_requestEnded_boxed_2844_ = lean_unbox(v_requestEnded_2839_);
v_res_2845_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_machine_2832_, v_requestStream_2833_, v_timer_2834_, v_response_2835_, v_respStream_2836_, v_inputWanted_2837_, v_dateSecond_2838_, v_requestEnded_boxed_2844_, v_toFunctor_2840_, v___x_2841_, v_x_2842_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2847_, lean_object* v_handler_2848_, lean_object* v_extensions_2849_, lean_object* v_connectionContext_2850_, lean_object* v_state_2851_){
_start:
{
lean_object* v___x_2853_; lean_object* v_toApplicative_2854_; lean_object* v_pendingHead_2855_; 
v___x_2853_ = l_instMonadBaseIO;
v_toApplicative_2854_ = lean_ctor_get(v___x_2853_, 0);
v_pendingHead_2855_ = lean_ctor_get(v_state_2851_, 7);
lean_inc(v_pendingHead_2855_);
if (lean_obj_tag(v_pendingHead_2855_) == 1)
{
lean_object* v_toFunctor_2856_; lean_object* v_machine_2857_; lean_object* v_requestStream_2858_; lean_object* v_timer_2859_; lean_object* v_response_2860_; lean_object* v_respStream_2861_; lean_object* v_inputWanted_2862_; lean_object* v_dateSecond_2863_; uint8_t v_requestEnded_2864_; lean_object* v_val_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2886_; 
v_toFunctor_2856_ = lean_ctor_get(v_toApplicative_2854_, 0);
v_machine_2857_ = lean_ctor_get(v_state_2851_, 0);
lean_inc_ref(v_machine_2857_);
v_requestStream_2858_ = lean_ctor_get(v_state_2851_, 1);
lean_inc_ref(v_requestStream_2858_);
v_timer_2859_ = lean_ctor_get(v_state_2851_, 2);
lean_inc_ref(v_timer_2859_);
v_response_2860_ = lean_ctor_get(v_state_2851_, 3);
lean_inc_ref(v_response_2860_);
v_respStream_2861_ = lean_ctor_get(v_state_2851_, 4);
lean_inc(v_respStream_2861_);
v_inputWanted_2862_ = lean_ctor_get(v_state_2851_, 5);
lean_inc(v_inputWanted_2862_);
v_dateSecond_2863_ = lean_ctor_get(v_state_2851_, 8);
lean_inc(v_dateSecond_2863_);
v_requestEnded_2864_ = lean_ctor_get_uint8(v_state_2851_, sizeof(void*)*9);
lean_dec_ref(v_state_2851_);
v_val_2865_ = lean_ctor_get(v_pendingHead_2855_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v_pendingHead_2855_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2867_ = v_pendingHead_2855_;
v_isShared_2868_ = v_isSharedCheck_2886_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_val_2865_);
lean_dec(v_pendingHead_2855_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2886_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v_onRequest_2869_; lean_object* v___f_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___f_2875_; uint8_t v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2882_; 
v_onRequest_2869_ = lean_ctor_get(v_inst_2847_, 1);
lean_inc_ref(v_onRequest_2869_);
lean_dec_ref(v_inst_2847_);
v___f_2870_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
lean_inc_ref(v_requestStream_2858_);
v___x_2871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2871_, 0, v_val_2865_);
lean_ctor_set(v___x_2871_, 1, v_requestStream_2858_);
lean_ctor_set(v___x_2871_, 2, v_extensions_2849_);
v___x_2872_ = lean_apply_3(v_onRequest_2869_, v_handler_2848_, v___x_2871_, v_connectionContext_2850_);
v___x_2873_ = lean_unsigned_to_nat(0u);
v___x_2874_ = lean_box(v_requestEnded_2864_);
lean_inc_ref(v_toFunctor_2856_);
v___f_2875_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_2875_, 0, v_machine_2857_);
lean_closure_set(v___f_2875_, 1, v_requestStream_2858_);
lean_closure_set(v___f_2875_, 2, v_timer_2859_);
lean_closure_set(v___f_2875_, 3, v_response_2860_);
lean_closure_set(v___f_2875_, 4, v_respStream_2861_);
lean_closure_set(v___f_2875_, 5, v_inputWanted_2862_);
lean_closure_set(v___f_2875_, 6, v_dateSecond_2863_);
lean_closure_set(v___f_2875_, 7, v___x_2874_);
lean_closure_set(v___f_2875_, 8, v_toFunctor_2856_);
lean_closure_set(v___f_2875_, 9, v___x_2873_);
v___x_2876_ = 0;
v___x_2877_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2877_, 0, lean_box(0));
lean_closure_set(v___x_2877_, 1, v___x_2872_);
v___x_2878_ = lean_io_as_task(v___x_2877_, v___x_2873_);
v___x_2879_ = 1;
v___x_2880_ = lean_task_bind(v___x_2878_, v___f_2870_, v___x_2873_, v___x_2879_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v___x_2880_);
v___x_2882_ = v___x_2867_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
v___x_2884_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2873_, v___x_2876_, v___x_2883_, v___f_2875_);
return v___x_2884_;
}
}
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_dec(v_pendingHead_2855_);
lean_dec_ref(v_connectionContext_2850_);
lean_dec(v_extensions_2849_);
lean_dec(v_handler_2848_);
lean_dec_ref(v_inst_2847_);
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v_state_2851_);
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
return v___x_2888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2889_, lean_object* v_handler_2890_, lean_object* v_extensions_2891_, lean_object* v_connectionContext_2892_, lean_object* v_state_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2889_, v_handler_2890_, v_extensions_2891_, v_connectionContext_2892_, v_state_2893_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2896_, lean_object* v_inst_2897_, lean_object* v_handler_2898_, lean_object* v_extensions_2899_, lean_object* v_connectionContext_2900_, lean_object* v_state_2901_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2897_, v_handler_2898_, v_extensions_2899_, v_connectionContext_2900_, v_state_2901_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2904_, lean_object* v_inst_2905_, lean_object* v_handler_2906_, lean_object* v_extensions_2907_, lean_object* v_connectionContext_2908_, lean_object* v_state_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2904_, v_inst_2905_, v_handler_2906_, v_extensions_2907_, v_connectionContext_2908_, v_state_2909_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2912_, lean_object* v_____r_2913_){
_start:
{
lean_object* v_writer_2915_; lean_object* v_reader_2916_; lean_object* v_config_2917_; lean_object* v_events_2918_; lean_object* v_error_2919_; lean_object* v_date_2920_; uint8_t v_keepAlive_2921_; uint8_t v_pullBodyStalled_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2948_; 
v_writer_2915_ = lean_ctor_get(v_machine_2912_, 1);
v_reader_2916_ = lean_ctor_get(v_machine_2912_, 0);
v_config_2917_ = lean_ctor_get(v_machine_2912_, 2);
v_events_2918_ = lean_ctor_get(v_machine_2912_, 3);
v_error_2919_ = lean_ctor_get(v_machine_2912_, 4);
v_date_2920_ = lean_ctor_get(v_machine_2912_, 5);
v_keepAlive_2921_ = lean_ctor_get_uint8(v_machine_2912_, sizeof(void*)*6);
v_pullBodyStalled_2922_ = lean_ctor_get_uint8(v_machine_2912_, sizeof(void*)*6 + 1);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_machine_2912_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2924_ = v_machine_2912_;
v_isShared_2925_ = v_isSharedCheck_2948_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_date_2920_);
lean_inc(v_error_2919_);
lean_inc(v_events_2918_);
lean_inc(v_config_2917_);
lean_inc(v_writer_2915_);
lean_inc(v_reader_2916_);
lean_dec(v_machine_2912_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2948_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v_userData_2926_; lean_object* v_outputData_2927_; lean_object* v_state_2928_; lean_object* v_knownSize_2929_; lean_object* v_messageHead_2930_; uint8_t v_omitBody_2931_; lean_object* v_userDataBytes_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2947_; 
v_userData_2926_ = lean_ctor_get(v_writer_2915_, 0);
v_outputData_2927_ = lean_ctor_get(v_writer_2915_, 1);
v_state_2928_ = lean_ctor_get(v_writer_2915_, 2);
v_knownSize_2929_ = lean_ctor_get(v_writer_2915_, 3);
v_messageHead_2930_ = lean_ctor_get(v_writer_2915_, 4);
v_omitBody_2931_ = lean_ctor_get_uint8(v_writer_2915_, sizeof(void*)*6 + 1);
v_userDataBytes_2932_ = lean_ctor_get(v_writer_2915_, 5);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_writer_2915_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2934_ = v_writer_2915_;
v_isShared_2935_ = v_isSharedCheck_2947_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_userDataBytes_2932_);
lean_inc(v_messageHead_2930_);
lean_inc(v_knownSize_2929_);
lean_inc(v_state_2928_);
lean_inc(v_outputData_2927_);
lean_inc(v_userData_2926_);
lean_dec(v_writer_2915_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2947_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
uint8_t v___x_2936_; lean_object* v___x_2938_; 
v___x_2936_ = 1;
if (v_isShared_2935_ == 0)
{
v___x_2938_ = v___x_2934_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_userData_2926_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_outputData_2927_);
lean_ctor_set(v_reuseFailAlloc_2946_, 2, v_state_2928_);
lean_ctor_set(v_reuseFailAlloc_2946_, 3, v_knownSize_2929_);
lean_ctor_set(v_reuseFailAlloc_2946_, 4, v_messageHead_2930_);
lean_ctor_set(v_reuseFailAlloc_2946_, 5, v_userDataBytes_2932_);
lean_ctor_set_uint8(v_reuseFailAlloc_2946_, sizeof(void*)*6 + 1, v_omitBody_2931_);
v___x_2938_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2940_; 
lean_ctor_set_uint8(v___x_2938_, sizeof(void*)*6, v___x_2936_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 1, v___x_2938_);
v___x_2940_ = v___x_2924_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_reader_2916_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v_config_2917_);
lean_ctor_set(v_reuseFailAlloc_2945_, 3, v_events_2918_);
lean_ctor_set(v_reuseFailAlloc_2945_, 4, v_error_2919_);
lean_ctor_set(v_reuseFailAlloc_2945_, 5, v_date_2920_);
lean_ctor_set_uint8(v_reuseFailAlloc_2945_, sizeof(void*)*6, v_keepAlive_2921_);
lean_ctor_set_uint8(v_reuseFailAlloc_2945_, sizeof(void*)*6 + 1, v_pullBodyStalled_2922_);
v___x_2940_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2941_ = lean_box(0);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
v___x_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
return v___x_2944_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2949_, lean_object* v_____r_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2949_, v_____r_2950_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2953_, lean_object* v_x2_2954_){
_start:
{
lean_object* v_data_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v_data_2955_ = lean_ctor_get(v_x2_2954_, 0);
v___x_2956_ = lean_byte_array_size(v_data_2955_);
v___x_2957_ = lean_nat_add(v_x1_2953_, v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2958_, lean_object* v_x2_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2958_, v_x2_2959_);
lean_dec_ref(v_x2_2959_);
lean_dec(v_x1_2958_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2961_, lean_object* v_machine_2962_, lean_object* v_isClosed_2963_, lean_object* v___f_2964_, lean_object* v___f_2965_, lean_object* v_x_2966_){
_start:
{
lean_object* v___y_2969_; 
if (lean_obj_tag(v_x_2966_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2982_; 
lean_dec_ref(v___f_2965_);
lean_dec_ref(v___f_2964_);
lean_dec_ref(v_isClosed_2963_);
lean_dec_ref(v_machine_2962_);
lean_dec(v_body_2961_);
v_a_2974_ = lean_ctor_get(v_x_2966_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_x_2966_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2976_ = v_x_2966_;
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v_x_2966_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
return v___x_2980_;
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3044_; 
v_a_2983_ = lean_ctor_get(v_x_2966_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_x_2966_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_2985_ = v_x_2966_;
v_isShared_2986_ = v_isSharedCheck_3044_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v_x_2966_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3044_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
if (lean_obj_tag(v_a_2983_) == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
lean_dec_ref(v___f_2965_);
lean_dec_ref(v___f_2964_);
lean_dec_ref(v_isClosed_2963_);
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v_body_2961_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v_machine_2962_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2988_);
v___x_2990_ = v___x_2985_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
return v___x_2991_;
}
}
else
{
lean_object* v_val_2993_; 
lean_del_object(v___x_2985_);
v_val_2993_ = lean_ctor_get(v_a_2983_, 0);
lean_inc(v_val_2993_);
lean_dec_ref_known(v_a_2983_, 1);
if (lean_obj_tag(v_val_2993_) == 0)
{
lean_object* v___x_2994_; uint8_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
lean_dec_ref(v___f_2965_);
lean_dec_ref(v_machine_2962_);
v___x_2994_ = lean_unsigned_to_nat(0u);
v___x_2995_ = 0;
v___x_2996_ = lean_apply_2(v_isClosed_2963_, v_body_2961_, lean_box(0));
v___x_2997_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2994_, v___x_2995_, v___x_2996_, v___f_2964_);
return v___x_2997_;
}
else
{
lean_object* v_val_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
lean_dec_ref(v___f_2964_);
lean_dec_ref(v_isClosed_2963_);
v_val_2998_ = lean_ctor_get(v_val_2993_, 0);
lean_inc(v_val_2998_);
lean_dec_ref_known(v_val_2993_, 1);
v___x_2999_ = lean_unsigned_to_nat(1u);
v___x_3000_ = lean_mk_empty_array_with_capacity(v___x_2999_);
v___x_3001_ = lean_array_push(v___x_3000_, v_val_2998_);
v___x_3002_ = lean_array_get_size(v___x_3001_);
v___x_3003_ = lean_unsigned_to_nat(0u);
v___x_3004_ = lean_nat_dec_eq(v___x_3002_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_object* v_reader_3005_; lean_object* v_writer_3006_; lean_object* v_config_3007_; lean_object* v_events_3008_; lean_object* v_error_3009_; lean_object* v_date_3010_; uint8_t v_keepAlive_3011_; uint8_t v_pullBodyStalled_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3043_; 
v_reader_3005_ = lean_ctor_get(v_machine_2962_, 0);
v_writer_3006_ = lean_ctor_get(v_machine_2962_, 1);
v_config_3007_ = lean_ctor_get(v_machine_2962_, 2);
v_events_3008_ = lean_ctor_get(v_machine_2962_, 3);
v_error_3009_ = lean_ctor_get(v_machine_2962_, 4);
v_date_3010_ = lean_ctor_get(v_machine_2962_, 5);
v_keepAlive_3011_ = lean_ctor_get_uint8(v_machine_2962_, sizeof(void*)*6);
v_pullBodyStalled_3012_ = lean_ctor_get_uint8(v_machine_2962_, sizeof(void*)*6 + 1);
v_isSharedCheck_3043_ = !lean_is_exclusive(v_machine_2962_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3014_ = v_machine_2962_;
v_isShared_3015_ = v_isSharedCheck_3043_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_date_3010_);
lean_inc(v_error_3009_);
lean_inc(v_events_3008_);
lean_inc(v_config_3007_);
lean_inc(v_writer_3006_);
lean_inc(v_reader_3005_);
lean_dec(v_machine_2962_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3043_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___y_3017_; lean_object* v___x_3038_; uint8_t v___x_3039_; 
v___x_3038_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_3039_ = lean_nat_dec_lt(v___x_3003_, v___x_3002_);
if (v___x_3039_ == 0)
{
lean_dec_ref(v___f_2965_);
v___y_3017_ = v___x_3003_;
goto v___jp_3016_;
}
else
{
size_t v___x_3040_; size_t v___x_3041_; lean_object* v___x_3042_; 
v___x_3040_ = ((size_t)0ULL);
v___x_3041_ = lean_usize_of_nat(v___x_3002_);
lean_inc_ref(v___x_3001_);
v___x_3042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3038_, v___f_2965_, v___x_3001_, v___x_3040_, v___x_3041_, v___x_3003_);
v___y_3017_ = v___x_3042_;
goto v___jp_3016_;
}
v___jp_3016_:
{
lean_object* v_userData_3018_; lean_object* v_outputData_3019_; lean_object* v_state_3020_; lean_object* v_knownSize_3021_; lean_object* v_messageHead_3022_; uint8_t v_userClosedBody_3023_; uint8_t v_omitBody_3024_; lean_object* v_userDataBytes_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3037_; 
v_userData_3018_ = lean_ctor_get(v_writer_3006_, 0);
v_outputData_3019_ = lean_ctor_get(v_writer_3006_, 1);
v_state_3020_ = lean_ctor_get(v_writer_3006_, 2);
v_knownSize_3021_ = lean_ctor_get(v_writer_3006_, 3);
v_messageHead_3022_ = lean_ctor_get(v_writer_3006_, 4);
v_userClosedBody_3023_ = lean_ctor_get_uint8(v_writer_3006_, sizeof(void*)*6);
v_omitBody_3024_ = lean_ctor_get_uint8(v_writer_3006_, sizeof(void*)*6 + 1);
v_userDataBytes_3025_ = lean_ctor_get(v_writer_3006_, 5);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_writer_3006_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3027_ = v_writer_3006_;
v_isShared_3028_ = v_isSharedCheck_3037_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_userDataBytes_3025_);
lean_inc(v_messageHead_3022_);
lean_inc(v_knownSize_3021_);
lean_inc(v_state_3020_);
lean_inc(v_outputData_3019_);
lean_inc(v_userData_3018_);
lean_dec(v_writer_3006_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3037_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
v___x_3029_ = l_Array_append___redArg(v_userData_3018_, v___x_3001_);
lean_dec_ref(v___x_3001_);
v___x_3030_ = lean_nat_add(v_userDataBytes_3025_, v___y_3017_);
lean_dec(v___y_3017_);
lean_dec(v_userDataBytes_3025_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 5, v___x_3030_);
lean_ctor_set(v___x_3027_, 0, v___x_3029_);
v___x_3032_ = v___x_3027_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3029_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_outputData_3019_);
lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_state_3020_);
lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_knownSize_3021_);
lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_messageHead_3022_);
lean_ctor_set(v_reuseFailAlloc_3036_, 5, v___x_3030_);
lean_ctor_set_uint8(v_reuseFailAlloc_3036_, sizeof(void*)*6, v_userClosedBody_3023_);
lean_ctor_set_uint8(v_reuseFailAlloc_3036_, sizeof(void*)*6 + 1, v_omitBody_3024_);
v___x_3032_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3034_; 
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 1, v___x_3032_);
v___x_3034_ = v___x_3014_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_reader_3005_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3035_, 2, v_config_3007_);
lean_ctor_set(v_reuseFailAlloc_3035_, 3, v_events_3008_);
lean_ctor_set(v_reuseFailAlloc_3035_, 4, v_error_3009_);
lean_ctor_set(v_reuseFailAlloc_3035_, 5, v_date_3010_);
lean_ctor_set_uint8(v_reuseFailAlloc_3035_, sizeof(void*)*6, v_keepAlive_3011_);
lean_ctor_set_uint8(v_reuseFailAlloc_3035_, sizeof(void*)*6 + 1, v_pullBodyStalled_3012_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
v___y_2969_ = v___x_3034_;
goto v___jp_2968_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3001_);
lean_dec_ref(v___f_2965_);
v___y_2969_ = v_machine_2962_;
goto v___jp_2968_;
}
}
}
}
}
v___jp_2968_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2970_, 0, v_body_2961_);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___y_2969_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
v___x_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
return v___x_2973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_3045_, lean_object* v_machine_3046_, lean_object* v_isClosed_3047_, lean_object* v___f_3048_, lean_object* v___f_3049_, lean_object* v_x_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_3045_, v_machine_3046_, v_isClosed_3047_, v___f_3048_, v___f_3049_, v_x_3050_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_3054_, lean_object* v_machine_3055_, lean_object* v_body_3056_){
_start:
{
lean_object* v_close_3058_; lean_object* v_isClosed_3059_; lean_object* v_tryRecv_3060_; lean_object* v___f_3061_; lean_object* v___f_3062_; lean_object* v___f_3063_; lean_object* v___f_3064_; lean_object* v___f_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_close_3058_ = lean_ctor_get(v_inst_3054_, 1);
lean_inc_ref(v_close_3058_);
v_isClosed_3059_ = lean_ctor_get(v_inst_3054_, 2);
lean_inc_ref(v_isClosed_3059_);
v_tryRecv_3060_ = lean_ctor_get(v_inst_3054_, 4);
lean_inc_ref(v_tryRecv_3060_);
lean_dec_ref(v_inst_3054_);
lean_inc_ref(v_machine_3055_);
v___f_3061_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3061_, 0, v_machine_3055_);
lean_inc_ref(v___f_3061_);
v___f_3062_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3062_, 0, v___f_3061_);
lean_inc_n(v_body_3056_, 2);
v___f_3063_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3063_, 0, v_close_3058_);
lean_closure_set(v___f_3063_, 1, v_body_3056_);
lean_closure_set(v___f_3063_, 2, v___f_3062_);
lean_closure_set(v___f_3063_, 3, v___f_3061_);
v___f_3064_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_3065_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_3065_, 0, v_body_3056_);
lean_closure_set(v___f_3065_, 1, v_machine_3055_);
lean_closure_set(v___f_3065_, 2, v_isClosed_3059_);
lean_closure_set(v___f_3065_, 3, v___f_3063_);
lean_closure_set(v___f_3065_, 4, v___f_3064_);
v___x_3066_ = lean_unsigned_to_nat(0u);
v___x_3067_ = 0;
v___x_3068_ = lean_apply_2(v_tryRecv_3060_, v_body_3056_, lean_box(0));
v___x_3069_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3066_, v___x_3067_, v___x_3068_, v___f_3065_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_3070_, lean_object* v_machine_3071_, lean_object* v_body_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3070_, v_machine_3071_, v_body_3072_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_3075_, lean_object* v_inst_3076_, lean_object* v_machine_3077_, lean_object* v_body_3078_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3076_, v_machine_3077_, v_body_3078_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_3081_, lean_object* v_inst_3082_, lean_object* v_machine_3083_, lean_object* v_body_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_3081_, v_inst_3082_, v_machine_3083_, v_body_3084_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_3091_, lean_object* v_____r_3092_, lean_object* v_st_3093_){
_start:
{
lean_object* v_machine_3095_; lean_object* v_requestStream_3096_; lean_object* v_timer_3097_; lean_object* v_response_3098_; lean_object* v_respStream_3099_; lean_object* v_inputWanted_3100_; lean_object* v_handler_3101_; lean_object* v_pendingHead_3102_; lean_object* v_dateSecond_3103_; uint8_t v_requestEnded_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3187_; 
v_machine_3095_ = lean_ctor_get(v_st_3093_, 0);
v_requestStream_3096_ = lean_ctor_get(v_st_3093_, 1);
v_timer_3097_ = lean_ctor_get(v_st_3093_, 2);
v_response_3098_ = lean_ctor_get(v_st_3093_, 3);
v_respStream_3099_ = lean_ctor_get(v_st_3093_, 4);
v_inputWanted_3100_ = lean_ctor_get(v_st_3093_, 5);
v_handler_3101_ = lean_ctor_get(v_st_3093_, 6);
v_pendingHead_3102_ = lean_ctor_get(v_st_3093_, 7);
v_dateSecond_3103_ = lean_ctor_get(v_st_3093_, 8);
v_requestEnded_3104_ = lean_ctor_get_uint8(v_st_3093_, sizeof(void*)*9);
v_isSharedCheck_3187_ = !lean_is_exclusive(v_st_3093_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3106_ = v_st_3093_;
v_isShared_3107_ = v_isSharedCheck_3187_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_dateSecond_3103_);
lean_inc(v_pendingHead_3102_);
lean_inc(v_handler_3101_);
lean_inc(v_inputWanted_3100_);
lean_inc(v_respStream_3099_);
lean_inc(v_response_3098_);
lean_inc(v_timer_3097_);
lean_inc(v_requestStream_3096_);
lean_inc(v_machine_3095_);
lean_dec(v_st_3093_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3187_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___y_3109_; lean_object* v_reader_3118_; lean_object* v_state_3119_; 
v_reader_3118_ = lean_ctor_get(v_machine_3095_, 0);
lean_inc_ref(v_reader_3118_);
v_state_3119_ = lean_ctor_get(v_reader_3118_, 0);
lean_inc(v_state_3119_);
if (lean_obj_tag(v_state_3119_) == 6)
{
lean_dec_ref(v_reader_3118_);
lean_dec_ref(v_val_3091_);
v___y_3109_ = v_machine_3095_;
goto v___jp_3108_;
}
else
{
lean_object* v_error_3120_; 
v_error_3120_ = lean_ctor_get(v_machine_3095_, 4);
if (lean_obj_tag(v_error_3120_) == 0)
{
lean_object* v_input_3121_; lean_object* v_writer_3122_; lean_object* v_config_3123_; lean_object* v_events_3124_; lean_object* v_date_3125_; uint8_t v_keepAlive_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3184_; 
lean_inc(v_error_3120_);
v_input_3121_ = lean_ctor_get(v_reader_3118_, 1);
lean_inc_ref(v_input_3121_);
v_writer_3122_ = lean_ctor_get(v_machine_3095_, 1);
v_config_3123_ = lean_ctor_get(v_machine_3095_, 2);
v_events_3124_ = lean_ctor_get(v_machine_3095_, 3);
v_date_3125_ = lean_ctor_get(v_machine_3095_, 5);
v_keepAlive_3126_ = lean_ctor_get_uint8(v_machine_3095_, sizeof(void*)*6);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_machine_3095_);
if (v_isSharedCheck_3184_ == 0)
{
lean_object* v_unused_3185_; lean_object* v_unused_3186_; 
v_unused_3185_ = lean_ctor_get(v_machine_3095_, 4);
lean_dec(v_unused_3185_);
v_unused_3186_ = lean_ctor_get(v_machine_3095_, 0);
lean_dec(v_unused_3186_);
v___x_3128_ = v_machine_3095_;
v_isShared_3129_ = v_isSharedCheck_3184_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_date_3125_);
lean_inc(v_events_3124_);
lean_inc(v_config_3123_);
lean_inc(v_writer_3122_);
lean_dec(v_machine_3095_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3184_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v_messageHead_3130_; lean_object* v_messageCount_3131_; lean_object* v_bodyBytesRead_3132_; lean_object* v_headerBytesRead_3133_; uint8_t v_peerClosed_3134_; uint8_t v_inputStopped_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3181_; 
v_messageHead_3130_ = lean_ctor_get(v_reader_3118_, 2);
v_messageCount_3131_ = lean_ctor_get(v_reader_3118_, 3);
v_bodyBytesRead_3132_ = lean_ctor_get(v_reader_3118_, 4);
v_headerBytesRead_3133_ = lean_ctor_get(v_reader_3118_, 5);
v_peerClosed_3134_ = lean_ctor_get_uint8(v_reader_3118_, sizeof(void*)*6);
v_inputStopped_3135_ = lean_ctor_get_uint8(v_reader_3118_, sizeof(void*)*6 + 1);
v_isSharedCheck_3181_ = !lean_is_exclusive(v_reader_3118_);
if (v_isSharedCheck_3181_ == 0)
{
lean_object* v_unused_3182_; lean_object* v_unused_3183_; 
v_unused_3182_ = lean_ctor_get(v_reader_3118_, 1);
lean_dec(v_unused_3182_);
v_unused_3183_ = lean_ctor_get(v_reader_3118_, 0);
lean_dec(v_unused_3183_);
v___x_3137_ = v_reader_3118_;
v_isShared_3138_ = v_isSharedCheck_3181_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_headerBytesRead_3133_);
lean_inc(v_bodyBytesRead_3132_);
lean_inc(v_messageCount_3131_);
lean_inc(v_messageHead_3130_);
lean_dec(v_reader_3118_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3181_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v_array_3139_; lean_object* v_idx_3140_; uint8_t v___x_3141_; lean_object* v___y_3143_; lean_object* v___x_3172_; uint8_t v___x_3173_; 
v_array_3139_ = lean_ctor_get(v_input_3121_, 0);
lean_inc_ref(v_array_3139_);
v_idx_3140_ = lean_ctor_get(v_input_3121_, 1);
lean_inc(v_idx_3140_);
lean_dec_ref(v_input_3121_);
v___x_3141_ = 0;
v___x_3172_ = lean_byte_array_size(v_array_3139_);
v___x_3173_ = lean_nat_dec_le(v___x_3172_, v_idx_3140_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3174_ = l_ByteArray_extract(v_array_3139_, v_idx_3140_, v___x_3172_);
lean_dec_ref(v_array_3139_);
v___x_3175_ = lean_unsigned_to_nat(0u);
v___x_3176_ = lean_byte_array_size(v___x_3174_);
v___x_3177_ = lean_byte_array_size(v_val_3091_);
v___x_3178_ = lean_byte_array_copy_slice(v_val_3091_, v___x_3175_, v___x_3174_, v___x_3176_, v___x_3177_, v___x_3173_);
lean_dec_ref(v_val_3091_);
v___x_3179_ = l_ByteArray_mkIterator(v___x_3178_);
v___y_3143_ = v___x_3179_;
goto v___jp_3142_;
}
else
{
lean_object* v___x_3180_; 
lean_dec(v_idx_3140_);
lean_dec_ref(v_array_3139_);
v___x_3180_ = l_ByteArray_mkIterator(v_val_3091_);
v___y_3143_ = v___x_3180_;
goto v___jp_3142_;
}
v___jp_3142_:
{
lean_object* v_maxHeaderBytes_3144_; lean_object* v_maxStartLineLength_3145_; lean_object* v_maxChunkLineLength_3146_; lean_object* v_maxBodySize_3147_; lean_object* v_array_3148_; lean_object* v_idx_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; 
v_maxHeaderBytes_3144_ = lean_ctor_get(v_config_3123_, 2);
v_maxStartLineLength_3145_ = lean_ctor_get(v_config_3123_, 5);
v_maxChunkLineLength_3146_ = lean_ctor_get(v_config_3123_, 13);
v_maxBodySize_3147_ = lean_ctor_get(v_config_3123_, 15);
v_array_3148_ = lean_ctor_get(v___y_3143_, 0);
v_idx_3149_ = lean_ctor_get(v___y_3143_, 1);
v___x_3150_ = lean_nat_add(v_maxBodySize_3147_, v_maxHeaderBytes_3144_);
v___x_3151_ = lean_nat_add(v___x_3150_, v_maxStartLineLength_3145_);
lean_dec(v___x_3150_);
v___x_3152_ = lean_nat_add(v___x_3151_, v_maxChunkLineLength_3146_);
lean_dec(v___x_3151_);
v___x_3153_ = lean_byte_array_size(v_array_3148_);
v___x_3154_ = lean_nat_sub(v___x_3153_, v_idx_3149_);
v___x_3155_ = lean_nat_dec_lt(v___x_3152_, v___x_3154_);
lean_dec(v___x_3154_);
lean_dec(v___x_3152_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3157_; 
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 1, v___y_3143_);
v___x_3157_ = v___x_3137_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_state_3119_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v___y_3143_);
lean_ctor_set(v_reuseFailAlloc_3161_, 2, v_messageHead_3130_);
lean_ctor_set(v_reuseFailAlloc_3161_, 3, v_messageCount_3131_);
lean_ctor_set(v_reuseFailAlloc_3161_, 4, v_bodyBytesRead_3132_);
lean_ctor_set(v_reuseFailAlloc_3161_, 5, v_headerBytesRead_3133_);
lean_ctor_set_uint8(v_reuseFailAlloc_3161_, sizeof(void*)*6, v_peerClosed_3134_);
lean_ctor_set_uint8(v_reuseFailAlloc_3161_, sizeof(void*)*6 + 1, v_inputStopped_3135_);
v___x_3157_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v_machine_3159_; 
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3157_);
v_machine_3159_ = v___x_3128_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_writer_3122_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_config_3123_);
lean_ctor_set(v_reuseFailAlloc_3160_, 3, v_events_3124_);
lean_ctor_set(v_reuseFailAlloc_3160_, 4, v_error_3120_);
lean_ctor_set(v_reuseFailAlloc_3160_, 5, v_date_3125_);
lean_ctor_set_uint8(v_reuseFailAlloc_3160_, sizeof(void*)*6, v_keepAlive_3126_);
v_machine_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_ctor_set_uint8(v_machine_3159_, sizeof(void*)*6 + 1, v___x_3141_);
v___y_3109_ = v_machine_3159_;
goto v___jp_3108_;
}
}
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3166_; 
lean_dec(v_state_3119_);
v___x_3162_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_3163_ = lean_array_push(v_events_3124_, v___x_3162_);
v___x_3164_ = lean_box(6);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 1, v___y_3143_);
lean_ctor_set(v___x_3137_, 0, v___x_3164_);
v___x_3166_ = v___x_3137_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v___y_3143_);
lean_ctor_set(v_reuseFailAlloc_3171_, 2, v_messageHead_3130_);
lean_ctor_set(v_reuseFailAlloc_3171_, 3, v_messageCount_3131_);
lean_ctor_set(v_reuseFailAlloc_3171_, 4, v_bodyBytesRead_3132_);
lean_ctor_set(v_reuseFailAlloc_3171_, 5, v_headerBytesRead_3133_);
lean_ctor_set_uint8(v_reuseFailAlloc_3171_, sizeof(void*)*6, v_peerClosed_3134_);
lean_ctor_set_uint8(v_reuseFailAlloc_3171_, sizeof(void*)*6 + 1, v_inputStopped_3135_);
v___x_3166_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3167_; lean_object* v___x_3169_; 
v___x_3167_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 4, v___x_3167_);
lean_ctor_set(v___x_3128_, 3, v___x_3163_);
lean_ctor_set(v___x_3128_, 0, v___x_3166_);
v___x_3169_ = v___x_3128_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3166_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_writer_3122_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_config_3123_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3170_, 5, v_date_3125_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_ctor_set_uint8(v___x_3169_, sizeof(void*)*6, v___x_3141_);
lean_ctor_set_uint8(v___x_3169_, sizeof(void*)*6 + 1, v___x_3141_);
v___y_3109_ = v___x_3169_;
goto v___jp_3108_;
}
}
}
}
}
}
}
else
{
lean_dec(v_state_3119_);
lean_dec_ref(v_reader_3118_);
lean_dec_ref(v_val_3091_);
v___y_3109_ = v_machine_3095_;
goto v___jp_3108_;
}
}
v___jp_3108_:
{
lean_object* v___x_3111_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v___y_3109_);
v___x_3111_ = v___x_3106_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___y_3109_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_requestStream_3096_);
lean_ctor_set(v_reuseFailAlloc_3117_, 2, v_timer_3097_);
lean_ctor_set(v_reuseFailAlloc_3117_, 3, v_response_3098_);
lean_ctor_set(v_reuseFailAlloc_3117_, 4, v_respStream_3099_);
lean_ctor_set(v_reuseFailAlloc_3117_, 5, v_inputWanted_3100_);
lean_ctor_set(v_reuseFailAlloc_3117_, 6, v_handler_3101_);
lean_ctor_set(v_reuseFailAlloc_3117_, 7, v_pendingHead_3102_);
lean_ctor_set(v_reuseFailAlloc_3117_, 8, v_dateSecond_3103_);
lean_ctor_set_uint8(v_reuseFailAlloc_3117_, sizeof(void*)*9, v_requestEnded_3104_);
v___x_3111_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
uint8_t v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3112_ = 0;
v___x_3113_ = lean_box(v___x_3112_);
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3111_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
v___x_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
return v___x_3116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_3188_, lean_object* v_____r_3189_, lean_object* v_st_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3188_, v_____r_3189_, v_st_3190_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_3193_, lean_object* v_machine_3194_, lean_object* v_requestStream_3195_, lean_object* v_response_3196_, lean_object* v_respStream_3197_, lean_object* v_inputWanted_3198_, lean_object* v_handler_3199_, lean_object* v_pendingHead_3200_, lean_object* v_dateSecond_3201_, uint8_t v_requestEnded_3202_, lean_object* v___f_3203_, lean_object* v_x_3204_){
_start:
{
if (lean_obj_tag(v_x_3204_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3214_; 
lean_dec_ref(v___f_3203_);
lean_dec(v_dateSecond_3201_);
lean_dec(v_pendingHead_3200_);
lean_dec(v_handler_3199_);
lean_dec(v_inputWanted_3198_);
lean_dec(v_respStream_3197_);
lean_dec_ref(v_response_3196_);
lean_dec_ref(v_requestStream_3195_);
lean_dec_ref(v_machine_3194_);
v_a_3206_ = lean_ctor_get(v_x_3204_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_x_3204_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3208_ = v_x_3204_;
v_isShared_3209_ = v_isSharedCheck_3214_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v_x_3204_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3214_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
lean_object* v___x_3212_; 
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
return v___x_3212_;
}
}
}
else
{
lean_object* v_a_3215_; lean_object* v_headerTimeout_3216_; lean_object* v_second_3217_; lean_object* v_nano_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v_second_3222_; lean_object* v_nano_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v_nanos_3226_; lean_object* v___x_3227_; lean_object* v_nanos_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v_a_3215_ = lean_ctor_get(v_x_3204_, 0);
lean_inc(v_a_3215_);
lean_dec_ref_known(v_x_3204_, 1);
v_headerTimeout_3216_ = lean_ctor_get(v_config_3193_, 6);
v_second_3217_ = lean_ctor_get(v_a_3215_, 0);
lean_inc(v_second_3217_);
v_nano_3218_ = lean_ctor_get(v_a_3215_, 1);
lean_inc(v_nano_3218_);
lean_dec(v_a_3215_);
v___x_3219_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__2);
v___x_3220_ = lean_int_mul(v_headerTimeout_3216_, v___x_3219_);
v___x_3221_ = l_Std_Time_Duration_ofNanoseconds(v___x_3220_);
lean_dec(v___x_3220_);
v_second_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_second_3222_);
v_nano_3223_ = lean_ctor_get(v___x_3221_, 1);
lean_inc(v_nano_3223_);
lean_dec_ref(v___x_3221_);
v___x_3224_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__12___closed__0);
v___x_3225_ = lean_int_mul(v_second_3217_, v___x_3224_);
lean_dec(v_second_3217_);
v_nanos_3226_ = lean_int_add(v___x_3225_, v_nano_3218_);
lean_dec(v_nano_3218_);
lean_dec(v___x_3225_);
v___x_3227_ = lean_int_mul(v_second_3222_, v___x_3224_);
lean_dec(v_second_3222_);
v_nanos_3228_ = lean_int_add(v___x_3227_, v_nano_3223_);
lean_dec(v_nano_3223_);
lean_dec(v___x_3227_);
v___x_3229_ = lean_int_add(v_nanos_3226_, v_nanos_3228_);
lean_dec(v_nanos_3228_);
lean_dec(v_nanos_3226_);
v___x_3230_ = l_Std_Time_Duration_ofNanoseconds(v___x_3229_);
lean_dec(v___x_3229_);
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
v___x_3232_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_3232_, 0, v_machine_3194_);
lean_ctor_set(v___x_3232_, 1, v_requestStream_3195_);
lean_ctor_set(v___x_3232_, 2, v___x_3231_);
lean_ctor_set(v___x_3232_, 3, v_response_3196_);
lean_ctor_set(v___x_3232_, 4, v_respStream_3197_);
lean_ctor_set(v___x_3232_, 5, v_inputWanted_3198_);
lean_ctor_set(v___x_3232_, 6, v_handler_3199_);
lean_ctor_set(v___x_3232_, 7, v_pendingHead_3200_);
lean_ctor_set(v___x_3232_, 8, v_dateSecond_3201_);
lean_ctor_set_uint8(v___x_3232_, sizeof(void*)*9, v_requestEnded_3202_);
v___x_3233_ = lean_box(0);
v___x_3234_ = lean_apply_3(v___f_3203_, v___x_3233_, v___x_3232_, lean_box(0));
return v___x_3234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_3235_, lean_object* v_machine_3236_, lean_object* v_requestStream_3237_, lean_object* v_response_3238_, lean_object* v_respStream_3239_, lean_object* v_inputWanted_3240_, lean_object* v_handler_3241_, lean_object* v_pendingHead_3242_, lean_object* v_dateSecond_3243_, lean_object* v_requestEnded_3244_, lean_object* v___f_3245_, lean_object* v_x_3246_, lean_object* v___y_3247_){
_start:
{
uint8_t v_requestEnded_boxed_3248_; lean_object* v_res_3249_; 
v_requestEnded_boxed_3248_ = lean_unbox(v_requestEnded_3244_);
v_res_3249_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_3235_, v_machine_3236_, v_requestStream_3237_, v_response_3238_, v_respStream_3239_, v_inputWanted_3240_, v_handler_3241_, v_pendingHead_3242_, v_dateSecond_3243_, v_requestEnded_boxed_3248_, v___f_3245_, v_x_3246_);
lean_dec_ref(v_config_3235_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_3250_, lean_object* v_requestStream_3251_, lean_object* v_timer_3252_, lean_object* v_response_3253_, lean_object* v_inputWanted_3254_, lean_object* v_handler_3255_, lean_object* v_pendingHead_3256_, lean_object* v_dateSecond_3257_, uint8_t v_requestEnded_3258_, lean_object* v_____r_3259_){
_start:
{
lean_object* v_writer_3261_; lean_object* v_reader_3262_; lean_object* v_config_3263_; lean_object* v_events_3264_; lean_object* v_error_3265_; lean_object* v_date_3266_; uint8_t v_keepAlive_3267_; uint8_t v_pullBodyStalled_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3297_; 
v_writer_3261_ = lean_ctor_get(v_machine_3250_, 1);
v_reader_3262_ = lean_ctor_get(v_machine_3250_, 0);
v_config_3263_ = lean_ctor_get(v_machine_3250_, 2);
v_events_3264_ = lean_ctor_get(v_machine_3250_, 3);
v_error_3265_ = lean_ctor_get(v_machine_3250_, 4);
v_date_3266_ = lean_ctor_get(v_machine_3250_, 5);
v_keepAlive_3267_ = lean_ctor_get_uint8(v_machine_3250_, sizeof(void*)*6);
v_pullBodyStalled_3268_ = lean_ctor_get_uint8(v_machine_3250_, sizeof(void*)*6 + 1);
v_isSharedCheck_3297_ = !lean_is_exclusive(v_machine_3250_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3270_ = v_machine_3250_;
v_isShared_3271_ = v_isSharedCheck_3297_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_date_3266_);
lean_inc(v_error_3265_);
lean_inc(v_events_3264_);
lean_inc(v_config_3263_);
lean_inc(v_writer_3261_);
lean_inc(v_reader_3262_);
lean_dec(v_machine_3250_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3297_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v_userData_3272_; lean_object* v_outputData_3273_; lean_object* v_state_3274_; lean_object* v_knownSize_3275_; lean_object* v_messageHead_3276_; uint8_t v_omitBody_3277_; lean_object* v_userDataBytes_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3296_; 
v_userData_3272_ = lean_ctor_get(v_writer_3261_, 0);
v_outputData_3273_ = lean_ctor_get(v_writer_3261_, 1);
v_state_3274_ = lean_ctor_get(v_writer_3261_, 2);
v_knownSize_3275_ = lean_ctor_get(v_writer_3261_, 3);
v_messageHead_3276_ = lean_ctor_get(v_writer_3261_, 4);
v_omitBody_3277_ = lean_ctor_get_uint8(v_writer_3261_, sizeof(void*)*6 + 1);
v_userDataBytes_3278_ = lean_ctor_get(v_writer_3261_, 5);
v_isSharedCheck_3296_ = !lean_is_exclusive(v_writer_3261_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3280_ = v_writer_3261_;
v_isShared_3281_ = v_isSharedCheck_3296_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_userDataBytes_3278_);
lean_inc(v_messageHead_3276_);
lean_inc(v_knownSize_3275_);
lean_inc(v_state_3274_);
lean_inc(v_outputData_3273_);
lean_inc(v_userData_3272_);
lean_dec(v_writer_3261_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3296_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
uint8_t v___x_3282_; lean_object* v___x_3284_; 
v___x_3282_ = 1;
if (v_isShared_3281_ == 0)
{
v___x_3284_ = v___x_3280_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_userData_3272_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_outputData_3273_);
lean_ctor_set(v_reuseFailAlloc_3295_, 2, v_state_3274_);
lean_ctor_set(v_reuseFailAlloc_3295_, 3, v_knownSize_3275_);
lean_ctor_set(v_reuseFailAlloc_3295_, 4, v_messageHead_3276_);
lean_ctor_set(v_reuseFailAlloc_3295_, 5, v_userDataBytes_3278_);
lean_ctor_set_uint8(v_reuseFailAlloc_3295_, sizeof(void*)*6 + 1, v_omitBody_3277_);
v___x_3284_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3286_; 
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*6, v___x_3282_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 1, v___x_3284_);
v___x_3286_ = v___x_3270_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_reader_3262_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v___x_3284_);
lean_ctor_set(v_reuseFailAlloc_3294_, 2, v_config_3263_);
lean_ctor_set(v_reuseFailAlloc_3294_, 3, v_events_3264_);
lean_ctor_set(v_reuseFailAlloc_3294_, 4, v_error_3265_);
lean_ctor_set(v_reuseFailAlloc_3294_, 5, v_date_3266_);
lean_ctor_set_uint8(v_reuseFailAlloc_3294_, sizeof(void*)*6, v_keepAlive_3267_);
lean_ctor_set_uint8(v_reuseFailAlloc_3294_, sizeof(void*)*6 + 1, v_pullBodyStalled_3268_);
v___x_3286_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3287_ = lean_box(0);
v___x_3288_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v_requestStream_3251_);
lean_ctor_set(v___x_3288_, 2, v_timer_3252_);
lean_ctor_set(v___x_3288_, 3, v_response_3253_);
lean_ctor_set(v___x_3288_, 4, v___x_3287_);
lean_ctor_set(v___x_3288_, 5, v_inputWanted_3254_);
lean_ctor_set(v___x_3288_, 6, v_handler_3255_);
lean_ctor_set(v___x_3288_, 7, v_pendingHead_3256_);
lean_ctor_set(v___x_3288_, 8, v_dateSecond_3257_);
lean_ctor_set_uint8(v___x_3288_, sizeof(void*)*9, v_requestEnded_3258_);
v___x_3289_ = 0;
v___x_3290_ = lean_box(v___x_3289_);
v___x_3291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3288_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
return v___x_3293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_3298_, lean_object* v_requestStream_3299_, lean_object* v_timer_3300_, lean_object* v_response_3301_, lean_object* v_inputWanted_3302_, lean_object* v_handler_3303_, lean_object* v_pendingHead_3304_, lean_object* v_dateSecond_3305_, lean_object* v_requestEnded_3306_, lean_object* v_____r_3307_, lean_object* v___y_3308_){
_start:
{
uint8_t v_requestEnded_boxed_3309_; lean_object* v_res_3310_; 
v_requestEnded_boxed_3309_ = lean_unbox(v_requestEnded_3306_);
v_res_3310_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3298_, v_requestStream_3299_, v_timer_3300_, v_response_3301_, v_inputWanted_3302_, v_handler_3303_, v_pendingHead_3304_, v_dateSecond_3305_, v_requestEnded_boxed_3309_, v_____r_3307_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_3311_, lean_object* v_x_3312_){
_start:
{
if (lean_obj_tag(v_x_3312_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3322_; 
lean_dec_ref(v___f_3311_);
v_a_3314_ = lean_ctor_get(v_x_3312_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v_x_3312_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3316_ = v_x_3312_;
v_isShared_3317_ = v_isSharedCheck_3322_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v_x_3312_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3322_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
return v___x_3320_;
}
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3324_; 
v_a_3323_ = lean_ctor_get(v_x_3312_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v_x_3312_, 1);
v___x_3324_ = lean_apply_2(v___f_3311_, v_a_3323_, lean_box(0));
return v___x_3324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_3325_, lean_object* v_x_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_3325_, v_x_3326_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_3329_, lean_object* v_val_3330_, lean_object* v___f_3331_, lean_object* v___f_3332_, lean_object* v_x_3333_){
_start:
{
if (lean_obj_tag(v_x_3333_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3343_; 
lean_dec_ref(v___f_3332_);
lean_dec_ref(v___f_3331_);
lean_dec(v_val_3330_);
lean_dec_ref(v_close_3329_);
v_a_3335_ = lean_ctor_get(v_x_3333_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v_x_3333_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3337_ = v_x_3333_;
v_isShared_3338_ = v_isSharedCheck_3343_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v_x_3333_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3343_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
lean_object* v___x_3341_; 
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
return v___x_3341_;
}
}
}
else
{
lean_object* v_a_3344_; uint8_t v___x_3345_; 
v_a_3344_ = lean_ctor_get(v_x_3333_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v_x_3333_, 1);
v___x_3345_ = lean_unbox(v_a_3344_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; lean_object* v___x_3349_; 
lean_dec_ref(v___f_3332_);
v___x_3346_ = lean_unsigned_to_nat(0u);
v___x_3347_ = lean_apply_2(v_close_3329_, v_val_3330_, lean_box(0));
v___x_3348_ = lean_unbox(v_a_3344_);
lean_dec(v_a_3344_);
v___x_3349_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3346_, v___x_3348_, v___x_3347_, v___f_3331_);
return v___x_3349_;
}
else
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
lean_dec(v_a_3344_);
lean_dec_ref(v___f_3331_);
lean_dec(v_val_3330_);
lean_dec_ref(v_close_3329_);
v___x_3350_ = lean_box(0);
v___x_3351_ = lean_apply_2(v___f_3332_, v___x_3350_, lean_box(0));
return v___x_3351_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_3352_, lean_object* v_val_3353_, lean_object* v___f_3354_, lean_object* v___f_3355_, lean_object* v_x_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_3352_, v_val_3353_, v___f_3354_, v___f_3355_, v_x_3356_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_inst_3359_, lean_object* v_handler_3360_, lean_object* v_x_3361_){
_start:
{
if (lean_obj_tag(v_x_3361_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; 
v_a_3363_ = lean_ctor_get(v_x_3361_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v_x_3361_, 1);
v___x_3364_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_3359_, v_handler_3360_, v_a_3363_);
return v___x_3364_;
}
else
{
lean_object* v___x_3365_; 
lean_dec(v_handler_3360_);
lean_dec_ref(v_inst_3359_);
v___x_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3365_, 0, v_x_3361_);
return v___x_3365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_inst_3366_, lean_object* v_handler_3367_, lean_object* v_x_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_inst_3366_, v_handler_3367_, v_x_3368_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object* v_st_3371_, lean_object* v_____r_3372_){
_start:
{
uint8_t v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3374_ = 0;
v___x_3375_ = lean_box(v___x_3374_);
v___x_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3376_, 0, v_st_3371_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
v___x_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_st_3379_, lean_object* v_____r_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_3379_, v_____r_3380_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_state_3383_, lean_object* v_x_3384_){
_start:
{
if (lean_obj_tag(v_x_3384_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3394_; 
lean_dec_ref(v_state_3383_);
v_a_3386_ = lean_ctor_get(v_x_3384_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_x_3384_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3388_ = v_x_3384_;
v_isShared_3389_ = v_isSharedCheck_3394_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v_x_3384_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3394_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
return v___x_3392_;
}
}
}
else
{
lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3425_; 
v_isSharedCheck_3425_ = !lean_is_exclusive(v_x_3384_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; 
v_unused_3426_ = lean_ctor_get(v_x_3384_, 0);
lean_dec(v_unused_3426_);
v___x_3396_ = v_x_3384_;
v_isShared_3397_ = v_isSharedCheck_3425_;
goto v_resetjp_3395_;
}
else
{
lean_dec(v_x_3384_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3425_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v_machine_3398_; lean_object* v_requestStream_3399_; lean_object* v_timer_3400_; lean_object* v_response_3401_; lean_object* v_respStream_3402_; lean_object* v_inputWanted_3403_; lean_object* v_pendingHead_3404_; lean_object* v_dateSecond_3405_; uint8_t v_requestEnded_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3423_; 
v_machine_3398_ = lean_ctor_get(v_state_3383_, 0);
v_requestStream_3399_ = lean_ctor_get(v_state_3383_, 1);
v_timer_3400_ = lean_ctor_get(v_state_3383_, 2);
v_response_3401_ = lean_ctor_get(v_state_3383_, 3);
v_respStream_3402_ = lean_ctor_get(v_state_3383_, 4);
v_inputWanted_3403_ = lean_ctor_get(v_state_3383_, 5);
v_pendingHead_3404_ = lean_ctor_get(v_state_3383_, 7);
v_dateSecond_3405_ = lean_ctor_get(v_state_3383_, 8);
v_requestEnded_3406_ = lean_ctor_get_uint8(v_state_3383_, sizeof(void*)*9);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_state_3383_);
if (v_isSharedCheck_3423_ == 0)
{
lean_object* v_unused_3424_; 
v_unused_3424_ = lean_ctor_get(v_state_3383_, 6);
lean_dec(v_unused_3424_);
v___x_3408_ = v_state_3383_;
v_isShared_3409_ = v_isSharedCheck_3423_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_dateSecond_3405_);
lean_inc(v_pendingHead_3404_);
lean_inc(v_inputWanted_3403_);
lean_inc(v_respStream_3402_);
lean_inc(v_response_3401_);
lean_inc(v_timer_3400_);
lean_inc(v_requestStream_3399_);
lean_inc(v_machine_3398_);
lean_dec(v_state_3383_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3423_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3410_ = lean_box(52);
v___x_3411_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3398_, v___x_3410_);
v___x_3412_ = lean_box(0);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 6, v___x_3412_);
lean_ctor_set(v___x_3408_, 0, v___x_3411_);
v___x_3414_ = v___x_3408_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_requestStream_3399_);
lean_ctor_set(v_reuseFailAlloc_3422_, 2, v_timer_3400_);
lean_ctor_set(v_reuseFailAlloc_3422_, 3, v_response_3401_);
lean_ctor_set(v_reuseFailAlloc_3422_, 4, v_respStream_3402_);
lean_ctor_set(v_reuseFailAlloc_3422_, 5, v_inputWanted_3403_);
lean_ctor_set(v_reuseFailAlloc_3422_, 6, v___x_3412_);
lean_ctor_set(v_reuseFailAlloc_3422_, 7, v_pendingHead_3404_);
lean_ctor_set(v_reuseFailAlloc_3422_, 8, v_dateSecond_3405_);
lean_ctor_set_uint8(v_reuseFailAlloc_3422_, sizeof(void*)*9, v_requestEnded_3406_);
v___x_3414_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
uint8_t v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3419_; 
v___x_3415_ = 0;
v___x_3416_ = lean_box(v___x_3415_);
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3414_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3417_);
v___x_3419_ = v___x_3396_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; 
v___x_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
return v___x_3420_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_state_3427_, lean_object* v_x_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v_res_3430_; 
v_res_3430_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_state_3427_, v_x_3428_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(uint8_t v___y_3431_, lean_object* v_x_3432_){
_start:
{
if (lean_obj_tag(v_x_3432_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3442_; 
v_a_3434_ = lean_ctor_get(v_x_3432_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_x_3432_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3436_ = v_x_3432_;
v_isShared_3437_ = v_isSharedCheck_3442_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v_x_3432_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3442_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3440_; 
v___x_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
return v___x_3440_;
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3462_; 
v_a_3443_ = lean_ctor_get(v_x_3432_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_x_3432_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3445_ = v_x_3432_;
v_isShared_3446_ = v_isSharedCheck_3462_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v_x_3432_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3462_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v_fst_3447_; lean_object* v_snd_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3461_; 
v_fst_3447_ = lean_ctor_get(v_a_3443_, 0);
v_snd_3448_ = lean_ctor_get(v_a_3443_, 1);
v_isSharedCheck_3461_ = !lean_is_exclusive(v_a_3443_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3450_ = v_a_3443_;
v_isShared_3451_ = v_isSharedCheck_3461_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_snd_3448_);
lean_inc(v_fst_3447_);
lean_dec(v_a_3443_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3461_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3452_ = lean_box(v___y_3431_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 1, v___x_3452_);
lean_ctor_set(v___x_3450_, 0, v_snd_3448_);
v___x_3454_ = v___x_3450_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_snd_3448_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3455_, 0, v_fst_3447_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3455_);
v___x_3457_ = v___x_3445_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
return v___x_3458_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v___y_3463_, lean_object* v_x_3464_, lean_object* v___y_3465_){
_start:
{
uint8_t v___y_8098__boxed_3466_; lean_object* v_res_3467_; 
v___y_8098__boxed_3466_ = lean_unbox(v___y_3463_);
v_res_3467_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v___y_8098__boxed_3466_, v_x_3464_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(lean_object* v_requestStream_3468_, lean_object* v_timer_3469_, lean_object* v_response_3470_, lean_object* v_inputWanted_3471_, lean_object* v_handler_3472_, lean_object* v_pendingHead_3473_, lean_object* v_dateSecond_3474_, uint8_t v_requestEnded_3475_, lean_object* v_____x_3476_){
_start:
{
lean_object* v_snd_3478_; lean_object* v_fst_3479_; lean_object* v_fst_3480_; lean_object* v_snd_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3491_; 
v_snd_3478_ = lean_ctor_get(v_____x_3476_, 1);
lean_inc(v_snd_3478_);
v_fst_3479_ = lean_ctor_get(v_____x_3476_, 0);
lean_inc(v_fst_3479_);
lean_dec_ref(v_____x_3476_);
v_fst_3480_ = lean_ctor_get(v_snd_3478_, 0);
v_snd_3481_ = lean_ctor_get(v_snd_3478_, 1);
v_isSharedCheck_3491_ = !lean_is_exclusive(v_snd_3478_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3483_ = v_snd_3478_;
v_isShared_3484_ = v_isSharedCheck_3491_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_snd_3481_);
lean_inc(v_fst_3480_);
lean_dec(v_snd_3478_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3491_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v___x_3487_; 
v___x_3485_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_3485_, 0, v_fst_3479_);
lean_ctor_set(v___x_3485_, 1, v_requestStream_3468_);
lean_ctor_set(v___x_3485_, 2, v_timer_3469_);
lean_ctor_set(v___x_3485_, 3, v_response_3470_);
lean_ctor_set(v___x_3485_, 4, v_fst_3480_);
lean_ctor_set(v___x_3485_, 5, v_inputWanted_3471_);
lean_ctor_set(v___x_3485_, 6, v_handler_3472_);
lean_ctor_set(v___x_3485_, 7, v_pendingHead_3473_);
lean_ctor_set(v___x_3485_, 8, v_dateSecond_3474_);
lean_ctor_set_uint8(v___x_3485_, sizeof(void*)*9, v_requestEnded_3475_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3485_);
v___x_3487_ = v___x_3483_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_snd_3481_);
v___x_3487_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
return v___x_3489_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v_requestStream_3492_, lean_object* v_timer_3493_, lean_object* v_response_3494_, lean_object* v_inputWanted_3495_, lean_object* v_handler_3496_, lean_object* v_pendingHead_3497_, lean_object* v_dateSecond_3498_, lean_object* v_requestEnded_3499_, lean_object* v_____x_3500_, lean_object* v___y_3501_){
_start:
{
uint8_t v_requestEnded_boxed_3502_; lean_object* v_res_3503_; 
v_requestEnded_boxed_3502_ = lean_unbox(v_requestEnded_3499_);
v_res_3503_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_requestStream_3492_, v_timer_3493_, v_response_3494_, v_inputWanted_3495_, v_handler_3496_, v_pendingHead_3497_, v_dateSecond_3498_, v_requestEnded_boxed_3502_, v_____x_3500_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v___f_3504_, lean_object* v_x_3505_){
_start:
{
if (lean_obj_tag(v_x_3505_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v___f_3504_);
v_a_3507_ = lean_ctor_get(v_x_3505_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v_x_3505_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3509_ = v_x_3505_;
v_isShared_3510_ = v_isSharedCheck_3515_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v_x_3505_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3515_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3513_; 
v___x_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
return v___x_3513_;
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3517_; 
v_a_3516_ = lean_ctor_get(v_x_3505_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v_x_3505_, 1);
v___x_3517_ = lean_apply_2(v___f_3504_, v_a_3516_, lean_box(0));
return v___x_3517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v___f_3518_, lean_object* v_x_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v___f_3518_, v_x_3519_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_snd_3522_, uint8_t v___x_3523_, lean_object* v_fst_3524_, lean_object* v_x_3525_){
_start:
{
if (lean_obj_tag(v_x_3525_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3535_; 
lean_dec_ref(v_fst_3524_);
lean_dec(v_snd_3522_);
v_a_3527_ = lean_ctor_get(v_x_3525_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_x_3525_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3529_ = v_x_3525_;
v_isShared_3530_ = v_isSharedCheck_3535_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v_x_3525_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3535_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
lean_object* v___x_3533_; 
v___x_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
return v___x_3533_;
}
}
}
else
{
lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3546_; 
v_isSharedCheck_3546_ = !lean_is_exclusive(v_x_3525_);
if (v_isSharedCheck_3546_ == 0)
{
lean_object* v_unused_3547_; 
v_unused_3547_ = lean_ctor_get(v_x_3525_, 0);
lean_dec(v_unused_3547_);
v___x_3537_ = v_x_3525_;
v_isShared_3538_ = v_isSharedCheck_3546_;
goto v_resetjp_3536_;
}
else
{
lean_dec(v_x_3525_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3546_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3539_ = lean_box(v___x_3523_);
v___x_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3540_, 0, v_snd_3522_);
lean_ctor_set(v___x_3540_, 1, v___x_3539_);
v___x_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3541_, 0, v_fst_3524_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3541_);
v___x_3543_ = v___x_3537_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3544_; 
v___x_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
return v___x_3544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_snd_3548_, lean_object* v___x_3549_, lean_object* v_fst_3550_, lean_object* v_x_3551_, lean_object* v___y_3552_){
_start:
{
uint8_t v___x_8231__boxed_3553_; lean_object* v_res_3554_; 
v___x_8231__boxed_3553_ = lean_unbox(v___x_3549_);
v_res_3554_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_snd_3548_, v___x_8231__boxed_3553_, v_fst_3550_, v_x_3551_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_inst_3555_, lean_object* v_handler_3556_, uint8_t v___y_3557_, lean_object* v___f_3558_, lean_object* v_x_3559_){
_start:
{
if (lean_obj_tag(v_x_3559_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v_a_3561_ = lean_ctor_get(v_x_3559_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v_x_3559_, 1);
v___x_3562_ = lean_unsigned_to_nat(0u);
v___x_3563_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_3555_, v_handler_3556_, v_a_3561_);
v___x_3564_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3562_, v___y_3557_, v___x_3563_, v___f_3558_);
return v___x_3564_;
}
else
{
lean_object* v___x_3565_; 
lean_dec_ref(v___f_3558_);
lean_dec(v_handler_3556_);
lean_dec_ref(v_inst_3555_);
v___x_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3565_, 0, v_x_3559_);
return v___x_3565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v_inst_3566_, lean_object* v_handler_3567_, lean_object* v___y_3568_, lean_object* v___f_3569_, lean_object* v_x_3570_, lean_object* v___y_3571_){
_start:
{
uint8_t v___y_8289__boxed_3572_; lean_object* v_res_3573_; 
v___y_8289__boxed_3572_ = lean_unbox(v___y_3568_);
v_res_3573_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_inst_3566_, v_handler_3567_, v___y_8289__boxed_3572_, v___f_3569_, v_x_3570_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(uint8_t v___y_3574_, lean_object* v___f_3575_, uint8_t v___x_3576_, lean_object* v_inst_3577_, lean_object* v_handler_3578_, lean_object* v_inst_3579_, lean_object* v___f_3580_, lean_object* v___f_3581_, lean_object* v_x_3582_){
_start:
{
if (lean_obj_tag(v_x_3582_) == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3592_; 
lean_dec_ref(v___f_3581_);
lean_dec_ref(v___f_3580_);
lean_dec_ref(v_inst_3579_);
lean_dec(v_handler_3578_);
lean_dec_ref(v_inst_3577_);
lean_dec_ref(v___f_3575_);
v_a_3584_ = lean_ctor_get(v_x_3582_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_x_3582_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3586_ = v_x_3582_;
v_isShared_3587_ = v_isSharedCheck_3592_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v_x_3582_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3592_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
return v___x_3590_;
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3626_; 
v_a_3593_ = lean_ctor_get(v_x_3582_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_x_3582_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3595_ = v_x_3582_;
v_isShared_3596_ = v_isSharedCheck_3626_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v_x_3582_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3626_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v_snd_3597_; 
v_snd_3597_ = lean_ctor_get(v_a_3593_, 1);
lean_inc(v_snd_3597_);
if (lean_obj_tag(v_snd_3597_) == 0)
{
lean_object* v_fst_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3613_; 
lean_dec_ref(v___f_3581_);
lean_dec_ref(v___f_3580_);
lean_dec_ref(v_inst_3579_);
lean_dec(v_handler_3578_);
lean_dec_ref(v_inst_3577_);
v_fst_3598_ = lean_ctor_get(v_a_3593_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_a_3593_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; 
v_unused_3614_ = lean_ctor_get(v_a_3593_, 1);
lean_dec(v_unused_3614_);
v___x_3600_ = v_a_3593_;
v_isShared_3601_ = v_isSharedCheck_3613_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_fst_3598_);
lean_dec(v_a_3593_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3613_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3602_ = lean_box(v___y_3574_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 1, v___x_3602_);
lean_ctor_set(v___x_3600_, 0, v_snd_3597_);
v___x_3604_ = v___x_3600_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_snd_3597_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3605_, 0, v_fst_3598_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = lean_unsigned_to_nat(0u);
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 0, v___x_3605_);
v___x_3608_ = v___x_3595_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3605_);
v___x_3608_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
v___x_3610_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3606_, v___y_3574_, v___x_3609_, v___f_3575_);
return v___x_3610_;
}
}
}
}
else
{
lean_object* v_fst_3615_; lean_object* v_val_3616_; lean_object* v___x_3617_; lean_object* v___f_3618_; lean_object* v___x_3619_; lean_object* v___f_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
lean_del_object(v___x_3595_);
lean_dec_ref(v___f_3575_);
v_fst_3615_ = lean_ctor_get(v_a_3593_, 0);
lean_inc_n(v_fst_3615_, 2);
lean_dec(v_a_3593_);
v_val_3616_ = lean_ctor_get(v_snd_3597_, 0);
lean_inc(v_val_3616_);
v___x_3617_ = lean_box(v___x_3576_);
v___f_3618_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 5, 3);
lean_closure_set(v___f_3618_, 0, v_snd_3597_);
lean_closure_set(v___f_3618_, 1, v___x_3617_);
lean_closure_set(v___f_3618_, 2, v_fst_3615_);
v___x_3619_ = lean_box(v___y_3574_);
v___f_3620_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 6, 4);
lean_closure_set(v___f_3620_, 0, v_inst_3577_);
lean_closure_set(v___f_3620_, 1, v_handler_3578_);
lean_closure_set(v___f_3620_, 2, v___x_3619_);
lean_closure_set(v___f_3620_, 3, v___f_3618_);
v___x_3621_ = lean_unsigned_to_nat(0u);
v___x_3622_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3579_, v_fst_3615_, v_val_3616_);
v___x_3623_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3621_, v___y_3574_, v___x_3622_, v___f_3580_);
v___x_3624_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3621_, v___y_3574_, v___x_3623_, v___f_3620_);
v___x_3625_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3621_, v___y_3574_, v___x_3624_, v___f_3581_);
return v___x_3625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v___y_3627_, lean_object* v___f_3628_, lean_object* v___x_3629_, lean_object* v_inst_3630_, lean_object* v_handler_3631_, lean_object* v_inst_3632_, lean_object* v___f_3633_, lean_object* v___f_3634_, lean_object* v_x_3635_, lean_object* v___y_3636_){
_start:
{
uint8_t v___y_8314__boxed_3637_; uint8_t v___x_8316__boxed_3638_; lean_object* v_res_3639_; 
v___y_8314__boxed_3637_ = lean_unbox(v___y_3627_);
v___x_8316__boxed_3638_ = lean_unbox(v___x_3629_);
v_res_3639_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v___y_8314__boxed_3637_, v___f_3628_, v___x_8316__boxed_3638_, v_inst_3630_, v_handler_3631_, v_inst_3632_, v___f_3633_, v___f_3634_, v_x_3635_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(uint8_t v___y_3640_, uint8_t v___x_3641_, lean_object* v_inst_3642_, lean_object* v_handler_3643_, lean_object* v_inst_3644_, lean_object* v___f_3645_, lean_object* v_a_3646_, lean_object* v_x_3647_){
_start:
{
if (lean_obj_tag(v_x_3647_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3657_; 
lean_dec_ref(v_a_3646_);
lean_dec_ref(v___f_3645_);
lean_dec_ref(v_inst_3644_);
lean_dec(v_handler_3643_);
lean_dec_ref(v_inst_3642_);
v_a_3649_ = lean_ctor_get(v_x_3647_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_x_3647_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3651_ = v_x_3647_;
v_isShared_3652_ = v_isSharedCheck_3657_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v_x_3647_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3657_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3649_);
v___x_3654_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; 
v___x_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
return v___x_3655_;
}
}
}
else
{
lean_object* v_a_3658_; lean_object* v_machine_3659_; lean_object* v_requestStream_3660_; lean_object* v_timer_3661_; lean_object* v_response_3662_; lean_object* v_inputWanted_3663_; lean_object* v_handler_3664_; lean_object* v_pendingHead_3665_; lean_object* v_dateSecond_3666_; uint8_t v_requestEnded_3667_; lean_object* v___x_3668_; lean_object* v___f_3669_; lean_object* v___f_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___f_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v_a_3658_ = lean_ctor_get(v_x_3647_, 0);
lean_inc(v_a_3658_);
lean_dec_ref_known(v_x_3647_, 1);
v_machine_3659_ = lean_ctor_get(v_a_3658_, 0);
lean_inc_ref(v_machine_3659_);
v_requestStream_3660_ = lean_ctor_get(v_a_3658_, 1);
lean_inc_ref(v_requestStream_3660_);
v_timer_3661_ = lean_ctor_get(v_a_3658_, 2);
lean_inc_ref(v_timer_3661_);
v_response_3662_ = lean_ctor_get(v_a_3658_, 3);
lean_inc_ref(v_response_3662_);
v_inputWanted_3663_ = lean_ctor_get(v_a_3658_, 5);
lean_inc(v_inputWanted_3663_);
v_handler_3664_ = lean_ctor_get(v_a_3658_, 6);
lean_inc(v_handler_3664_);
v_pendingHead_3665_ = lean_ctor_get(v_a_3658_, 7);
lean_inc(v_pendingHead_3665_);
v_dateSecond_3666_ = lean_ctor_get(v_a_3658_, 8);
lean_inc(v_dateSecond_3666_);
v_requestEnded_3667_ = lean_ctor_get_uint8(v_a_3658_, sizeof(void*)*9);
lean_dec(v_a_3658_);
v___x_3668_ = lean_box(v_requestEnded_3667_);
v___f_3669_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 10, 8);
lean_closure_set(v___f_3669_, 0, v_requestStream_3660_);
lean_closure_set(v___f_3669_, 1, v_timer_3661_);
lean_closure_set(v___f_3669_, 2, v_response_3662_);
lean_closure_set(v___f_3669_, 3, v_inputWanted_3663_);
lean_closure_set(v___f_3669_, 4, v_handler_3664_);
lean_closure_set(v___f_3669_, 5, v_pendingHead_3665_);
lean_closure_set(v___f_3669_, 6, v_dateSecond_3666_);
lean_closure_set(v___f_3669_, 7, v___x_3668_);
v___f_3670_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 3, 1);
lean_closure_set(v___f_3670_, 0, v___f_3669_);
v___x_3671_ = lean_box(v___y_3640_);
v___x_3672_ = lean_box(v___x_3641_);
lean_inc_ref(v_inst_3644_);
lean_inc_ref(v___f_3670_);
v___f_3673_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 10, 8);
lean_closure_set(v___f_3673_, 0, v___x_3671_);
lean_closure_set(v___f_3673_, 1, v___f_3670_);
lean_closure_set(v___f_3673_, 2, v___x_3672_);
lean_closure_set(v___f_3673_, 3, v_inst_3642_);
lean_closure_set(v___f_3673_, 4, v_handler_3643_);
lean_closure_set(v___f_3673_, 5, v_inst_3644_);
lean_closure_set(v___f_3673_, 6, v___f_3645_);
lean_closure_set(v___f_3673_, 7, v___f_3670_);
v___x_3674_ = lean_unsigned_to_nat(0u);
v___x_3675_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3644_, v_machine_3659_, v_a_3646_);
v___x_3676_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3674_, v___y_3640_, v___x_3675_, v___f_3673_);
return v___x_3676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v___y_3677_, lean_object* v___x_3678_, lean_object* v_inst_3679_, lean_object* v_handler_3680_, lean_object* v_inst_3681_, lean_object* v___f_3682_, lean_object* v_a_3683_, lean_object* v_x_3684_, lean_object* v___y_3685_){
_start:
{
uint8_t v___y_8427__boxed_3686_; uint8_t v___x_8428__boxed_3687_; lean_object* v_res_3688_; 
v___y_8427__boxed_3686_ = lean_unbox(v___y_3677_);
v___x_8428__boxed_3687_ = lean_unbox(v___x_3678_);
v_res_3688_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v___y_8427__boxed_3686_, v___x_8428__boxed_3687_, v_inst_3679_, v_handler_3680_, v_inst_3681_, v___f_3682_, v_a_3683_, v_x_3684_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(lean_object* v_machine_3689_, lean_object* v_requestStream_3690_, lean_object* v_timer_3691_, lean_object* v_response_3692_, lean_object* v_respStream_3693_, lean_object* v_inputWanted_3694_, lean_object* v___x_3695_, lean_object* v_pendingHead_3696_, lean_object* v_dateSecond_3697_, uint8_t v_requestEnded_3698_, uint8_t v___x_3699_, lean_object* v_x_3700_){
_start:
{
if (lean_obj_tag(v_x_3700_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3710_; 
lean_dec(v_dateSecond_3697_);
lean_dec(v_pendingHead_3696_);
lean_dec(v___x_3695_);
lean_dec(v_inputWanted_3694_);
lean_dec(v_respStream_3693_);
lean_dec_ref(v_response_3692_);
lean_dec_ref(v_timer_3691_);
lean_dec_ref(v_requestStream_3690_);
lean_dec_ref(v_machine_3689_);
v_a_3702_ = lean_ctor_get(v_x_3700_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_x_3700_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3704_ = v_x_3700_;
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v_x_3700_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3702_);
v___x_3707_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3708_; 
v___x_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
return v___x_3708_;
}
}
}
else
{
lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3723_; 
v_isSharedCheck_3723_ = !lean_is_exclusive(v_x_3700_);
if (v_isSharedCheck_3723_ == 0)
{
lean_object* v_unused_3724_; 
v_unused_3724_ = lean_ctor_get(v_x_3700_, 0);
lean_dec(v_unused_3724_);
v___x_3712_ = v_x_3700_;
v_isShared_3713_ = v_isSharedCheck_3723_;
goto v_resetjp_3711_;
}
else
{
lean_dec(v_x_3700_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3723_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3714_ = lean_box(52);
v___x_3715_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3689_, v___x_3714_);
v___x_3716_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
lean_ctor_set(v___x_3716_, 1, v_requestStream_3690_);
lean_ctor_set(v___x_3716_, 2, v_timer_3691_);
lean_ctor_set(v___x_3716_, 3, v_response_3692_);
lean_ctor_set(v___x_3716_, 4, v_respStream_3693_);
lean_ctor_set(v___x_3716_, 5, v_inputWanted_3694_);
lean_ctor_set(v___x_3716_, 6, v___x_3695_);
lean_ctor_set(v___x_3716_, 7, v_pendingHead_3696_);
lean_ctor_set(v___x_3716_, 8, v_dateSecond_3697_);
lean_ctor_set_uint8(v___x_3716_, sizeof(void*)*9, v_requestEnded_3698_);
v___x_3717_ = lean_box(v___x_3699_);
v___x_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v___x_3718_);
v___x_3720_ = v___x_3712_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
return v___x_3721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v_machine_3725_, lean_object* v_requestStream_3726_, lean_object* v_timer_3727_, lean_object* v_response_3728_, lean_object* v_respStream_3729_, lean_object* v_inputWanted_3730_, lean_object* v___x_3731_, lean_object* v_pendingHead_3732_, lean_object* v_dateSecond_3733_, lean_object* v_requestEnded_3734_, lean_object* v___x_3735_, lean_object* v_x_3736_, lean_object* v___y_3737_){
_start:
{
uint8_t v_requestEnded_boxed_3738_; uint8_t v___x_8490__boxed_3739_; lean_object* v_res_3740_; 
v_requestEnded_boxed_3738_ = lean_unbox(v_requestEnded_3734_);
v___x_8490__boxed_3739_ = lean_unbox(v___x_3735_);
v_res_3740_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v_machine_3725_, v_requestStream_3726_, v_timer_3727_, v_response_3728_, v_respStream_3729_, v_inputWanted_3730_, v___x_3731_, v_pendingHead_3732_, v_dateSecond_3733_, v_requestEnded_boxed_3738_, v___x_8490__boxed_3739_, v_x_3736_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(uint16_t v___x_3743_, lean_object* v_inst_3744_, lean_object* v_handler_3745_, uint8_t v___x_3746_, lean_object* v___f_3747_, lean_object* v_____r_3748_){
_start:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3750_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___closed__0));
v___x_3751_ = lean_uint16_to_nat(v___x_3743_);
v___x_3752_ = l_Nat_reprFast(v___x_3751_);
v___x_3753_ = lean_string_append(v___x_3750_, v___x_3752_);
lean_dec_ref(v___x_3752_);
v___x_3754_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___closed__1));
v___x_3755_ = lean_string_append(v___x_3753_, v___x_3754_);
v___x_3756_ = lean_mk_io_user_error(v___x_3755_);
v___x_3757_ = lean_unsigned_to_nat(0u);
v___x_3758_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_3744_, v_handler_3745_, v___x_3756_);
v___x_3759_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3757_, v___x_3746_, v___x_3758_, v___f_3747_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v___x_3760_, lean_object* v_inst_3761_, lean_object* v_handler_3762_, lean_object* v___x_3763_, lean_object* v___f_3764_, lean_object* v_____r_3765_, lean_object* v___y_3766_){
_start:
{
uint16_t v___x_8552__boxed_3767_; uint8_t v___x_8554__boxed_3768_; lean_object* v_res_3769_; 
v___x_8552__boxed_3767_ = lean_unbox(v___x_3760_);
v___x_8554__boxed_3768_ = lean_unbox(v___x_3763_);
v_res_3769_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v___x_8552__boxed_3767_, v_inst_3761_, v_handler_3762_, v___x_8554__boxed_3768_, v___f_3764_, v_____r_3765_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object* v_close_3770_, lean_object* v_body_3771_, uint8_t v___x_3772_, lean_object* v___f_3773_, lean_object* v___f_3774_, lean_object* v_x_3775_){
_start:
{
if (lean_obj_tag(v_x_3775_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3785_; 
lean_dec_ref(v___f_3774_);
lean_dec_ref(v___f_3773_);
lean_dec(v_body_3771_);
lean_dec_ref(v_close_3770_);
v_a_3777_ = lean_ctor_get(v_x_3775_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_x_3775_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3779_ = v_x_3775_;
v_isShared_3780_ = v_isSharedCheck_3785_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v_x_3775_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3785_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
return v___x_3783_;
}
}
}
else
{
lean_object* v_a_3786_; uint8_t v___x_3787_; 
v_a_3786_ = lean_ctor_get(v_x_3775_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v_x_3775_, 1);
v___x_3787_ = lean_unbox(v_a_3786_);
lean_dec(v_a_3786_);
if (v___x_3787_ == 0)
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
lean_dec_ref(v___f_3774_);
v___x_3788_ = lean_unsigned_to_nat(0u);
v___x_3789_ = lean_apply_2(v_close_3770_, v_body_3771_, lean_box(0));
v___x_3790_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3788_, v___x_3772_, v___x_3789_, v___f_3773_);
return v___x_3790_;
}
else
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
lean_dec_ref(v___f_3773_);
lean_dec(v_body_3771_);
lean_dec_ref(v_close_3770_);
v___x_3791_ = lean_box(0);
v___x_3792_ = lean_apply_2(v___f_3774_, v___x_3791_, lean_box(0));
return v___x_3792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v_close_3793_, lean_object* v_body_3794_, lean_object* v___x_3795_, lean_object* v___f_3796_, lean_object* v___f_3797_, lean_object* v_x_3798_, lean_object* v___y_3799_){
_start:
{
uint8_t v___x_8592__boxed_3800_; lean_object* v_res_3801_; 
v___x_8592__boxed_3800_ = lean_unbox(v___x_3795_);
v_res_3801_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_close_3793_, v_body_3794_, v___x_8592__boxed_3800_, v___f_3796_, v___f_3797_, v_x_3798_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(lean_object* v_state_3802_, lean_object* v_____r_3803_){
_start:
{
uint8_t v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3805_ = 0;
v___x_3806_ = lean_box(v___x_3805_);
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v_state_3802_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
v___x_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v_state_3810_, lean_object* v_____r_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v_state_3810_, v_____r_3811_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20(lean_object* v_close_3814_, lean_object* v_body_3815_, lean_object* v___f_3816_, lean_object* v___f_3817_, lean_object* v_x_3818_){
_start:
{
if (lean_obj_tag(v_x_3818_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3828_; 
lean_dec_ref(v___f_3817_);
lean_dec_ref(v___f_3816_);
lean_dec(v_body_3815_);
lean_dec_ref(v_close_3814_);
v_a_3820_ = lean_ctor_get(v_x_3818_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v_x_3818_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3822_ = v_x_3818_;
v_isShared_3823_ = v_isSharedCheck_3828_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v_x_3818_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3828_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
return v___x_3826_;
}
}
}
else
{
lean_object* v_a_3829_; uint8_t v___x_3830_; 
v_a_3829_ = lean_ctor_get(v_x_3818_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v_x_3818_, 1);
v___x_3830_ = lean_unbox(v_a_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; lean_object* v___x_3834_; 
lean_dec_ref(v___f_3817_);
v___x_3831_ = lean_unsigned_to_nat(0u);
v___x_3832_ = lean_apply_2(v_close_3814_, v_body_3815_, lean_box(0));
v___x_3833_ = lean_unbox(v_a_3829_);
lean_dec(v_a_3829_);
v___x_3834_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3831_, v___x_3833_, v___x_3832_, v___f_3816_);
return v___x_3834_;
}
else
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
lean_dec(v_a_3829_);
lean_dec_ref(v___f_3816_);
lean_dec(v_body_3815_);
lean_dec_ref(v_close_3814_);
v___x_3835_ = lean_box(0);
v___x_3836_ = lean_apply_2(v___f_3817_, v___x_3835_, lean_box(0));
return v___x_3836_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20___boxed(lean_object* v_close_3837_, lean_object* v_body_3838_, lean_object* v___f_3839_, lean_object* v___f_3840_, lean_object* v_x_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20(v_close_3837_, v_body_3838_, v___f_3839_, v___f_3840_, v_x_3841_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19(lean_object* v_state_3844_, lean_object* v_x_3845_){
_start:
{
if (lean_obj_tag(v_x_3845_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3855_; 
lean_dec_ref(v_state_3844_);
v_a_3847_ = lean_ctor_get(v_x_3845_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_x_3845_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3849_ = v_x_3845_;
v_isShared_3850_ = v_isSharedCheck_3855_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v_x_3845_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3855_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
return v___x_3853_;
}
}
}
else
{
lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3886_; 
v_isSharedCheck_3886_ = !lean_is_exclusive(v_x_3845_);
if (v_isSharedCheck_3886_ == 0)
{
lean_object* v_unused_3887_; 
v_unused_3887_ = lean_ctor_get(v_x_3845_, 0);
lean_dec(v_unused_3887_);
v___x_3857_ = v_x_3845_;
v_isShared_3858_ = v_isSharedCheck_3886_;
goto v_resetjp_3856_;
}
else
{
lean_dec(v_x_3845_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3886_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v_machine_3859_; lean_object* v_requestStream_3860_; lean_object* v_timer_3861_; lean_object* v_response_3862_; lean_object* v_respStream_3863_; lean_object* v_inputWanted_3864_; lean_object* v_handler_3865_; lean_object* v_pendingHead_3866_; lean_object* v_dateSecond_3867_; uint8_t v_requestEnded_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3885_; 
v_machine_3859_ = lean_ctor_get(v_state_3844_, 0);
v_requestStream_3860_ = lean_ctor_get(v_state_3844_, 1);
v_timer_3861_ = lean_ctor_get(v_state_3844_, 2);
v_response_3862_ = lean_ctor_get(v_state_3844_, 3);
v_respStream_3863_ = lean_ctor_get(v_state_3844_, 4);
v_inputWanted_3864_ = lean_ctor_get(v_state_3844_, 5);
v_handler_3865_ = lean_ctor_get(v_state_3844_, 6);
v_pendingHead_3866_ = lean_ctor_get(v_state_3844_, 7);
v_dateSecond_3867_ = lean_ctor_get(v_state_3844_, 8);
v_requestEnded_3868_ = lean_ctor_get_uint8(v_state_3844_, sizeof(void*)*9);
v_isSharedCheck_3885_ = !lean_is_exclusive(v_state_3844_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3870_ = v_state_3844_;
v_isShared_3871_ = v_isSharedCheck_3885_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_dateSecond_3867_);
lean_inc(v_pendingHead_3866_);
lean_inc(v_handler_3865_);
lean_inc(v_inputWanted_3864_);
lean_inc(v_respStream_3863_);
lean_inc(v_response_3862_);
lean_inc(v_timer_3861_);
lean_inc(v_requestStream_3860_);
lean_inc(v_machine_3859_);
lean_dec(v_state_3844_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3885_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3876_; 
v___x_3872_ = lean_box(31);
v___x_3873_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3859_, v___x_3872_);
v___x_3874_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon___redArg(v_handler_3865_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 6, v___x_3874_);
lean_ctor_set(v___x_3870_, 0, v___x_3873_);
v___x_3876_ = v___x_3870_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3873_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v_requestStream_3860_);
lean_ctor_set(v_reuseFailAlloc_3884_, 2, v_timer_3861_);
lean_ctor_set(v_reuseFailAlloc_3884_, 3, v_response_3862_);
lean_ctor_set(v_reuseFailAlloc_3884_, 4, v_respStream_3863_);
lean_ctor_set(v_reuseFailAlloc_3884_, 5, v_inputWanted_3864_);
lean_ctor_set(v_reuseFailAlloc_3884_, 6, v___x_3874_);
lean_ctor_set(v_reuseFailAlloc_3884_, 7, v_pendingHead_3866_);
lean_ctor_set(v_reuseFailAlloc_3884_, 8, v_dateSecond_3867_);
lean_ctor_set_uint8(v_reuseFailAlloc_3884_, sizeof(void*)*9, v_requestEnded_3868_);
v___x_3876_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
uint8_t v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3881_; 
v___x_3877_ = 0;
v___x_3878_ = lean_box(v___x_3877_);
v___x_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3876_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3879_);
v___x_3881_ = v___x_3857_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
lean_object* v___x_3882_; 
v___x_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
return v___x_3882_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19___boxed(lean_object* v_state_3888_, lean_object* v_x_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19(v_state_3888_, v_x_3889_);
return v_res_3891_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1(void){
_start:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3893_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___x_3894_ = lean_mk_io_user_error(v___x_3893_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_3895_, lean_object* v_inst_3896_, lean_object* v_handler_3897_, lean_object* v_config_3898_, lean_object* v_event_3899_, lean_object* v_state_3900_){
_start:
{
lean_object* v___y_3903_; lean_object* v___y_3904_; uint8_t v___y_3905_; lean_object* v_val_3906_; 
switch(lean_obj_tag(v_event_3899_))
{
case 0:
{
lean_object* v_x_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_4020_; 
lean_dec(v_handler_3897_);
lean_dec_ref(v_inst_3896_);
lean_dec_ref(v_inst_3895_);
v_x_3915_ = lean_ctor_get(v_event_3899_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v_event_3899_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_3917_ = v_event_3899_;
v_isShared_3918_ = v_isSharedCheck_4020_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_x_3915_);
lean_dec(v_event_3899_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_4020_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
if (lean_obj_tag(v_x_3915_) == 0)
{
lean_object* v_machine_3919_; lean_object* v_reader_3920_; lean_object* v_requestStream_3921_; lean_object* v_timer_3922_; lean_object* v_response_3923_; lean_object* v_respStream_3924_; lean_object* v_inputWanted_3925_; lean_object* v_handler_3926_; lean_object* v_pendingHead_3927_; lean_object* v_dateSecond_3928_; uint8_t v_requestEnded_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3972_; 
lean_dec_ref(v_config_3898_);
v_machine_3919_ = lean_ctor_get(v_state_3900_, 0);
lean_inc_ref(v_machine_3919_);
v_reader_3920_ = lean_ctor_get(v_machine_3919_, 0);
lean_inc_ref(v_reader_3920_);
v_requestStream_3921_ = lean_ctor_get(v_state_3900_, 1);
v_timer_3922_ = lean_ctor_get(v_state_3900_, 2);
v_response_3923_ = lean_ctor_get(v_state_3900_, 3);
v_respStream_3924_ = lean_ctor_get(v_state_3900_, 4);
v_inputWanted_3925_ = lean_ctor_get(v_state_3900_, 5);
v_handler_3926_ = lean_ctor_get(v_state_3900_, 6);
v_pendingHead_3927_ = lean_ctor_get(v_state_3900_, 7);
v_dateSecond_3928_ = lean_ctor_get(v_state_3900_, 8);
v_requestEnded_3929_ = lean_ctor_get_uint8(v_state_3900_, sizeof(void*)*9);
v_isSharedCheck_3972_ = !lean_is_exclusive(v_state_3900_);
if (v_isSharedCheck_3972_ == 0)
{
lean_object* v_unused_3973_; 
v_unused_3973_ = lean_ctor_get(v_state_3900_, 0);
lean_dec(v_unused_3973_);
v___x_3931_ = v_state_3900_;
v_isShared_3932_ = v_isSharedCheck_3972_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_dateSecond_3928_);
lean_inc(v_pendingHead_3927_);
lean_inc(v_handler_3926_);
lean_inc(v_inputWanted_3925_);
lean_inc(v_respStream_3924_);
lean_inc(v_response_3923_);
lean_inc(v_timer_3922_);
lean_inc(v_requestStream_3921_);
lean_dec(v_state_3900_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3972_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v_writer_3933_; lean_object* v_config_3934_; lean_object* v_events_3935_; lean_object* v_error_3936_; lean_object* v_date_3937_; uint8_t v_keepAlive_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3970_; 
v_writer_3933_ = lean_ctor_get(v_machine_3919_, 1);
v_config_3934_ = lean_ctor_get(v_machine_3919_, 2);
v_events_3935_ = lean_ctor_get(v_machine_3919_, 3);
v_error_3936_ = lean_ctor_get(v_machine_3919_, 4);
v_date_3937_ = lean_ctor_get(v_machine_3919_, 5);
v_keepAlive_3938_ = lean_ctor_get_uint8(v_machine_3919_, sizeof(void*)*6);
v_isSharedCheck_3970_ = !lean_is_exclusive(v_machine_3919_);
if (v_isSharedCheck_3970_ == 0)
{
lean_object* v_unused_3971_; 
v_unused_3971_ = lean_ctor_get(v_machine_3919_, 0);
lean_dec(v_unused_3971_);
v___x_3940_ = v_machine_3919_;
v_isShared_3941_ = v_isSharedCheck_3970_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_date_3937_);
lean_inc(v_error_3936_);
lean_inc(v_events_3935_);
lean_inc(v_config_3934_);
lean_inc(v_writer_3933_);
lean_dec(v_machine_3919_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3970_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v_state_3942_; lean_object* v_input_3943_; lean_object* v_messageHead_3944_; lean_object* v_messageCount_3945_; lean_object* v_bodyBytesRead_3946_; lean_object* v_headerBytesRead_3947_; uint8_t v_inputStopped_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3969_; 
v_state_3942_ = lean_ctor_get(v_reader_3920_, 0);
v_input_3943_ = lean_ctor_get(v_reader_3920_, 1);
v_messageHead_3944_ = lean_ctor_get(v_reader_3920_, 2);
v_messageCount_3945_ = lean_ctor_get(v_reader_3920_, 3);
v_bodyBytesRead_3946_ = lean_ctor_get(v_reader_3920_, 4);
v_headerBytesRead_3947_ = lean_ctor_get(v_reader_3920_, 5);
v_inputStopped_3948_ = lean_ctor_get_uint8(v_reader_3920_, sizeof(void*)*6 + 1);
v_isSharedCheck_3969_ = !lean_is_exclusive(v_reader_3920_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3950_ = v_reader_3920_;
v_isShared_3951_ = v_isSharedCheck_3969_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_headerBytesRead_3947_);
lean_inc(v_bodyBytesRead_3946_);
lean_inc(v_messageCount_3945_);
lean_inc(v_messageHead_3944_);
lean_inc(v_input_3943_);
lean_inc(v_state_3942_);
lean_dec(v_reader_3920_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3969_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
uint8_t v___x_3952_; lean_object* v___x_3954_; 
v___x_3952_ = 1;
if (v_isShared_3951_ == 0)
{
v___x_3954_ = v___x_3950_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_state_3942_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_input_3943_);
lean_ctor_set(v_reuseFailAlloc_3968_, 2, v_messageHead_3944_);
lean_ctor_set(v_reuseFailAlloc_3968_, 3, v_messageCount_3945_);
lean_ctor_set(v_reuseFailAlloc_3968_, 4, v_bodyBytesRead_3946_);
lean_ctor_set(v_reuseFailAlloc_3968_, 5, v_headerBytesRead_3947_);
lean_ctor_set_uint8(v_reuseFailAlloc_3968_, sizeof(void*)*6 + 1, v_inputStopped_3948_);
v___x_3954_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
uint8_t v___x_3955_; lean_object* v___x_3957_; 
lean_ctor_set_uint8(v___x_3954_, sizeof(void*)*6, v___x_3952_);
v___x_3955_ = 0;
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3954_);
v___x_3957_ = v___x_3940_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_writer_3933_);
lean_ctor_set(v_reuseFailAlloc_3967_, 2, v_config_3934_);
lean_ctor_set(v_reuseFailAlloc_3967_, 3, v_events_3935_);
lean_ctor_set(v_reuseFailAlloc_3967_, 4, v_error_3936_);
lean_ctor_set(v_reuseFailAlloc_3967_, 5, v_date_3937_);
lean_ctor_set_uint8(v_reuseFailAlloc_3967_, sizeof(void*)*6, v_keepAlive_3938_);
v___x_3957_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
lean_object* v___x_3959_; 
lean_ctor_set_uint8(v___x_3957_, sizeof(void*)*6 + 1, v___x_3955_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v___x_3957_);
v___x_3959_ = v___x_3931_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3957_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_requestStream_3921_);
lean_ctor_set(v_reuseFailAlloc_3966_, 2, v_timer_3922_);
lean_ctor_set(v_reuseFailAlloc_3966_, 3, v_response_3923_);
lean_ctor_set(v_reuseFailAlloc_3966_, 4, v_respStream_3924_);
lean_ctor_set(v_reuseFailAlloc_3966_, 5, v_inputWanted_3925_);
lean_ctor_set(v_reuseFailAlloc_3966_, 6, v_handler_3926_);
lean_ctor_set(v_reuseFailAlloc_3966_, 7, v_pendingHead_3927_);
lean_ctor_set(v_reuseFailAlloc_3966_, 8, v_dateSecond_3928_);
lean_ctor_set_uint8(v_reuseFailAlloc_3966_, sizeof(void*)*9, v_requestEnded_3929_);
v___x_3959_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3963_; 
v___x_3960_ = lean_box(v___x_3955_);
v___x_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3959_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
if (v_isShared_3918_ == 0)
{
lean_ctor_set_tag(v___x_3917_, 1);
lean_ctor_set(v___x_3917_, 0, v___x_3961_);
v___x_3963_ = v___x_3917_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3961_);
v___x_3963_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
lean_object* v___x_3964_; 
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
return v___x_3964_;
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
lean_object* v_val_3974_; lean_object* v_machine_3975_; lean_object* v_requestStream_3976_; lean_object* v_timer_3977_; lean_object* v_response_3978_; lean_object* v_respStream_3979_; lean_object* v_inputWanted_3980_; lean_object* v_handler_3981_; lean_object* v_pendingHead_3982_; lean_object* v_dateSecond_3983_; uint8_t v_requestEnded_3984_; lean_object* v___f_3985_; 
lean_del_object(v___x_3917_);
v_val_3974_ = lean_ctor_get(v_x_3915_, 0);
lean_inc_n(v_val_3974_, 2);
lean_dec_ref_known(v_x_3915_, 1);
v_machine_3975_ = lean_ctor_get(v_state_3900_, 0);
v_requestStream_3976_ = lean_ctor_get(v_state_3900_, 1);
v_timer_3977_ = lean_ctor_get(v_state_3900_, 2);
lean_inc_ref(v_timer_3977_);
v_response_3978_ = lean_ctor_get(v_state_3900_, 3);
v_respStream_3979_ = lean_ctor_get(v_state_3900_, 4);
v_inputWanted_3980_ = lean_ctor_get(v_state_3900_, 5);
v_handler_3981_ = lean_ctor_get(v_state_3900_, 6);
v_pendingHead_3982_ = lean_ctor_get(v_state_3900_, 7);
v_dateSecond_3983_ = lean_ctor_get(v_state_3900_, 8);
v_requestEnded_3984_ = lean_ctor_get_uint8(v_state_3900_, sizeof(void*)*9);
v___f_3985_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3985_, 0, v_val_3974_);
if (lean_obj_tag(v_timer_3977_) == 0)
{
lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_4016_; 
lean_inc(v_dateSecond_3983_);
lean_inc(v_pendingHead_3982_);
lean_inc(v_handler_3981_);
lean_inc(v_inputWanted_3980_);
lean_inc(v_respStream_3979_);
lean_inc_ref(v_response_3978_);
lean_inc_ref(v_requestStream_3976_);
lean_inc_ref(v_machine_3975_);
lean_dec(v_val_3974_);
lean_dec_ref(v_state_3900_);
v_isSharedCheck_4016_ = !lean_is_exclusive(v_timer_3977_);
if (v_isSharedCheck_4016_ == 0)
{
lean_object* v_unused_4017_; 
v_unused_4017_ = lean_ctor_get(v_timer_3977_, 0);
lean_dec(v_unused_4017_);
v___x_3987_ = v_timer_3977_;
v_isShared_3988_ = v_isSharedCheck_4016_;
goto v_resetjp_3986_;
}
else
{
lean_dec(v_timer_3977_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_4016_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___f_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; lean_object* v_val_3994_; lean_object* v___x_3999_; 
v___x_3989_ = lean_box(v_requestEnded_3984_);
v___f_3990_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_3990_, 0, v_config_3898_);
lean_closure_set(v___f_3990_, 1, v_machine_3975_);
lean_closure_set(v___f_3990_, 2, v_requestStream_3976_);
lean_closure_set(v___f_3990_, 3, v_response_3978_);
lean_closure_set(v___f_3990_, 4, v_respStream_3979_);
lean_closure_set(v___f_3990_, 5, v_inputWanted_3980_);
lean_closure_set(v___f_3990_, 6, v_handler_3981_);
lean_closure_set(v___f_3990_, 7, v_pendingHead_3982_);
lean_closure_set(v___f_3990_, 8, v_dateSecond_3983_);
lean_closure_set(v___f_3990_, 9, v___x_3989_);
lean_closure_set(v___f_3990_, 10, v___f_3985_);
v___x_3991_ = lean_unsigned_to_nat(0u);
v___x_3992_ = 0;
v___x_3999_ = lean_get_current_time();
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3999_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3999_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
lean_ctor_set_tag(v___x_4002_, 1);
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
v_val_3994_ = v___x_4005_;
goto v___jp_3993_;
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
v_a_4008_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3999_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3999_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
lean_ctor_set_tag(v___x_4010_, 0);
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
v_val_3994_ = v___x_4013_;
goto v___jp_3993_;
}
}
}
v___jp_3993_:
{
lean_object* v___x_3996_; 
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v_val_3994_);
v___x_3996_ = v___x_3987_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_val_3994_);
v___x_3996_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3997_; 
v___x_3997_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3991_, v___x_3992_, v___x_3996_, v___f_3990_);
return v___x_3997_;
}
}
}
}
else
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
lean_dec_ref(v___f_3985_);
lean_dec_ref(v_timer_3977_);
lean_dec_ref(v_config_3898_);
v___x_4018_ = lean_box(0);
v___x_4019_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3974_, v___x_4018_, v_state_3900_);
return v___x_4019_;
}
}
}
}
case 1:
{
lean_object* v_x_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4127_; 
lean_dec_ref(v_config_3898_);
lean_dec(v_handler_3897_);
lean_dec_ref(v_inst_3895_);
v_x_4021_ = lean_ctor_get(v_event_3899_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v_event_3899_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4023_ = v_event_3899_;
v_isShared_4024_ = v_isSharedCheck_4127_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_x_4021_);
lean_dec(v_event_3899_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4127_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
if (lean_obj_tag(v_x_4021_) == 0)
{
lean_object* v_machine_4025_; lean_object* v_requestStream_4026_; lean_object* v_timer_4027_; lean_object* v_response_4028_; lean_object* v_respStream_4029_; lean_object* v_inputWanted_4030_; lean_object* v_handler_4031_; lean_object* v_pendingHead_4032_; lean_object* v_dateSecond_4033_; uint8_t v_requestEnded_4034_; lean_object* v___x_4035_; lean_object* v___f_4036_; 
lean_del_object(v___x_4023_);
v_machine_4025_ = lean_ctor_get(v_state_3900_, 0);
lean_inc_ref_n(v_machine_4025_, 2);
v_requestStream_4026_ = lean_ctor_get(v_state_3900_, 1);
lean_inc_ref_n(v_requestStream_4026_, 2);
v_timer_4027_ = lean_ctor_get(v_state_3900_, 2);
lean_inc_ref_n(v_timer_4027_, 2);
v_response_4028_ = lean_ctor_get(v_state_3900_, 3);
lean_inc_ref_n(v_response_4028_, 2);
v_respStream_4029_ = lean_ctor_get(v_state_3900_, 4);
lean_inc(v_respStream_4029_);
v_inputWanted_4030_ = lean_ctor_get(v_state_3900_, 5);
lean_inc_n(v_inputWanted_4030_, 2);
v_handler_4031_ = lean_ctor_get(v_state_3900_, 6);
lean_inc_n(v_handler_4031_, 2);
v_pendingHead_4032_ = lean_ctor_get(v_state_3900_, 7);
lean_inc_n(v_pendingHead_4032_, 2);
v_dateSecond_4033_ = lean_ctor_get(v_state_3900_, 8);
lean_inc_n(v_dateSecond_4033_, 2);
v_requestEnded_4034_ = lean_ctor_get_uint8(v_state_3900_, sizeof(void*)*9);
lean_dec_ref(v_state_3900_);
v___x_4035_ = lean_box(v_requestEnded_4034_);
v___f_4036_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_4036_, 0, v_machine_4025_);
lean_closure_set(v___f_4036_, 1, v_requestStream_4026_);
lean_closure_set(v___f_4036_, 2, v_timer_4027_);
lean_closure_set(v___f_4036_, 3, v_response_4028_);
lean_closure_set(v___f_4036_, 4, v_inputWanted_4030_);
lean_closure_set(v___f_4036_, 5, v_handler_4031_);
lean_closure_set(v___f_4036_, 6, v_pendingHead_4032_);
lean_closure_set(v___f_4036_, 7, v_dateSecond_4033_);
lean_closure_set(v___f_4036_, 8, v___x_4035_);
if (lean_obj_tag(v_respStream_4029_) == 1)
{
lean_object* v_val_4037_; lean_object* v_close_4038_; lean_object* v_isClosed_4039_; lean_object* v___f_4040_; lean_object* v___f_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
lean_dec(v_dateSecond_4033_);
lean_dec(v_pendingHead_4032_);
lean_dec(v_handler_4031_);
lean_dec(v_inputWanted_4030_);
lean_dec_ref(v_response_4028_);
lean_dec_ref(v_timer_4027_);
lean_dec_ref(v_requestStream_4026_);
lean_dec_ref(v_machine_4025_);
v_val_4037_ = lean_ctor_get(v_respStream_4029_, 0);
lean_inc_n(v_val_4037_, 2);
lean_dec_ref_known(v_respStream_4029_, 1);
v_close_4038_ = lean_ctor_get(v_inst_3896_, 1);
lean_inc_ref(v_close_4038_);
v_isClosed_4039_ = lean_ctor_get(v_inst_3896_, 2);
lean_inc_ref(v_isClosed_4039_);
lean_dec_ref(v_inst_3896_);
lean_inc_ref(v___f_4036_);
v___f_4040_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4040_, 0, v___f_4036_);
v___f_4041_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_4041_, 0, v_close_4038_);
lean_closure_set(v___f_4041_, 1, v_val_4037_);
lean_closure_set(v___f_4041_, 2, v___f_4040_);
lean_closure_set(v___f_4041_, 3, v___f_4036_);
v___x_4042_ = lean_unsigned_to_nat(0u);
v___x_4043_ = 0;
v___x_4044_ = lean_apply_2(v_isClosed_4039_, v_val_4037_, lean_box(0));
v___x_4045_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4042_, v___x_4043_, v___x_4044_, v___f_4041_);
return v___x_4045_;
}
else
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
lean_dec_ref(v___f_4036_);
lean_dec(v_respStream_4029_);
lean_dec_ref(v_inst_3896_);
v___x_4046_ = lean_box(0);
v___x_4047_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_4025_, v_requestStream_4026_, v_timer_4027_, v_response_4028_, v_inputWanted_4030_, v_handler_4031_, v_pendingHead_4032_, v_dateSecond_4033_, v_requestEnded_4034_, v___x_4046_);
return v___x_4047_;
}
}
else
{
lean_object* v_val_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4126_; 
lean_dec_ref(v_inst_3896_);
v_val_4048_ = lean_ctor_get(v_x_4021_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v_x_4021_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4050_ = v_x_4021_;
v_isShared_4051_ = v_isSharedCheck_4126_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_val_4048_);
lean_dec(v_x_4021_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4126_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v_machine_4052_; lean_object* v_requestStream_4053_; lean_object* v_timer_4054_; lean_object* v_response_4055_; lean_object* v_respStream_4056_; lean_object* v_inputWanted_4057_; lean_object* v_handler_4058_; lean_object* v_pendingHead_4059_; lean_object* v_dateSecond_4060_; uint8_t v_requestEnded_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4125_; 
v_machine_4052_ = lean_ctor_get(v_state_3900_, 0);
v_requestStream_4053_ = lean_ctor_get(v_state_3900_, 1);
v_timer_4054_ = lean_ctor_get(v_state_3900_, 2);
v_response_4055_ = lean_ctor_get(v_state_3900_, 3);
v_respStream_4056_ = lean_ctor_get(v_state_3900_, 4);
v_inputWanted_4057_ = lean_ctor_get(v_state_3900_, 5);
v_handler_4058_ = lean_ctor_get(v_state_3900_, 6);
v_pendingHead_4059_ = lean_ctor_get(v_state_3900_, 7);
v_dateSecond_4060_ = lean_ctor_get(v_state_3900_, 8);
v_requestEnded_4061_ = lean_ctor_get_uint8(v_state_3900_, sizeof(void*)*9);
v_isSharedCheck_4125_ = !lean_is_exclusive(v_state_3900_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4063_ = v_state_3900_;
v_isShared_4064_ = v_isSharedCheck_4125_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_dateSecond_4060_);
lean_inc(v_pendingHead_4059_);
lean_inc(v_handler_4058_);
lean_inc(v_inputWanted_4057_);
lean_inc(v_respStream_4056_);
lean_inc(v_response_4055_);
lean_inc(v_timer_4054_);
lean_inc(v_requestStream_4053_);
lean_inc(v_machine_4052_);
lean_dec(v_state_3900_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4125_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___y_4066_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; uint8_t v___x_4084_; 
v___x_4079_ = lean_unsigned_to_nat(1u);
v___x_4080_ = lean_mk_empty_array_with_capacity(v___x_4079_);
v___x_4081_ = lean_array_push(v___x_4080_, v_val_4048_);
v___x_4082_ = lean_array_get_size(v___x_4081_);
v___x_4083_ = lean_unsigned_to_nat(0u);
v___x_4084_ = lean_nat_dec_eq(v___x_4082_, v___x_4083_);
if (v___x_4084_ == 0)
{
lean_object* v_reader_4085_; lean_object* v_writer_4086_; lean_object* v_config_4087_; lean_object* v_events_4088_; lean_object* v_error_4089_; lean_object* v_date_4090_; uint8_t v_keepAlive_4091_; uint8_t v_pullBodyStalled_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4124_; 
v_reader_4085_ = lean_ctor_get(v_machine_4052_, 0);
v_writer_4086_ = lean_ctor_get(v_machine_4052_, 1);
v_config_4087_ = lean_ctor_get(v_machine_4052_, 2);
v_events_4088_ = lean_ctor_get(v_machine_4052_, 3);
v_error_4089_ = lean_ctor_get(v_machine_4052_, 4);
v_date_4090_ = lean_ctor_get(v_machine_4052_, 5);
v_keepAlive_4091_ = lean_ctor_get_uint8(v_machine_4052_, sizeof(void*)*6);
v_pullBodyStalled_4092_ = lean_ctor_get_uint8(v_machine_4052_, sizeof(void*)*6 + 1);
v_isSharedCheck_4124_ = !lean_is_exclusive(v_machine_4052_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4094_ = v_machine_4052_;
v_isShared_4095_ = v_isSharedCheck_4124_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_date_4090_);
lean_inc(v_error_4089_);
lean_inc(v_events_4088_);
lean_inc(v_config_4087_);
lean_inc(v_writer_4086_);
lean_inc(v_reader_4085_);
lean_dec(v_machine_4052_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4124_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___y_4097_; lean_object* v___x_4118_; uint8_t v___x_4119_; 
v___x_4118_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_4119_ = lean_nat_dec_lt(v___x_4083_, v___x_4082_);
if (v___x_4119_ == 0)
{
v___y_4097_ = v___x_4083_;
goto v___jp_4096_;
}
else
{
lean_object* v___f_4120_; size_t v___x_4121_; size_t v___x_4122_; lean_object* v___x_4123_; 
v___f_4120_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_4121_ = ((size_t)0ULL);
v___x_4122_ = lean_usize_of_nat(v___x_4082_);
lean_inc_ref(v___x_4081_);
v___x_4123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4118_, v___f_4120_, v___x_4081_, v___x_4121_, v___x_4122_, v___x_4083_);
v___y_4097_ = v___x_4123_;
goto v___jp_4096_;
}
v___jp_4096_:
{
lean_object* v_userData_4098_; lean_object* v_outputData_4099_; lean_object* v_state_4100_; lean_object* v_knownSize_4101_; lean_object* v_messageHead_4102_; uint8_t v_userClosedBody_4103_; uint8_t v_omitBody_4104_; lean_object* v_userDataBytes_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4117_; 
v_userData_4098_ = lean_ctor_get(v_writer_4086_, 0);
v_outputData_4099_ = lean_ctor_get(v_writer_4086_, 1);
v_state_4100_ = lean_ctor_get(v_writer_4086_, 2);
v_knownSize_4101_ = lean_ctor_get(v_writer_4086_, 3);
v_messageHead_4102_ = lean_ctor_get(v_writer_4086_, 4);
v_userClosedBody_4103_ = lean_ctor_get_uint8(v_writer_4086_, sizeof(void*)*6);
v_omitBody_4104_ = lean_ctor_get_uint8(v_writer_4086_, sizeof(void*)*6 + 1);
v_userDataBytes_4105_ = lean_ctor_get(v_writer_4086_, 5);
v_isSharedCheck_4117_ = !lean_is_exclusive(v_writer_4086_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4107_ = v_writer_4086_;
v_isShared_4108_ = v_isSharedCheck_4117_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_userDataBytes_4105_);
lean_inc(v_messageHead_4102_);
lean_inc(v_knownSize_4101_);
lean_inc(v_state_4100_);
lean_inc(v_outputData_4099_);
lean_inc(v_userData_4098_);
lean_dec(v_writer_4086_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4117_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4112_; 
v___x_4109_ = l_Array_append___redArg(v_userData_4098_, v___x_4081_);
lean_dec_ref(v___x_4081_);
v___x_4110_ = lean_nat_add(v_userDataBytes_4105_, v___y_4097_);
lean_dec(v___y_4097_);
lean_dec(v_userDataBytes_4105_);
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 5, v___x_4110_);
lean_ctor_set(v___x_4107_, 0, v___x_4109_);
v___x_4112_ = v___x_4107_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4116_, 1, v_outputData_4099_);
lean_ctor_set(v_reuseFailAlloc_4116_, 2, v_state_4100_);
lean_ctor_set(v_reuseFailAlloc_4116_, 3, v_knownSize_4101_);
lean_ctor_set(v_reuseFailAlloc_4116_, 4, v_messageHead_4102_);
lean_ctor_set(v_reuseFailAlloc_4116_, 5, v___x_4110_);
lean_ctor_set_uint8(v_reuseFailAlloc_4116_, sizeof(void*)*6, v_userClosedBody_4103_);
lean_ctor_set_uint8(v_reuseFailAlloc_4116_, sizeof(void*)*6 + 1, v_omitBody_4104_);
v___x_4112_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
lean_object* v___x_4114_; 
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 1, v___x_4112_);
v___x_4114_ = v___x_4094_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_reader_4085_);
lean_ctor_set(v_reuseFailAlloc_4115_, 1, v___x_4112_);
lean_ctor_set(v_reuseFailAlloc_4115_, 2, v_config_4087_);
lean_ctor_set(v_reuseFailAlloc_4115_, 3, v_events_4088_);
lean_ctor_set(v_reuseFailAlloc_4115_, 4, v_error_4089_);
lean_ctor_set(v_reuseFailAlloc_4115_, 5, v_date_4090_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, sizeof(void*)*6, v_keepAlive_4091_);
lean_ctor_set_uint8(v_reuseFailAlloc_4115_, sizeof(void*)*6 + 1, v_pullBodyStalled_4092_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
v___y_4066_ = v___x_4114_;
goto v___jp_4065_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_4081_);
v___y_4066_ = v_machine_4052_;
goto v___jp_4065_;
}
v___jp_4065_:
{
lean_object* v___x_4068_; 
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v___y_4066_);
v___x_4068_ = v___x_4063_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___y_4066_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v_requestStream_4053_);
lean_ctor_set(v_reuseFailAlloc_4078_, 2, v_timer_4054_);
lean_ctor_set(v_reuseFailAlloc_4078_, 3, v_response_4055_);
lean_ctor_set(v_reuseFailAlloc_4078_, 4, v_respStream_4056_);
lean_ctor_set(v_reuseFailAlloc_4078_, 5, v_inputWanted_4057_);
lean_ctor_set(v_reuseFailAlloc_4078_, 6, v_handler_4058_);
lean_ctor_set(v_reuseFailAlloc_4078_, 7, v_pendingHead_4059_);
lean_ctor_set(v_reuseFailAlloc_4078_, 8, v_dateSecond_4060_);
lean_ctor_set_uint8(v_reuseFailAlloc_4078_, sizeof(void*)*9, v_requestEnded_4061_);
v___x_4068_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
uint8_t v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4073_; 
v___x_4069_ = 0;
v___x_4070_ = lean_box(v___x_4069_);
v___x_4071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4068_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v___x_4071_);
v___x_4073_ = v___x_4050_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4071_);
v___x_4073_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
lean_object* v___x_4075_; 
if (v_isShared_4024_ == 0)
{
lean_ctor_set_tag(v___x_4023_, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4073_);
v___x_4075_ = v___x_4023_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
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
uint8_t v_x_4128_; 
lean_dec_ref(v_config_3898_);
lean_dec_ref(v_inst_3896_);
v_x_4128_ = lean_ctor_get_uint8(v_event_3899_, 0);
lean_dec_ref_known(v_event_3899_, 0);
if (v_x_4128_ == 0)
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
lean_dec(v_handler_3897_);
lean_dec_ref(v_inst_3895_);
v___x_4129_ = lean_box(v_x_4128_);
v___x_4130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4130_, 0, v_state_3900_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
v___x_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4130_);
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
return v___x_4132_;
}
else
{
lean_object* v_machine_4133_; lean_object* v_requestStream_4134_; lean_object* v_timer_4135_; lean_object* v_response_4136_; lean_object* v_respStream_4137_; lean_object* v_inputWanted_4138_; lean_object* v_handler_4139_; lean_object* v_pendingHead_4140_; lean_object* v_dateSecond_4141_; uint8_t v_requestEnded_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4199_; 
v_machine_4133_ = lean_ctor_get(v_state_3900_, 0);
v_requestStream_4134_ = lean_ctor_get(v_state_3900_, 1);
v_timer_4135_ = lean_ctor_get(v_state_3900_, 2);
v_response_4136_ = lean_ctor_get(v_state_3900_, 3);
v_respStream_4137_ = lean_ctor_get(v_state_3900_, 4);
v_inputWanted_4138_ = lean_ctor_get(v_state_3900_, 5);
v_handler_4139_ = lean_ctor_get(v_state_3900_, 6);
v_pendingHead_4140_ = lean_ctor_get(v_state_3900_, 7);
v_dateSecond_4141_ = lean_ctor_get(v_state_3900_, 8);
v_requestEnded_4142_ = lean_ctor_get_uint8(v_state_3900_, sizeof(void*)*9);
v_isSharedCheck_4199_ = !lean_is_exclusive(v_state_3900_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4144_ = v_state_3900_;
v_isShared_4145_ = v_isSharedCheck_4199_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_dateSecond_4141_);
lean_inc(v_pendingHead_4140_);
lean_inc(v_handler_4139_);
lean_inc(v_inputWanted_4138_);
lean_inc(v_respStream_4137_);
lean_inc(v_response_4136_);
lean_inc(v_timer_4135_);
lean_inc(v_requestStream_4134_);
lean_inc(v_machine_4133_);
lean_dec(v_state_3900_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4199_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
uint8_t v___x_4146_; lean_object* v___x_4147_; lean_object* v_fst_4148_; lean_object* v_reader_4149_; lean_object* v_writer_4150_; lean_object* v_snd_4151_; lean_object* v_config_4152_; lean_object* v_events_4153_; lean_object* v_error_4154_; lean_object* v_date_4155_; uint8_t v_keepAlive_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4196_; 
v___x_4146_ = 0;
v___x_4147_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_4146_, v_machine_4133_);
v_fst_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_fst_4148_);
v_reader_4149_ = lean_ctor_get(v_fst_4148_, 0);
lean_inc_ref(v_reader_4149_);
v_writer_4150_ = lean_ctor_get(v_fst_4148_, 1);
lean_inc_ref(v_writer_4150_);
v_snd_4151_ = lean_ctor_get(v___x_4147_, 1);
lean_inc(v_snd_4151_);
lean_dec_ref(v___x_4147_);
v_config_4152_ = lean_ctor_get(v_fst_4148_, 2);
v_events_4153_ = lean_ctor_get(v_fst_4148_, 3);
v_error_4154_ = lean_ctor_get(v_fst_4148_, 4);
v_date_4155_ = lean_ctor_get(v_fst_4148_, 5);
v_keepAlive_4156_ = lean_ctor_get_uint8(v_fst_4148_, sizeof(void*)*6);
v_isSharedCheck_4196_ = !lean_is_exclusive(v_fst_4148_);
if (v_isSharedCheck_4196_ == 0)
{
lean_object* v_unused_4197_; lean_object* v_unused_4198_; 
v_unused_4197_ = lean_ctor_get(v_fst_4148_, 1);
lean_dec(v_unused_4197_);
v_unused_4198_ = lean_ctor_get(v_fst_4148_, 0);
lean_dec(v_unused_4198_);
v___x_4158_ = v_fst_4148_;
v_isShared_4159_ = v_isSharedCheck_4196_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_date_4155_);
lean_inc(v_error_4154_);
lean_inc(v_events_4153_);
lean_inc(v_config_4152_);
lean_dec(v_fst_4148_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4196_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v_state_4160_; lean_object* v_state_4161_; lean_object* v___f_4162_; uint8_t v___y_4164_; uint8_t v___y_4185_; 
v_state_4160_ = lean_ctor_get(v_reader_4149_, 0);
v_state_4161_ = lean_ctor_get(v_writer_4150_, 2);
v___f_4162_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_4162_, 0, v_inst_3895_);
lean_closure_set(v___f_4162_, 1, v_handler_3897_);
switch(lean_obj_tag(v_state_4161_))
{
case 6:
{
v___y_4185_ = v_x_4128_;
goto v___jp_4184_;
}
case 7:
{
v___y_4185_ = v_x_4128_;
goto v___jp_4184_;
}
default: 
{
switch(lean_obj_tag(v_state_4161_))
{
case 0:
{
uint8_t v___x_4188_; 
v___x_4188_ = 0;
v___y_4185_ = v___x_4188_;
goto v___jp_4184_;
}
case 1:
{
uint8_t v___x_4189_; 
v___x_4189_ = 0;
v___y_4185_ = v___x_4189_;
goto v___jp_4184_;
}
default: 
{
if (lean_obj_tag(v_state_4160_) == 2)
{
lean_object* v_a_4190_; 
v_a_4190_ = lean_ctor_get(v_state_4160_, 0);
if (lean_obj_tag(v_a_4190_) == 0)
{
lean_object* v_remaining_4191_; lean_object* v___x_4192_; uint8_t v___x_4193_; 
v_remaining_4191_ = lean_ctor_get(v_a_4190_, 0);
v___x_4192_ = lean_unsigned_to_nat(0u);
v___x_4193_ = lean_nat_dec_eq(v_remaining_4191_, v___x_4192_);
v___y_4185_ = v___x_4193_;
goto v___jp_4184_;
}
else
{
uint8_t v___x_4194_; 
v___x_4194_ = 0;
v___y_4185_ = v___x_4194_;
goto v___jp_4184_;
}
}
else
{
uint8_t v___x_4195_; 
v___x_4195_ = 0;
v___y_4185_ = v___x_4195_;
goto v___jp_4184_;
}
}
}
}
}
v___jp_4163_:
{
lean_object* v___x_4166_; 
if (v_isShared_4159_ == 0)
{
v___x_4166_ = v___x_4158_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_reader_4149_);
lean_ctor_set(v_reuseFailAlloc_4183_, 1, v_writer_4150_);
lean_ctor_set(v_reuseFailAlloc_4183_, 2, v_config_4152_);
lean_ctor_set(v_reuseFailAlloc_4183_, 3, v_events_4153_);
lean_ctor_set(v_reuseFailAlloc_4183_, 4, v_error_4154_);
lean_ctor_set(v_reuseFailAlloc_4183_, 5, v_date_4155_);
lean_ctor_set_uint8(v_reuseFailAlloc_4183_, sizeof(void*)*6, v_keepAlive_4156_);
v___x_4166_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
lean_object* v_st_4168_; 
lean_ctor_set_uint8(v___x_4166_, sizeof(void*)*6 + 1, v___y_4164_);
lean_inc_ref(v_requestStream_4134_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 0, v___x_4166_);
v_st_4168_ = v___x_4144_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4166_);
lean_ctor_set(v_reuseFailAlloc_4182_, 1, v_requestStream_4134_);
lean_ctor_set(v_reuseFailAlloc_4182_, 2, v_timer_4135_);
lean_ctor_set(v_reuseFailAlloc_4182_, 3, v_response_4136_);
lean_ctor_set(v_reuseFailAlloc_4182_, 4, v_respStream_4137_);
lean_ctor_set(v_reuseFailAlloc_4182_, 5, v_inputWanted_4138_);
lean_ctor_set(v_reuseFailAlloc_4182_, 6, v_handler_4139_);
lean_ctor_set(v_reuseFailAlloc_4182_, 7, v_pendingHead_4140_);
lean_ctor_set(v_reuseFailAlloc_4182_, 8, v_dateSecond_4141_);
lean_ctor_set_uint8(v_reuseFailAlloc_4182_, sizeof(void*)*9, v_requestEnded_4142_);
v_st_4168_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
lean_object* v___f_4169_; 
lean_inc_ref(v_st_4168_);
v___f_4169_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4169_, 0, v_st_4168_);
if (lean_obj_tag(v_snd_4151_) == 1)
{
lean_object* v_val_4170_; uint8_t v_final_4171_; uint8_t v_incomplete_4172_; lean_object* v_chunk_4173_; lean_object* v___f_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
lean_dec_ref(v_st_4168_);
v_val_4170_ = lean_ctor_get(v_snd_4151_, 0);
lean_inc(v_val_4170_);
lean_dec_ref_known(v_snd_4151_, 1);
v_final_4171_ = lean_ctor_get_uint8(v_val_4170_, sizeof(void*)*1);
v_incomplete_4172_ = lean_ctor_get_uint8(v_val_4170_, sizeof(void*)*1 + 1);
v_chunk_4173_ = lean_ctor_get(v_val_4170_, 0);
lean_inc_ref(v_chunk_4173_);
lean_dec(v_val_4170_);
v___f_4174_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4174_, 0, v___f_4169_);
v___x_4175_ = lean_unsigned_to_nat(0u);
v___x_4176_ = 0;
v___x_4177_ = l_Std_Http_Body_Stream_offer(v_requestStream_4134_, v_chunk_4173_, v_incomplete_4172_, v_final_4171_);
v___x_4178_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4175_, v___x_4176_, v___x_4177_, v___f_4162_);
v___x_4179_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4175_, v___x_4176_, v___x_4178_, v___f_4174_);
return v___x_4179_;
}
else
{
lean_object* v___x_4180_; lean_object* v___x_4181_; 
lean_dec_ref(v___f_4169_);
lean_dec_ref(v___f_4162_);
lean_dec(v_snd_4151_);
lean_dec_ref(v_requestStream_4134_);
v___x_4180_ = lean_box(0);
v___x_4181_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_4168_, v___x_4180_);
return v___x_4181_;
}
}
}
}
v___jp_4184_:
{
if (lean_obj_tag(v_snd_4151_) == 0)
{
if (v___y_4185_ == 0)
{
if (lean_obj_tag(v_state_4160_) == 2)
{
v___y_4164_ = v_x_4128_;
goto v___jp_4163_;
}
else
{
v___y_4164_ = v___y_4185_;
goto v___jp_4163_;
}
}
else
{
uint8_t v___x_4186_; 
v___x_4186_ = 0;
v___y_4164_ = v___x_4186_;
goto v___jp_4163_;
}
}
else
{
uint8_t v___x_4187_; 
v___x_4187_ = 0;
v___y_4164_ = v___x_4187_;
goto v___jp_4163_;
}
}
}
}
}
}
case 3:
{
lean_object* v_x_4200_; 
v_x_4200_ = lean_ctor_get(v_event_3899_, 0);
lean_inc_ref(v_x_4200_);
lean_dec_ref_known(v_event_3899_, 1);
if (lean_obj_tag(v_x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___f_4202_; lean_object* v___x_4203_; uint8_t v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
lean_dec_ref(v_config_3898_);
lean_dec_ref(v_inst_3896_);
v_a_4201_ = lean_ctor_get(v_x_4200_, 0);
lean_inc(v_a_4201_);
lean_dec_ref_known(v_x_4200_, 1);
v___f_4202_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_4202_, 0, v_state_3900_);
v___x_4203_ = lean_unsigned_to_nat(0u);
v___x_4204_ = 0;
v___x_4205_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_3895_, v_handler_3897_, v_a_4201_);
v___x_4206_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4203_, v___x_4204_, v___x_4205_, v___f_4202_);
return v___x_4206_;
}
else
{
lean_object* v_machine_4207_; lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4282_; 
v_machine_4207_ = lean_ctor_get(v_state_3900_, 0);
lean_inc_ref(v_machine_4207_);
v_a_4208_ = lean_ctor_get(v_x_4200_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v_x_4200_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4210_ = v_x_4200_;
v_isShared_4211_ = v_isSharedCheck_4282_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v_x_4200_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4282_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v_requestStream_4212_; lean_object* v_timer_4213_; lean_object* v_response_4214_; lean_object* v_respStream_4215_; lean_object* v_inputWanted_4216_; lean_object* v_pendingHead_4217_; lean_object* v_dateSecond_4218_; uint8_t v_requestEnded_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4279_; 
v_requestStream_4212_ = lean_ctor_get(v_state_3900_, 1);
v_timer_4213_ = lean_ctor_get(v_state_3900_, 2);
v_response_4214_ = lean_ctor_get(v_state_3900_, 3);
v_respStream_4215_ = lean_ctor_get(v_state_3900_, 4);
v_inputWanted_4216_ = lean_ctor_get(v_state_3900_, 5);
v_pendingHead_4217_ = lean_ctor_get(v_state_3900_, 7);
v_dateSecond_4218_ = lean_ctor_get(v_state_3900_, 8);
v_requestEnded_4219_ = lean_ctor_get_uint8(v_state_3900_, sizeof(void*)*9);
v_isSharedCheck_4279_ = !lean_is_exclusive(v_state_3900_);
if (v_isSharedCheck_4279_ == 0)
{
lean_object* v_unused_4280_; lean_object* v_unused_4281_; 
v_unused_4280_ = lean_ctor_get(v_state_3900_, 6);
lean_dec(v_unused_4280_);
v_unused_4281_ = lean_ctor_get(v_state_3900_, 0);
lean_dec(v_unused_4281_);
v___x_4221_ = v_state_3900_;
v_isShared_4222_ = v_isSharedCheck_4279_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_dateSecond_4218_);
lean_inc(v_pendingHead_4217_);
lean_inc(v_inputWanted_4216_);
lean_inc(v_respStream_4215_);
lean_inc(v_response_4214_);
lean_inc(v_timer_4213_);
lean_inc(v_requestStream_4212_);
lean_dec(v_state_3900_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4279_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v_error_4223_; lean_object* v___x_4224_; lean_object* v_state_4226_; 
v_error_4223_ = lean_ctor_get(v_machine_4207_, 4);
v___x_4224_ = lean_box(0);
lean_inc(v_dateSecond_4218_);
lean_inc(v_pendingHead_4217_);
lean_inc(v_inputWanted_4216_);
lean_inc(v_respStream_4215_);
lean_inc_ref(v_response_4214_);
lean_inc_ref(v_timer_4213_);
lean_inc_ref(v_requestStream_4212_);
lean_inc_ref(v_machine_4207_);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 6, v___x_4224_);
v_state_4226_ = v___x_4221_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_machine_4207_);
lean_ctor_set(v_reuseFailAlloc_4278_, 1, v_requestStream_4212_);
lean_ctor_set(v_reuseFailAlloc_4278_, 2, v_timer_4213_);
lean_ctor_set(v_reuseFailAlloc_4278_, 3, v_response_4214_);
lean_ctor_set(v_reuseFailAlloc_4278_, 4, v_respStream_4215_);
lean_ctor_set(v_reuseFailAlloc_4278_, 5, v_inputWanted_4216_);
lean_ctor_set(v_reuseFailAlloc_4278_, 6, v___x_4224_);
lean_ctor_set(v_reuseFailAlloc_4278_, 7, v_pendingHead_4217_);
lean_ctor_set(v_reuseFailAlloc_4278_, 8, v_dateSecond_4218_);
lean_ctor_set_uint8(v_reuseFailAlloc_4278_, sizeof(void*)*9, v_requestEnded_4219_);
v_state_4226_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
if (lean_obj_tag(v_error_4223_) == 0)
{
lean_object* v_line_4227_; lean_object* v_body_4228_; lean_object* v_status_4229_; uint8_t v___x_4230_; uint8_t v___y_4232_; uint16_t v___x_4248_; uint16_t v___x_4249_; uint8_t v___x_4250_; 
v_line_4227_ = lean_ctor_get(v_a_4208_, 0);
v_body_4228_ = lean_ctor_get(v_a_4208_, 1);
v_status_4229_ = lean_ctor_get(v_line_4227_, 0);
v___x_4230_ = 1;
v___x_4248_ = 100;
v___x_4249_ = l_Std_Http_Status_toCode(v_status_4229_);
v___x_4250_ = lean_uint16_dec_le(v___x_4248_, v___x_4249_);
if (v___x_4250_ == 0)
{
lean_dec(v_dateSecond_4218_);
lean_dec(v_pendingHead_4217_);
lean_dec(v_inputWanted_4216_);
lean_dec(v_respStream_4215_);
lean_dec_ref(v_response_4214_);
lean_dec_ref(v_timer_4213_);
lean_dec_ref(v_requestStream_4212_);
lean_dec_ref(v_machine_4207_);
v___y_4232_ = v___x_4250_;
goto v___jp_4231_;
}
else
{
uint16_t v___x_4251_; uint8_t v___x_4252_; 
v___x_4251_ = 200;
v___x_4252_ = lean_uint16_dec_lt(v___x_4249_, v___x_4251_);
if (v___x_4252_ == 0)
{
lean_dec(v_dateSecond_4218_);
lean_dec(v_pendingHead_4217_);
lean_dec(v_inputWanted_4216_);
lean_dec(v_respStream_4215_);
lean_dec_ref(v_response_4214_);
lean_dec_ref(v_timer_4213_);
lean_dec_ref(v_requestStream_4212_);
lean_dec_ref(v_machine_4207_);
v___y_4232_ = v___x_4252_;
goto v___jp_4231_;
}
else
{
lean_object* v_close_4253_; lean_object* v_isClosed_4254_; uint8_t v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___f_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___f_4261_; lean_object* v___f_4262_; lean_object* v___x_4263_; lean_object* v___f_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_inc_n(v_body_4228_, 2);
lean_dec_ref(v_state_4226_);
lean_del_object(v___x_4210_);
lean_dec(v_a_4208_);
lean_dec_ref(v_config_3898_);
v_close_4253_ = lean_ctor_get(v_inst_3896_, 1);
lean_inc_ref(v_close_4253_);
v_isClosed_4254_ = lean_ctor_get(v_inst_3896_, 2);
lean_inc_ref(v_isClosed_4254_);
lean_dec_ref(v_inst_3896_);
v___x_4255_ = 0;
v___x_4256_ = lean_box(v_requestEnded_4219_);
v___x_4257_ = lean_box(v___x_4255_);
v___f_4258_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed), 13, 11);
lean_closure_set(v___f_4258_, 0, v_machine_4207_);
lean_closure_set(v___f_4258_, 1, v_requestStream_4212_);
lean_closure_set(v___f_4258_, 2, v_timer_4213_);
lean_closure_set(v___f_4258_, 3, v_response_4214_);
lean_closure_set(v___f_4258_, 4, v_respStream_4215_);
lean_closure_set(v___f_4258_, 5, v_inputWanted_4216_);
lean_closure_set(v___f_4258_, 6, v___x_4224_);
lean_closure_set(v___f_4258_, 7, v_pendingHead_4217_);
lean_closure_set(v___f_4258_, 8, v_dateSecond_4218_);
lean_closure_set(v___f_4258_, 9, v___x_4256_);
lean_closure_set(v___f_4258_, 10, v___x_4257_);
v___x_4259_ = lean_box(v___x_4249_);
v___x_4260_ = lean_box(v___x_4255_);
v___f_4261_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 7, 5);
lean_closure_set(v___f_4261_, 0, v___x_4259_);
lean_closure_set(v___f_4261_, 1, v_inst_3895_);
lean_closure_set(v___f_4261_, 2, v_handler_3897_);
lean_closure_set(v___f_4261_, 3, v___x_4260_);
lean_closure_set(v___f_4261_, 4, v___f_4258_);
lean_inc_ref(v___f_4261_);
v___f_4262_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4262_, 0, v___f_4261_);
v___x_4263_ = lean_box(v___x_4255_);
v___f_4264_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 7, 5);
lean_closure_set(v___f_4264_, 0, v_close_4253_);
lean_closure_set(v___f_4264_, 1, v_body_4228_);
lean_closure_set(v___f_4264_, 2, v___x_4263_);
lean_closure_set(v___f_4264_, 3, v___f_4262_);
lean_closure_set(v___f_4264_, 4, v___f_4261_);
v___x_4265_ = lean_unsigned_to_nat(0u);
v___x_4266_ = lean_apply_2(v_isClosed_4254_, v_body_4228_, lean_box(0));
v___x_4267_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4265_, v___x_4255_, v___x_4266_, v___f_4264_);
return v___x_4267_;
}
}
v___jp_4231_:
{
lean_object* v___x_4233_; lean_object* v___f_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___f_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v___x_4233_ = lean_box(v___y_4232_);
v___f_4234_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_4234_, 0, v___x_4233_);
v___x_4235_ = lean_box(v___y_4232_);
v___x_4236_ = lean_box(v___x_4230_);
v___f_4237_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 9, 7);
lean_closure_set(v___f_4237_, 0, v___x_4235_);
lean_closure_set(v___f_4237_, 1, v___x_4236_);
lean_closure_set(v___f_4237_, 2, v_inst_3895_);
lean_closure_set(v___f_4237_, 3, v_handler_3897_);
lean_closure_set(v___f_4237_, 4, v_inst_3896_);
lean_closure_set(v___f_4237_, 5, v___f_4234_);
lean_closure_set(v___f_4237_, 6, v_a_4208_);
v___x_4238_ = lean_unsigned_to_nat(0u);
v___x_4239_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(v_config_3898_, v_state_4226_);
lean_dec_ref(v_config_3898_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v_a_4240_; lean_object* v___x_4242_; 
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_a_4240_);
lean_dec_ref_known(v___x_4239_, 1);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 0, v_a_4240_);
v___x_4242_ = v___x_4210_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4240_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
v___y_3903_ = v___f_4237_;
v___y_3904_ = v___x_4238_;
v___y_3905_ = v___y_4232_;
v_val_3906_ = v___x_4242_;
goto v___jp_3902_;
}
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; 
v_a_4244_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_a_4244_);
lean_dec_ref_known(v___x_4239_, 1);
if (v_isShared_4211_ == 0)
{
lean_ctor_set_tag(v___x_4210_, 0);
lean_ctor_set(v___x_4210_, 0, v_a_4244_);
v___x_4246_ = v___x_4210_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4244_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
v___y_3903_ = v___f_4237_;
v___y_3904_ = v___x_4238_;
v___y_3905_ = v___y_4232_;
v_val_3906_ = v___x_4246_;
goto v___jp_3902_;
}
}
}
}
else
{
lean_object* v_close_4268_; lean_object* v_isClosed_4269_; lean_object* v_body_4270_; lean_object* v___f_4271_; lean_object* v___f_4272_; lean_object* v___f_4273_; lean_object* v___x_4274_; uint8_t v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
lean_dec(v_dateSecond_4218_);
lean_dec(v_pendingHead_4217_);
lean_dec(v_inputWanted_4216_);
lean_dec(v_respStream_4215_);
lean_dec_ref(v_response_4214_);
lean_dec_ref(v_timer_4213_);
lean_dec_ref(v_requestStream_4212_);
lean_del_object(v___x_4210_);
lean_dec_ref(v_machine_4207_);
lean_dec_ref(v_config_3898_);
lean_dec(v_handler_3897_);
lean_dec_ref(v_inst_3895_);
v_close_4268_ = lean_ctor_get(v_inst_3896_, 1);
lean_inc_ref(v_close_4268_);
v_isClosed_4269_ = lean_ctor_get(v_inst_3896_, 2);
lean_inc_ref(v_isClosed_4269_);
lean_dec_ref(v_inst_3896_);
v_body_4270_ = lean_ctor_get(v_a_4208_, 1);
lean_inc_n(v_body_4270_, 2);
lean_dec(v_a_4208_);
v___f_4271_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 3, 1);
lean_closure_set(v___f_4271_, 0, v_state_4226_);
lean_inc_ref(v___f_4271_);
v___f_4272_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4272_, 0, v___f_4271_);
v___f_4273_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20___boxed), 6, 4);
lean_closure_set(v___f_4273_, 0, v_close_4268_);
lean_closure_set(v___f_4273_, 1, v_body_4270_);
lean_closure_set(v___f_4273_, 2, v___f_4272_);
lean_closure_set(v___f_4273_, 3, v___f_4271_);
v___x_4274_ = lean_unsigned_to_nat(0u);
v___x_4275_ = 0;
v___x_4276_ = lean_apply_2(v_isClosed_4269_, v_body_4270_, lean_box(0));
v___x_4277_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4274_, v___x_4275_, v___x_4276_, v___f_4273_);
return v___x_4277_;
}
}
}
}
}
}
case 4:
{
lean_object* v___f_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; uint8_t v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
lean_dec_ref(v_config_3898_);
lean_dec_ref(v_inst_3896_);
v___f_4283_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19___boxed), 3, 1);
lean_closure_set(v___f_4283_, 0, v_state_3900_);
v___x_4284_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1);
v___x_4285_ = lean_unsigned_to_nat(0u);
v___x_4286_ = 0;
v___x_4287_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_3895_, v_handler_3897_, v___x_4284_);
v___x_4288_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4285_, v___x_4286_, v___x_4287_, v___f_4283_);
return v___x_4288_;
}
case 6:
{
lean_object* v_machine_4289_; lean_object* v_requestStream_4290_; lean_object* v_timer_4291_; lean_object* v_response_4292_; lean_object* v_respStream_4293_; lean_object* v_inputWanted_4294_; lean_object* v_handler_4295_; lean_object* v_pendingHead_4296_; lean_object* v_dateSecond_4297_; uint8_t v_requestEnded_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4313_; 
lean_dec_ref(v_config_3898_);
lean_dec(v_handler_3897_);
lean_dec_ref(v_inst_3896_);
lean_dec_ref(v_inst_3895_);
v_machine_4289_ = lean_ctor_get(v_state_3900_, 0);
v_requestStream_4290_ = lean_ctor_get(v_state_3900_, 1);
v_timer_4291_ = lean_ctor_get(v_state_3900_, 2);
v_response_4292_ = lean_ctor_get(v_state_3900_, 3);
v_respStream_4293_ = lean_ctor_get(v_state_3900_, 4);
v_inputWanted_4294_ = lean_ctor_get(v_state_3900_, 5);
v_handler_4295_ = lean_ctor_get(v_state_3900_, 6);
v_pendingHead_4296_ = lean_ctor_get(v_state_3900_, 7);
v_dateSecond_4297_ = lean_ctor_get(v_state_3900_, 8);
v_requestEnded_4298_ = lean_ctor_get_uint8(v_state_3900_, sizeof(void*)*9);
v_isSharedCheck_4313_ = !lean_is_exclusive(v_state_3900_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4300_ = v_state_3900_;
v_isShared_4301_ = v_isSharedCheck_4313_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_dateSecond_4297_);
lean_inc(v_pendingHead_4296_);
lean_inc(v_handler_4295_);
lean_inc(v_inputWanted_4294_);
lean_inc(v_respStream_4293_);
lean_inc(v_response_4292_);
lean_inc(v_timer_4291_);
lean_inc(v_requestStream_4290_);
lean_inc(v_machine_4289_);
lean_dec(v_state_3900_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4313_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4306_; 
v___x_4302_ = lean_box(55);
v___x_4303_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_4289_, v___x_4302_);
v___x_4304_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon___redArg(v_handler_4295_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 6, v___x_4304_);
lean_ctor_set(v___x_4300_, 0, v___x_4303_);
v___x_4306_ = v___x_4300_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4303_);
lean_ctor_set(v_reuseFailAlloc_4312_, 1, v_requestStream_4290_);
lean_ctor_set(v_reuseFailAlloc_4312_, 2, v_timer_4291_);
lean_ctor_set(v_reuseFailAlloc_4312_, 3, v_response_4292_);
lean_ctor_set(v_reuseFailAlloc_4312_, 4, v_respStream_4293_);
lean_ctor_set(v_reuseFailAlloc_4312_, 5, v_inputWanted_4294_);
lean_ctor_set(v_reuseFailAlloc_4312_, 6, v___x_4304_);
lean_ctor_set(v_reuseFailAlloc_4312_, 7, v_pendingHead_4296_);
lean_ctor_set(v_reuseFailAlloc_4312_, 8, v_dateSecond_4297_);
lean_ctor_set_uint8(v_reuseFailAlloc_4312_, sizeof(void*)*9, v_requestEnded_4298_);
v___x_4306_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
uint8_t v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4307_ = 0;
v___x_4308_ = lean_box(v___x_4307_);
v___x_4309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4306_);
lean_ctor_set(v___x_4309_, 1, v___x_4308_);
v___x_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4309_);
v___x_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4310_);
return v___x_4311_;
}
}
}
default: 
{
lean_dec(v_event_3899_);
lean_dec_ref(v_config_3898_);
lean_dec(v_handler_3897_);
lean_dec_ref(v_inst_3896_);
lean_dec_ref(v_inst_3895_);
goto v___jp_3909_;
}
}
v___jp_3902_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3907_, 0, v_val_3906_);
v___x_3908_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_3904_, v___y_3905_, v___x_3907_, v___y_3903_);
return v___x_3908_;
}
v___jp_3909_:
{
uint8_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3910_ = 1;
v___x_3911_ = lean_box(v___x_3910_);
v___x_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3912_, 0, v_state_3900_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
v___x_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
return v___x_3914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_4314_, lean_object* v_inst_4315_, lean_object* v_handler_4316_, lean_object* v_config_4317_, lean_object* v_event_4318_, lean_object* v_state_4319_, lean_object* v_a_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_4314_, v_inst_4315_, v_handler_4316_, v_config_4317_, v_event_4318_, v_state_4319_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_4322_, lean_object* v_00_u03b2_4323_, lean_object* v_inst_4324_, lean_object* v_inst_4325_, lean_object* v_handler_4326_, lean_object* v_config_4327_, lean_object* v_event_4328_, lean_object* v_state_4329_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_4324_, v_inst_4325_, v_handler_4326_, v_config_4327_, v_event_4328_, v_state_4329_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_4332_, lean_object* v_00_u03b2_4333_, lean_object* v_inst_4334_, lean_object* v_inst_4335_, lean_object* v_handler_4336_, lean_object* v_config_4337_, lean_object* v_event_4338_, lean_object* v_state_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_4332_, v_00_u03b2_4333_, v_inst_4334_, v_inst_4335_, v_handler_4336_, v_config_4337_, v_event_4338_, v_state_4339_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_respStream_4342_, lean_object* v_connectionContext_4343_, lean_object* v_handler_4344_, lean_object* v_response_4345_, lean_object* v_inputWanted_4346_, lean_object* v_timer_4347_, lean_object* v_socket_4348_, lean_object* v_reader_4349_, lean_object* v_inputLimit_4350_, uint8_t v_pullBodyStalled_4351_, uint8_t v_requestBodyOpen_4352_, lean_object* v_state_4353_, uint8_t v_requestBodyInterested_4354_, lean_object* v_requestBody_4355_){
_start:
{
lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; uint8_t v___x_4365_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4373_; lean_object* v___y_4374_; uint8_t v___y_4378_; lean_object* v___y_4379_; uint8_t v___y_4383_; uint8_t v___y_4388_; uint8_t v___y_4391_; uint8_t v___y_4403_; uint8_t v___y_4405_; uint8_t v___y_4407_; uint8_t v___y_4408_; uint8_t v___y_4411_; uint8_t v___y_4418_; uint8_t v___y_4420_; uint8_t v___y_4421_; uint8_t v___y_4423_; uint8_t v___y_4424_; uint8_t v___y_4427_; 
v___x_4365_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg(v_handler_4344_);
if (v___x_4365_ == 0)
{
uint8_t v___x_4433_; 
v___x_4433_ = 1;
v___y_4391_ = v___x_4433_;
goto v___jp_4390_;
}
else
{
if (lean_obj_tag(v_respStream_4342_) == 0)
{
uint8_t v___x_4434_; 
v___x_4434_ = 0;
switch(lean_obj_tag(v_state_4353_))
{
case 0:
{
v___y_4427_ = v___x_4434_;
goto v___jp_4426_;
}
case 1:
{
v___y_4427_ = v___x_4434_;
goto v___jp_4426_;
}
default: 
{
v___y_4391_ = v___x_4365_;
goto v___jp_4390_;
}
}
}
else
{
v___y_4391_ = v___x_4365_;
goto v___jp_4390_;
}
}
v___jp_4357_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4362_, 0, v___y_4360_);
lean_ctor_set(v___x_4362_, 1, v___y_4359_);
lean_ctor_set(v___x_4362_, 2, v___y_4358_);
lean_ctor_set(v___x_4362_, 3, v___y_4361_);
lean_ctor_set(v___x_4362_, 4, v_respStream_4342_);
lean_ctor_set(v___x_4362_, 5, v_requestBody_4355_);
lean_ctor_set(v___x_4362_, 6, v_connectionContext_4343_);
v___x_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
v___x_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4363_);
return v___x_4364_;
}
v___jp_4366_:
{
if (v___x_4365_ == 0)
{
lean_object* v___x_4370_; 
lean_dec_ref(v_response_4345_);
v___x_4370_ = lean_box(0);
v___y_4358_ = v___y_4369_;
v___y_4359_ = v___y_4367_;
v___y_4360_ = v___y_4368_;
v___y_4361_ = v___x_4370_;
goto v___jp_4357_;
}
else
{
lean_object* v___x_4371_; 
v___x_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4371_, 0, v_response_4345_);
v___y_4358_ = v___y_4369_;
v___y_4359_ = v___y_4367_;
v___y_4360_ = v___y_4368_;
v___y_4361_ = v___x_4371_;
goto v___jp_4357_;
}
}
v___jp_4372_:
{
if (lean_obj_tag(v_inputWanted_4346_) == 0)
{
lean_object* v___x_4375_; 
v___x_4375_ = lean_box(0);
v___y_4367_ = v___y_4374_;
v___y_4368_ = v___y_4373_;
v___y_4369_ = v___x_4375_;
goto v___jp_4366_;
}
else
{
lean_object* v_val_4376_; 
v_val_4376_ = lean_ctor_get(v_inputWanted_4346_, 0);
lean_inc(v_val_4376_);
lean_dec_ref_known(v_inputWanted_4346_, 1);
v___y_4367_ = v___y_4374_;
v___y_4368_ = v___y_4373_;
v___y_4369_ = v_val_4376_;
goto v___jp_4366_;
}
}
v___jp_4377_:
{
if (v___y_4378_ == 0)
{
lean_object* v___x_4380_; 
lean_dec_ref(v_timer_4347_);
v___x_4380_ = lean_box(0);
v___y_4373_ = v___y_4379_;
v___y_4374_ = v___x_4380_;
goto v___jp_4372_;
}
else
{
lean_object* v___x_4381_; 
v___x_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4381_, 0, v_timer_4347_);
v___y_4373_ = v___y_4379_;
v___y_4374_ = v___x_4381_;
goto v___jp_4372_;
}
}
v___jp_4382_:
{
lean_object* v___x_4384_; 
v___x_4384_ = lean_box(0);
v___y_4378_ = v___y_4383_;
v___y_4379_ = v___x_4384_;
goto v___jp_4377_;
}
v___jp_4385_:
{
uint8_t v___x_4386_; 
v___x_4386_ = 0;
v___y_4383_ = v___x_4386_;
goto v___jp_4382_;
}
v___jp_4387_:
{
lean_object* v___x_4389_; 
v___x_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4389_, 0, v_socket_4348_);
v___y_4378_ = v___y_4388_;
v___y_4379_ = v___x_4389_;
goto v___jp_4377_;
}
v___jp_4390_:
{
uint8_t v_peerClosed_4392_; 
v_peerClosed_4392_ = lean_ctor_get_uint8(v_reader_4349_, sizeof(void*)*6);
if (v_peerClosed_4392_ == 0)
{
uint8_t v_inputStopped_4393_; 
v_inputStopped_4393_ = lean_ctor_get_uint8(v_reader_4349_, sizeof(void*)*6 + 1);
if (v_inputStopped_4393_ == 0)
{
lean_object* v_input_4394_; lean_object* v_array_4395_; lean_object* v_idx_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; uint8_t v___x_4399_; 
v_input_4394_ = lean_ctor_get(v_reader_4349_, 1);
v_array_4395_ = lean_ctor_get(v_input_4394_, 0);
v_idx_4396_ = lean_ctor_get(v_input_4394_, 1);
v___x_4397_ = lean_byte_array_size(v_array_4395_);
v___x_4398_ = lean_nat_sub(v___x_4397_, v_idx_4396_);
v___x_4399_ = lean_nat_dec_le(v_inputLimit_4350_, v___x_4398_);
lean_dec(v___x_4398_);
if (v___x_4399_ == 0)
{
v___y_4388_ = v___y_4391_;
goto v___jp_4387_;
}
else
{
if (lean_obj_tag(v_inputWanted_4346_) == 0)
{
lean_dec(v_socket_4348_);
v___y_4383_ = v___y_4391_;
goto v___jp_4382_;
}
else
{
v___y_4388_ = v___y_4391_;
goto v___jp_4387_;
}
}
}
else
{
lean_dec(v_socket_4348_);
v___y_4383_ = v___y_4391_;
goto v___jp_4382_;
}
}
else
{
lean_dec(v_socket_4348_);
v___y_4383_ = v___y_4391_;
goto v___jp_4382_;
}
}
v___jp_4400_:
{
uint8_t v___x_4401_; 
v___x_4401_ = 1;
v___y_4391_ = v___x_4401_;
goto v___jp_4390_;
}
v___jp_4402_:
{
goto v___jp_4400_;
}
v___jp_4404_:
{
if (v_pullBodyStalled_4351_ == 0)
{
lean_dec(v_socket_4348_);
goto v___jp_4385_;
}
else
{
v___y_4403_ = v___y_4405_;
goto v___jp_4402_;
}
}
v___jp_4406_:
{
lean_object* v_state_4409_; 
v_state_4409_ = lean_ctor_get(v_reader_4349_, 0);
if (lean_obj_tag(v_state_4409_) == 2)
{
v___y_4405_ = v___y_4407_;
goto v___jp_4404_;
}
else
{
if (v___y_4408_ == 0)
{
goto v___jp_4400_;
}
else
{
v___y_4405_ = v___y_4407_;
goto v___jp_4404_;
}
}
}
v___jp_4410_:
{
if (v_requestBodyOpen_4352_ == 0)
{
lean_dec(v_socket_4348_);
v___y_4383_ = v_requestBodyOpen_4352_;
goto v___jp_4382_;
}
else
{
switch(lean_obj_tag(v_state_4353_))
{
case 6:
{
v___y_4403_ = v___y_4411_;
goto v___jp_4402_;
}
case 7:
{
v___y_4403_ = v___y_4411_;
goto v___jp_4402_;
}
default: 
{
switch(lean_obj_tag(v_state_4353_))
{
case 0:
{
v___y_4407_ = v___y_4411_;
v___y_4408_ = v___y_4411_;
goto v___jp_4406_;
}
case 1:
{
v___y_4407_ = v___y_4411_;
v___y_4408_ = v___y_4411_;
goto v___jp_4406_;
}
default: 
{
lean_object* v_state_4412_; 
v_state_4412_ = lean_ctor_get(v_reader_4349_, 0);
if (lean_obj_tag(v_state_4412_) == 2)
{
lean_object* v_a_4413_; 
v_a_4413_ = lean_ctor_get(v_state_4412_, 0);
if (lean_obj_tag(v_a_4413_) == 0)
{
lean_object* v_remaining_4414_; lean_object* v___x_4415_; uint8_t v___x_4416_; 
v_remaining_4414_ = lean_ctor_get(v_a_4413_, 0);
v___x_4415_ = lean_unsigned_to_nat(0u);
v___x_4416_ = lean_nat_dec_eq(v_remaining_4414_, v___x_4415_);
if (v___x_4416_ == 0)
{
v___y_4407_ = v___y_4411_;
v___y_4408_ = v___x_4416_;
goto v___jp_4406_;
}
else
{
v___y_4403_ = v___y_4411_;
goto v___jp_4402_;
}
}
else
{
v___y_4407_ = v___y_4411_;
v___y_4408_ = v___y_4411_;
goto v___jp_4406_;
}
}
else
{
v___y_4407_ = v___y_4411_;
v___y_4408_ = v___y_4411_;
goto v___jp_4406_;
}
}
}
}
}
}
}
v___jp_4417_:
{
if (v_requestBodyInterested_4354_ == 0)
{
v___y_4411_ = v___y_4418_;
goto v___jp_4410_;
}
else
{
v___y_4391_ = v_requestBodyInterested_4354_;
goto v___jp_4390_;
}
}
v___jp_4419_:
{
if (v___y_4421_ == 0)
{
v___y_4411_ = v___y_4420_;
goto v___jp_4410_;
}
else
{
v___y_4418_ = v___y_4420_;
goto v___jp_4417_;
}
}
v___jp_4422_:
{
lean_object* v_state_4425_; 
v_state_4425_ = lean_ctor_get(v_reader_4349_, 0);
if (lean_obj_tag(v_state_4425_) == 2)
{
v___y_4418_ = v___y_4423_;
goto v___jp_4417_;
}
else
{
v___y_4420_ = v___y_4423_;
v___y_4421_ = v___y_4424_;
goto v___jp_4419_;
}
}
v___jp_4426_:
{
switch(lean_obj_tag(v_state_4353_))
{
case 6:
{
v___y_4420_ = v___y_4427_;
v___y_4421_ = v___y_4427_;
goto v___jp_4419_;
}
case 7:
{
v___y_4420_ = v___y_4427_;
v___y_4421_ = v___y_4427_;
goto v___jp_4419_;
}
default: 
{
switch(lean_obj_tag(v_state_4353_))
{
case 0:
{
v___y_4423_ = v___y_4427_;
v___y_4424_ = v___y_4427_;
goto v___jp_4422_;
}
case 1:
{
v___y_4423_ = v___y_4427_;
v___y_4424_ = v___y_4427_;
goto v___jp_4422_;
}
default: 
{
lean_object* v_state_4428_; 
v_state_4428_ = lean_ctor_get(v_reader_4349_, 0);
if (lean_obj_tag(v_state_4428_) == 2)
{
lean_object* v_a_4429_; 
v_a_4429_ = lean_ctor_get(v_state_4428_, 0);
if (lean_obj_tag(v_a_4429_) == 0)
{
lean_object* v_remaining_4430_; lean_object* v___x_4431_; uint8_t v___x_4432_; 
v_remaining_4430_ = lean_ctor_get(v_a_4429_, 0);
v___x_4431_ = lean_unsigned_to_nat(0u);
v___x_4432_ = lean_nat_dec_eq(v_remaining_4430_, v___x_4431_);
if (v___x_4432_ == 0)
{
v___y_4423_ = v___y_4427_;
v___y_4424_ = v___x_4432_;
goto v___jp_4422_;
}
else
{
v___y_4420_ = v___y_4427_;
v___y_4421_ = v___y_4427_;
goto v___jp_4419_;
}
}
else
{
v___y_4423_ = v___y_4427_;
v___y_4424_ = v___y_4427_;
goto v___jp_4422_;
}
}
else
{
v___y_4423_ = v___y_4427_;
v___y_4424_ = v___y_4427_;
goto v___jp_4422_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_respStream_4435_, lean_object* v_connectionContext_4436_, lean_object* v_handler_4437_, lean_object* v_response_4438_, lean_object* v_inputWanted_4439_, lean_object* v_timer_4440_, lean_object* v_socket_4441_, lean_object* v_reader_4442_, lean_object* v_inputLimit_4443_, lean_object* v_pullBodyStalled_4444_, lean_object* v_requestBodyOpen_4445_, lean_object* v_state_4446_, lean_object* v_requestBodyInterested_4447_, lean_object* v_requestBody_4448_, lean_object* v___y_4449_){
_start:
{
uint8_t v_pullBodyStalled_boxed_4450_; uint8_t v_requestBodyOpen_boxed_4451_; uint8_t v_requestBodyInterested_boxed_4452_; lean_object* v_res_4453_; 
v_pullBodyStalled_boxed_4450_ = lean_unbox(v_pullBodyStalled_4444_);
v_requestBodyOpen_boxed_4451_ = lean_unbox(v_requestBodyOpen_4445_);
v_requestBodyInterested_boxed_4452_ = lean_unbox(v_requestBodyInterested_4447_);
v_res_4453_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_respStream_4435_, v_connectionContext_4436_, v_handler_4437_, v_response_4438_, v_inputWanted_4439_, v_timer_4440_, v_socket_4441_, v_reader_4442_, v_inputLimit_4443_, v_pullBodyStalled_boxed_4450_, v_requestBodyOpen_boxed_4451_, v_state_4446_, v_requestBodyInterested_boxed_4452_, v_requestBody_4448_);
lean_dec(v_state_4446_);
lean_dec(v_inputLimit_4443_);
lean_dec_ref(v_reader_4442_);
lean_dec(v_handler_4437_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_4454_, lean_object* v_x_4455_){
_start:
{
if (lean_obj_tag(v_x_4455_) == 0)
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4465_; 
lean_dec_ref(v___f_4454_);
v_a_4457_ = lean_ctor_get(v_x_4455_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v_x_4455_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4459_ = v_x_4455_;
v_isShared_4460_ = v_isSharedCheck_4465_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v_x_4455_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4465_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
lean_object* v___x_4463_; 
v___x_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4462_);
return v___x_4463_;
}
}
}
else
{
lean_object* v_a_4466_; lean_object* v___x_4467_; 
v_a_4466_ = lean_ctor_get(v_x_4455_, 0);
lean_inc(v_a_4466_);
lean_dec_ref_known(v_x_4455_, 1);
v___x_4467_ = lean_apply_2(v___f_4454_, v_a_4466_, lean_box(0));
return v___x_4467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_4468_, lean_object* v_x_4469_, lean_object* v___y_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_4468_, v_x_4469_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_respStream_4476_, lean_object* v_connectionContext_4477_, lean_object* v_handler_4478_, lean_object* v_response_4479_, lean_object* v_inputWanted_4480_, lean_object* v_timer_4481_, lean_object* v_socket_4482_, lean_object* v_reader_4483_, lean_object* v_inputLimit_4484_, uint8_t v_pullBodyStalled_4485_, uint8_t v_requestBodyOpen_4486_, lean_object* v_state_4487_, lean_object* v_requestStream_4488_, uint8_t v_requestBodyInterested_4489_){
_start:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___f_4494_; lean_object* v___f_4495_; uint8_t v___y_4497_; 
v___x_4491_ = lean_box(v_pullBodyStalled_4485_);
v___x_4492_ = lean_box(v_requestBodyOpen_4486_);
v___x_4493_ = lean_box(v_requestBodyInterested_4489_);
lean_inc(v_state_4487_);
lean_inc_ref(v_reader_4483_);
v___f_4494_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_4494_, 0, v_respStream_4476_);
lean_closure_set(v___f_4494_, 1, v_connectionContext_4477_);
lean_closure_set(v___f_4494_, 2, v_handler_4478_);
lean_closure_set(v___f_4494_, 3, v_response_4479_);
lean_closure_set(v___f_4494_, 4, v_inputWanted_4480_);
lean_closure_set(v___f_4494_, 5, v_timer_4481_);
lean_closure_set(v___f_4494_, 6, v_socket_4482_);
lean_closure_set(v___f_4494_, 7, v_reader_4483_);
lean_closure_set(v___f_4494_, 8, v_inputLimit_4484_);
lean_closure_set(v___f_4494_, 9, v___x_4491_);
lean_closure_set(v___f_4494_, 10, v___x_4492_);
lean_closure_set(v___f_4494_, 11, v_state_4487_);
lean_closure_set(v___f_4494_, 12, v___x_4493_);
v___f_4495_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4495_, 0, v___f_4494_);
switch(lean_obj_tag(v_state_4487_))
{
case 6:
{
uint8_t v___x_4501_; 
lean_dec_ref(v_requestStream_4488_);
lean_dec_ref(v_reader_4483_);
v___x_4501_ = 0;
v___y_4497_ = v___x_4501_;
goto v___jp_4496_;
}
case 7:
{
uint8_t v___x_4502_; 
lean_dec_ref(v_requestStream_4488_);
lean_dec_ref(v_reader_4483_);
v___x_4502_ = 0;
v___y_4497_ = v___x_4502_;
goto v___jp_4496_;
}
default: 
{
uint8_t v___y_4511_; 
switch(lean_obj_tag(v_state_4487_))
{
case 0:
{
uint8_t v___x_4513_; 
v___x_4513_ = 0;
v___y_4511_ = v___x_4513_;
goto v___jp_4510_;
}
case 1:
{
uint8_t v___x_4514_; 
v___x_4514_ = 0;
v___y_4511_ = v___x_4514_;
goto v___jp_4510_;
}
default: 
{
lean_object* v_state_4515_; 
lean_dec(v_state_4487_);
v_state_4515_ = lean_ctor_get(v_reader_4483_, 0);
if (lean_obj_tag(v_state_4515_) == 2)
{
lean_object* v_a_4516_; 
v_a_4516_ = lean_ctor_get(v_state_4515_, 0);
if (lean_obj_tag(v_a_4516_) == 0)
{
lean_object* v_remaining_4517_; lean_object* v___x_4518_; uint8_t v___x_4519_; 
v_remaining_4517_ = lean_ctor_get(v_a_4516_, 0);
v___x_4518_ = lean_unsigned_to_nat(0u);
v___x_4519_ = lean_nat_dec_eq(v_remaining_4517_, v___x_4518_);
if (v___x_4519_ == 0)
{
v___y_4511_ = v___x_4519_;
goto v___jp_4510_;
}
else
{
uint8_t v___x_4520_; 
lean_dec_ref(v_requestStream_4488_);
lean_dec_ref(v_reader_4483_);
v___x_4520_ = 0;
v___y_4497_ = v___x_4520_;
goto v___jp_4496_;
}
}
else
{
uint8_t v___x_4521_; 
v___x_4521_ = 0;
v___y_4511_ = v___x_4521_;
goto v___jp_4510_;
}
}
else
{
uint8_t v___x_4522_; 
v___x_4522_ = 0;
v___y_4511_ = v___x_4522_;
goto v___jp_4510_;
}
}
}
v___jp_4503_:
{
if (v_pullBodyStalled_4485_ == 0)
{
if (v_requestBodyOpen_4486_ == 0)
{
lean_dec_ref(v_requestStream_4488_);
v___y_4497_ = v_requestBodyOpen_4486_;
goto v___jp_4496_;
}
else
{
lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4504_, 0, v_requestStream_4488_);
v___x_4505_ = lean_unsigned_to_nat(0u);
v___x_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4504_);
v___x_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4506_);
v___x_4508_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4505_, v_pullBodyStalled_4485_, v___x_4507_, v___f_4495_);
return v___x_4508_;
}
}
else
{
uint8_t v___x_4509_; 
lean_dec_ref(v_requestStream_4488_);
v___x_4509_ = 0;
v___y_4497_ = v___x_4509_;
goto v___jp_4496_;
}
}
v___jp_4510_:
{
lean_object* v_state_4512_; 
v_state_4512_ = lean_ctor_get(v_reader_4483_, 0);
lean_inc(v_state_4512_);
lean_dec_ref(v_reader_4483_);
if (lean_obj_tag(v_state_4512_) == 2)
{
lean_dec_ref_known(v_state_4512_, 1);
goto v___jp_4503_;
}
else
{
lean_dec(v_state_4512_);
if (v___y_4511_ == 0)
{
lean_dec_ref(v_requestStream_4488_);
v___y_4497_ = v___y_4511_;
goto v___jp_4496_;
}
else
{
goto v___jp_4503_;
}
}
}
}
}
v___jp_4496_:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4498_ = lean_unsigned_to_nat(0u);
v___x_4499_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_4500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4498_, v___y_4497_, v___x_4499_, v___f_4495_);
return v___x_4500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object* v_respStream_4523_, lean_object* v_connectionContext_4524_, lean_object* v_handler_4525_, lean_object* v_response_4526_, lean_object* v_inputWanted_4527_, lean_object* v_timer_4528_, lean_object* v_socket_4529_, lean_object* v_reader_4530_, lean_object* v_inputLimit_4531_, lean_object* v_pullBodyStalled_4532_, lean_object* v_requestBodyOpen_4533_, lean_object* v_state_4534_, lean_object* v_requestStream_4535_, lean_object* v_requestBodyInterested_4536_, lean_object* v___y_4537_){
_start:
{
uint8_t v_pullBodyStalled_boxed_4538_; uint8_t v_requestBodyOpen_boxed_4539_; uint8_t v_requestBodyInterested_boxed_4540_; lean_object* v_res_4541_; 
v_pullBodyStalled_boxed_4538_ = lean_unbox(v_pullBodyStalled_4532_);
v_requestBodyOpen_boxed_4539_ = lean_unbox(v_requestBodyOpen_4533_);
v_requestBodyInterested_boxed_4540_ = lean_unbox(v_requestBodyInterested_4536_);
v_res_4541_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_respStream_4523_, v_connectionContext_4524_, v_handler_4525_, v_response_4526_, v_inputWanted_4527_, v_timer_4528_, v_socket_4529_, v_reader_4530_, v_inputLimit_4531_, v_pullBodyStalled_boxed_4538_, v_requestBodyOpen_boxed_4539_, v_state_4534_, v_requestStream_4535_, v_requestBodyInterested_boxed_4540_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_4542_, lean_object* v_x_4543_){
_start:
{
if (lean_obj_tag(v_x_4543_) == 0)
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4553_; 
lean_dec_ref(v___f_4542_);
v_a_4545_ = lean_ctor_get(v_x_4543_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v_x_4543_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4547_ = v_x_4543_;
v_isShared_4548_ = v_isSharedCheck_4553_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v_x_4543_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4553_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
lean_object* v___x_4551_; 
v___x_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4550_);
return v___x_4551_;
}
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4555_; 
v_a_4554_ = lean_ctor_get(v_x_4543_, 0);
lean_inc(v_a_4554_);
lean_dec_ref_known(v_x_4543_, 1);
v___x_4555_ = lean_apply_2(v___f_4542_, v_a_4554_, lean_box(0));
return v___x_4555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_4556_, lean_object* v_x_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_4556_, v_x_4557_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_respStream_4560_, lean_object* v_connectionContext_4561_, lean_object* v_handler_4562_, lean_object* v_response_4563_, lean_object* v_inputWanted_4564_, lean_object* v_timer_4565_, lean_object* v_socket_4566_, lean_object* v_reader_4567_, lean_object* v_inputLimit_4568_, uint8_t v_pullBodyStalled_4569_, lean_object* v_state_4570_, lean_object* v_requestStream_4571_, uint8_t v_requestBodyOpen_4572_){
_start:
{
lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___f_4576_; lean_object* v___f_4577_; uint8_t v___y_4579_; 
v___x_4574_ = lean_box(v_pullBodyStalled_4569_);
v___x_4575_ = lean_box(v_requestBodyOpen_4572_);
lean_inc_ref(v_requestStream_4571_);
lean_inc(v_state_4570_);
lean_inc_ref(v_reader_4567_);
v___f_4576_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 15, 13);
lean_closure_set(v___f_4576_, 0, v_respStream_4560_);
lean_closure_set(v___f_4576_, 1, v_connectionContext_4561_);
lean_closure_set(v___f_4576_, 2, v_handler_4562_);
lean_closure_set(v___f_4576_, 3, v_response_4563_);
lean_closure_set(v___f_4576_, 4, v_inputWanted_4564_);
lean_closure_set(v___f_4576_, 5, v_timer_4565_);
lean_closure_set(v___f_4576_, 6, v_socket_4566_);
lean_closure_set(v___f_4576_, 7, v_reader_4567_);
lean_closure_set(v___f_4576_, 8, v_inputLimit_4568_);
lean_closure_set(v___f_4576_, 9, v___x_4574_);
lean_closure_set(v___f_4576_, 10, v___x_4575_);
lean_closure_set(v___f_4576_, 11, v_state_4570_);
lean_closure_set(v___f_4576_, 12, v_requestStream_4571_);
v___f_4577_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4577_, 0, v___f_4576_);
switch(lean_obj_tag(v_state_4570_))
{
case 6:
{
uint8_t v___x_4585_; 
lean_dec_ref(v_requestStream_4571_);
lean_dec_ref(v_reader_4567_);
v___x_4585_ = 0;
v___y_4579_ = v___x_4585_;
goto v___jp_4578_;
}
case 7:
{
uint8_t v___x_4586_; 
lean_dec_ref(v_requestStream_4571_);
lean_dec_ref(v_reader_4567_);
v___x_4586_ = 0;
v___y_4579_ = v___x_4586_;
goto v___jp_4578_;
}
default: 
{
uint8_t v___y_4593_; 
switch(lean_obj_tag(v_state_4570_))
{
case 0:
{
uint8_t v___x_4595_; 
v___x_4595_ = 0;
v___y_4593_ = v___x_4595_;
goto v___jp_4592_;
}
case 1:
{
uint8_t v___x_4596_; 
v___x_4596_ = 0;
v___y_4593_ = v___x_4596_;
goto v___jp_4592_;
}
default: 
{
lean_object* v_state_4597_; 
lean_dec(v_state_4570_);
v_state_4597_ = lean_ctor_get(v_reader_4567_, 0);
if (lean_obj_tag(v_state_4597_) == 2)
{
lean_object* v_a_4598_; 
v_a_4598_ = lean_ctor_get(v_state_4597_, 0);
if (lean_obj_tag(v_a_4598_) == 0)
{
lean_object* v_remaining_4599_; lean_object* v___x_4600_; uint8_t v___x_4601_; 
v_remaining_4599_ = lean_ctor_get(v_a_4598_, 0);
v___x_4600_ = lean_unsigned_to_nat(0u);
v___x_4601_ = lean_nat_dec_eq(v_remaining_4599_, v___x_4600_);
if (v___x_4601_ == 0)
{
v___y_4593_ = v___x_4601_;
goto v___jp_4592_;
}
else
{
uint8_t v___x_4602_; 
lean_dec_ref(v_requestStream_4571_);
lean_dec_ref(v_reader_4567_);
v___x_4602_ = 0;
v___y_4579_ = v___x_4602_;
goto v___jp_4578_;
}
}
else
{
uint8_t v___x_4603_; 
v___x_4603_ = 0;
v___y_4593_ = v___x_4603_;
goto v___jp_4592_;
}
}
else
{
uint8_t v___x_4604_; 
v___x_4604_ = 0;
v___y_4593_ = v___x_4604_;
goto v___jp_4592_;
}
}
}
v___jp_4587_:
{
if (v_requestBodyOpen_4572_ == 0)
{
lean_dec_ref(v_requestStream_4571_);
v___y_4579_ = v_requestBodyOpen_4572_;
goto v___jp_4578_;
}
else
{
lean_object* v___x_4588_; uint8_t v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; 
v___x_4588_ = lean_unsigned_to_nat(0u);
v___x_4589_ = 0;
v___x_4590_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_4571_);
v___x_4591_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4588_, v___x_4589_, v___x_4590_, v___f_4577_);
return v___x_4591_;
}
}
v___jp_4592_:
{
lean_object* v_state_4594_; 
v_state_4594_ = lean_ctor_get(v_reader_4567_, 0);
lean_inc(v_state_4594_);
lean_dec_ref(v_reader_4567_);
if (lean_obj_tag(v_state_4594_) == 2)
{
lean_dec_ref_known(v_state_4594_, 1);
goto v___jp_4587_;
}
else
{
lean_dec(v_state_4594_);
if (v___y_4593_ == 0)
{
lean_dec_ref(v_requestStream_4571_);
v___y_4579_ = v___y_4593_;
goto v___jp_4578_;
}
else
{
goto v___jp_4587_;
}
}
}
}
}
v___jp_4578_:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4580_ = lean_unsigned_to_nat(0u);
v___x_4581_ = lean_box(v___y_4579_);
v___x_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
v___x_4583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
v___x_4584_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4580_, v___y_4579_, v___x_4583_, v___f_4577_);
return v___x_4584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_respStream_4605_, lean_object* v_connectionContext_4606_, lean_object* v_handler_4607_, lean_object* v_response_4608_, lean_object* v_inputWanted_4609_, lean_object* v_timer_4610_, lean_object* v_socket_4611_, lean_object* v_reader_4612_, lean_object* v_inputLimit_4613_, lean_object* v_pullBodyStalled_4614_, lean_object* v_state_4615_, lean_object* v_requestStream_4616_, lean_object* v_requestBodyOpen_4617_, lean_object* v___y_4618_){
_start:
{
uint8_t v_pullBodyStalled_boxed_4619_; uint8_t v_requestBodyOpen_boxed_4620_; lean_object* v_res_4621_; 
v_pullBodyStalled_boxed_4619_ = lean_unbox(v_pullBodyStalled_4614_);
v_requestBodyOpen_boxed_4620_ = lean_unbox(v_requestBodyOpen_4617_);
v_res_4621_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_respStream_4605_, v_connectionContext_4606_, v_handler_4607_, v_response_4608_, v_inputWanted_4609_, v_timer_4610_, v_socket_4611_, v_reader_4612_, v_inputLimit_4613_, v_pullBodyStalled_boxed_4619_, v_state_4615_, v_requestStream_4616_, v_requestBodyOpen_boxed_4620_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7(lean_object* v___f_4622_, uint8_t v___y_4623_, lean_object* v_x_4624_){
_start:
{
uint8_t v___y_4627_; 
if (lean_obj_tag(v_x_4624_) == 0)
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4642_; 
lean_dec_ref(v___f_4622_);
v_a_4634_ = lean_ctor_get(v_x_4624_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v_x_4624_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4636_ = v_x_4624_;
v_isShared_4637_ = v_isSharedCheck_4642_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v_x_4624_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4642_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4639_; 
if (v_isShared_4637_ == 0)
{
v___x_4639_ = v___x_4636_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_a_4634_);
v___x_4639_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
lean_object* v___x_4640_; 
v___x_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
return v___x_4640_;
}
}
}
else
{
lean_object* v_a_4643_; uint8_t v___x_4644_; 
v_a_4643_ = lean_ctor_get(v_x_4624_, 0);
lean_inc(v_a_4643_);
lean_dec_ref_known(v_x_4624_, 1);
v___x_4644_ = lean_unbox(v_a_4643_);
lean_dec(v_a_4643_);
if (v___x_4644_ == 0)
{
v___y_4627_ = v___y_4623_;
goto v___jp_4626_;
}
else
{
uint8_t v___x_4645_; 
v___x_4645_ = 0;
v___y_4627_ = v___x_4645_;
goto v___jp_4626_;
}
}
v___jp_4626_:
{
lean_object* v___x_4628_; uint8_t v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4628_ = lean_unsigned_to_nat(0u);
v___x_4629_ = 0;
v___x_4630_ = lean_box(v___y_4627_);
v___x_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4630_);
v___x_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4631_);
v___x_4633_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4628_, v___x_4629_, v___x_4632_, v___f_4622_);
return v___x_4633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7___boxed(lean_object* v___f_4646_, lean_object* v___y_4647_, lean_object* v_x_4648_, lean_object* v___y_4649_){
_start:
{
uint8_t v___y_3801__boxed_4650_; lean_object* v_res_4651_; 
v___y_3801__boxed_4650_ = lean_unbox(v___y_4647_);
v_res_4651_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7(v___f_4646_, v___y_3801__boxed_4650_, v_x_4648_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4(uint8_t v___y_4652_, lean_object* v_____do__lift_4653_, lean_object* v___y_4654_){
_start:
{
uint8_t v___y_4657_; lean_object* v_ended_4661_; 
v_ended_4661_ = lean_ctor_get(v_____do__lift_4653_, 3);
if (lean_obj_tag(v_ended_4661_) == 0)
{
uint8_t v___x_4662_; 
v___x_4662_ = 0;
v___y_4657_ = v___x_4662_;
goto v___jp_4656_;
}
else
{
v___y_4657_ = v___y_4652_;
goto v___jp_4656_;
}
v___jp_4656_:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4658_ = lean_box(v___y_4657_);
v___x_4659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4658_);
v___x_4660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4660_, 0, v___x_4659_);
return v___x_4660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4___boxed(lean_object* v___y_4663_, lean_object* v_____do__lift_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
uint8_t v___y_3852__boxed_4667_; lean_object* v_res_4668_; 
v___y_3852__boxed_4667_ = lean_unbox(v___y_4663_);
v_res_4668_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4(v___y_3852__boxed_4667_, v_____do__lift_4664_, v___y_4665_);
lean_dec(v___y_4665_);
lean_dec_ref(v_____do__lift_4664_);
return v_res_4668_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3(void){
_start:
{
lean_object* v___x_4676_; lean_object* v___f_4677_; lean_object* v___f_4678_; 
v___x_4676_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1);
v___f_4677_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__2));
v___f_4678_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_4678_, 0, v___f_4677_);
lean_closure_set(v___f_4678_, 1, v___x_4676_);
return v___f_4678_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4(void){
_start:
{
lean_object* v___f_4679_; lean_object* v___x_4680_; 
v___f_4679_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3);
v___x_4680_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_4680_, 0, lean_box(0));
lean_closure_set(v___x_4680_, 1, lean_box(0));
lean_closure_set(v___x_4680_, 2, lean_box(0));
lean_closure_set(v___x_4680_, 3, v___f_4679_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_4681_, lean_object* v_connectionContext_4682_, lean_object* v_state_4683_, lean_object* v_inputWanted_4684_, lean_object* v_inputLimit_4685_){
_start:
{
lean_object* v_machine_4687_; lean_object* v_writer_4688_; lean_object* v_requestStream_4689_; lean_object* v_timer_4690_; lean_object* v_response_4691_; lean_object* v_respStream_4692_; lean_object* v_handler_4693_; lean_object* v_reader_4694_; uint8_t v_pullBodyStalled_4695_; lean_object* v_state_4696_; lean_object* v___x_4697_; lean_object* v___f_4698_; lean_object* v___f_4699_; uint8_t v___y_4701_; 
v_machine_4687_ = lean_ctor_get(v_state_4683_, 0);
lean_inc_ref(v_machine_4687_);
v_writer_4688_ = lean_ctor_get(v_machine_4687_, 1);
lean_inc_ref(v_writer_4688_);
v_requestStream_4689_ = lean_ctor_get(v_state_4683_, 1);
lean_inc_ref_n(v_requestStream_4689_, 2);
v_timer_4690_ = lean_ctor_get(v_state_4683_, 2);
lean_inc_ref(v_timer_4690_);
v_response_4691_ = lean_ctor_get(v_state_4683_, 3);
lean_inc_ref(v_response_4691_);
v_respStream_4692_ = lean_ctor_get(v_state_4683_, 4);
lean_inc(v_respStream_4692_);
v_handler_4693_ = lean_ctor_get(v_state_4683_, 6);
lean_inc(v_handler_4693_);
lean_dec_ref(v_state_4683_);
v_reader_4694_ = lean_ctor_get(v_machine_4687_, 0);
lean_inc_ref_n(v_reader_4694_, 2);
v_pullBodyStalled_4695_ = lean_ctor_get_uint8(v_machine_4687_, sizeof(void*)*6 + 1);
lean_dec_ref(v_machine_4687_);
v_state_4696_ = lean_ctor_get(v_writer_4688_, 2);
lean_inc_n(v_state_4696_, 2);
lean_dec_ref(v_writer_4688_);
v___x_4697_ = lean_box(v_pullBodyStalled_4695_);
v___f_4698_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 14, 12);
lean_closure_set(v___f_4698_, 0, v_respStream_4692_);
lean_closure_set(v___f_4698_, 1, v_connectionContext_4682_);
lean_closure_set(v___f_4698_, 2, v_handler_4693_);
lean_closure_set(v___f_4698_, 3, v_response_4691_);
lean_closure_set(v___f_4698_, 4, v_inputWanted_4684_);
lean_closure_set(v___f_4698_, 5, v_timer_4690_);
lean_closure_set(v___f_4698_, 6, v_socket_4681_);
lean_closure_set(v___f_4698_, 7, v_reader_4694_);
lean_closure_set(v___f_4698_, 8, v_inputLimit_4685_);
lean_closure_set(v___f_4698_, 9, v___x_4697_);
lean_closure_set(v___f_4698_, 10, v_state_4696_);
lean_closure_set(v___f_4698_, 11, v_requestStream_4689_);
v___f_4699_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4699_, 0, v___f_4698_);
switch(lean_obj_tag(v_state_4696_))
{
case 6:
{
uint8_t v___x_4707_; 
lean_dec_ref(v_reader_4694_);
lean_dec_ref(v_requestStream_4689_);
v___x_4707_ = 0;
v___y_4701_ = v___x_4707_;
goto v___jp_4700_;
}
case 7:
{
uint8_t v___x_4708_; 
lean_dec_ref(v_reader_4694_);
lean_dec_ref(v_requestStream_4689_);
v___x_4708_ = 0;
v___y_4701_ = v___x_4708_;
goto v___jp_4700_;
}
default: 
{
uint8_t v___y_4710_; uint8_t v___y_4726_; 
switch(lean_obj_tag(v_state_4696_))
{
case 0:
{
uint8_t v___x_4729_; 
v___x_4729_ = 0;
v___y_4726_ = v___x_4729_;
goto v___jp_4725_;
}
case 1:
{
uint8_t v___x_4730_; 
v___x_4730_ = 0;
v___y_4726_ = v___x_4730_;
goto v___jp_4725_;
}
default: 
{
lean_object* v_state_4731_; 
lean_dec(v_state_4696_);
v_state_4731_ = lean_ctor_get(v_reader_4694_, 0);
if (lean_obj_tag(v_state_4731_) == 2)
{
lean_object* v_a_4732_; 
v_a_4732_ = lean_ctor_get(v_state_4731_, 0);
if (lean_obj_tag(v_a_4732_) == 0)
{
lean_object* v_remaining_4733_; lean_object* v___x_4734_; uint8_t v___x_4735_; 
v_remaining_4733_ = lean_ctor_get(v_a_4732_, 0);
v___x_4734_ = lean_unsigned_to_nat(0u);
v___x_4735_ = lean_nat_dec_eq(v_remaining_4733_, v___x_4734_);
if (v___x_4735_ == 0)
{
v___y_4726_ = v___x_4735_;
goto v___jp_4725_;
}
else
{
uint8_t v___x_4736_; 
lean_dec_ref(v_reader_4694_);
lean_dec_ref(v_requestStream_4689_);
v___x_4736_ = 0;
v___y_4701_ = v___x_4736_;
goto v___jp_4700_;
}
}
else
{
uint8_t v___x_4737_; 
v___x_4737_ = 0;
v___y_4726_ = v___x_4737_;
goto v___jp_4725_;
}
}
else
{
uint8_t v___x_4738_; 
v___x_4738_ = 0;
v___y_4726_ = v___x_4738_;
goto v___jp_4725_;
}
}
}
v___jp_4709_:
{
lean_object* v___x_4711_; lean_object* v___f_4712_; lean_object* v___x_4713_; lean_object* v___f_4714_; lean_object* v___x_4715_; uint8_t v___x_4716_; lean_object* v___x_4717_; lean_object* v___f_4718_; lean_object* v___f_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_3153__overap_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4711_ = lean_box(v___y_4710_);
v___f_4712_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_4712_, 0, v___f_4699_);
lean_closure_set(v___f_4712_, 1, v___x_4711_);
v___x_4713_ = lean_box(v___y_4710_);
v___f_4714_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4___boxed), 4, 1);
lean_closure_set(v___f_4714_, 0, v___x_4713_);
v___x_4715_ = lean_unsigned_to_nat(0u);
v___x_4716_ = 0;
v___x_4717_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0);
v___f_4718_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5);
v___f_4719_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__6));
v___x_4720_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4);
v___x_4721_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4721_, 0, lean_box(0));
lean_closure_set(v___x_4721_, 1, lean_box(0));
lean_closure_set(v___x_4721_, 2, v___x_4717_);
lean_closure_set(v___x_4721_, 3, lean_box(0));
lean_closure_set(v___x_4721_, 4, lean_box(0));
lean_closure_set(v___x_4721_, 5, v___x_4720_);
lean_closure_set(v___x_4721_, 6, v___f_4714_);
v___x_3153__overap_4722_ = l_Std_Mutex_atomically___redArg(v___x_4717_, v___f_4718_, v___f_4719_, v_requestStream_4689_, v___x_4721_);
v___x_4723_ = lean_apply_1(v___x_3153__overap_4722_, lean_box(0));
v___x_4724_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4715_, v___x_4716_, v___x_4723_, v___f_4712_);
return v___x_4724_;
}
v___jp_4725_:
{
lean_object* v_state_4727_; 
v_state_4727_ = lean_ctor_get(v_reader_4694_, 0);
lean_inc(v_state_4727_);
lean_dec_ref(v_reader_4694_);
if (lean_obj_tag(v_state_4727_) == 2)
{
uint8_t v___x_4728_; 
lean_dec_ref_known(v_state_4727_, 1);
v___x_4728_ = 1;
v___y_4710_ = v___x_4728_;
goto v___jp_4709_;
}
else
{
lean_dec(v_state_4727_);
if (v___y_4726_ == 0)
{
lean_dec_ref(v_requestStream_4689_);
v___y_4701_ = v___y_4726_;
goto v___jp_4700_;
}
else
{
v___y_4710_ = v___y_4726_;
goto v___jp_4709_;
}
}
}
}
}
v___jp_4700_:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
v___x_4702_ = lean_unsigned_to_nat(0u);
v___x_4703_ = lean_box(v___y_4701_);
v___x_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4704_, 0, v___x_4703_);
v___x_4705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4705_, 0, v___x_4704_);
v___x_4706_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4702_, v___y_4701_, v___x_4705_, v___f_4699_);
return v___x_4706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_4739_, lean_object* v_connectionContext_4740_, lean_object* v_state_4741_, lean_object* v_inputWanted_4742_, lean_object* v_inputLimit_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4739_, v_connectionContext_4740_, v_state_4741_, v_inputWanted_4742_, v_inputLimit_4743_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_4746_, lean_object* v_00_u03b2_4747_, lean_object* v_inst_4748_, lean_object* v_socket_4749_, lean_object* v_connectionContext_4750_, lean_object* v_state_4751_, lean_object* v_inputWanted_4752_, lean_object* v_inputLimit_4753_){
_start:
{
lean_object* v___x_4755_; 
v___x_4755_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4749_, v_connectionContext_4750_, v_state_4751_, v_inputWanted_4752_, v_inputLimit_4753_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4756_, lean_object* v_00_u03b2_4757_, lean_object* v_inst_4758_, lean_object* v_socket_4759_, lean_object* v_connectionContext_4760_, lean_object* v_state_4761_, lean_object* v_inputWanted_4762_, lean_object* v_inputLimit_4763_, lean_object* v_a_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4756_, v_00_u03b2_4757_, v_inst_4758_, v_socket_4759_, v_connectionContext_4760_, v_state_4761_, v_inputWanted_4762_, v_inputLimit_4763_);
lean_dec_ref(v_inst_4758_);
return v_res_4765_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput(lean_object* v_x_4766_){
_start:
{
switch(lean_obj_tag(v_x_4766_))
{
case 0:
{
lean_object* v_head_4767_; uint8_t v_method_4768_; uint8_t v___x_4769_; 
v_head_4767_ = lean_ctor_get(v_x_4766_, 0);
v_method_4768_ = lean_ctor_get_uint8(v_head_4767_, sizeof(void*)*2);
v___x_4769_ = l_Std_Http_Method_isSafe(v_method_4768_);
if (v___x_4769_ == 0)
{
uint8_t v___x_4770_; 
v___x_4770_ = 1;
return v___x_4770_;
}
else
{
uint8_t v___x_4771_; 
v___x_4771_ = 0;
return v___x_4771_;
}
}
case 7:
{
uint8_t v___x_4772_; 
v___x_4772_ = 1;
return v___x_4772_;
}
default: 
{
uint8_t v___x_4773_; 
v___x_4773_ = 0;
return v___x_4773_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput___boxed(lean_object* v_x_4774_){
_start:
{
uint8_t v_res_4775_; lean_object* v_r_4776_; 
v_res_4775_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput(v_x_4774_);
lean_dec(v_x_4774_);
v_r_4776_ = lean_box(v_res_4775_);
return v_r_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0(lean_object* v_inst_4777_, lean_object* v_handler_4778_, lean_object* v_x_4779_){
_start:
{
if (lean_obj_tag(v_x_4779_) == 0)
{
lean_object* v_a_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4789_; 
lean_dec(v_handler_4778_);
lean_dec_ref(v_inst_4777_);
v_a_4781_ = lean_ctor_get(v_x_4779_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v_x_4779_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4783_ = v_x_4779_;
v_isShared_4784_ = v_isSharedCheck_4789_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_a_4781_);
lean_dec(v_x_4779_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4789_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4786_; 
if (v_isShared_4784_ == 0)
{
v___x_4786_ = v___x_4783_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4781_);
v___x_4786_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
lean_object* v___x_4787_; 
v___x_4787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4786_);
return v___x_4787_;
}
}
}
else
{
lean_object* v_a_4790_; 
v_a_4790_ = lean_ctor_get(v_x_4779_, 0);
lean_inc(v_a_4790_);
lean_dec_ref_known(v_x_4779_, 1);
if (lean_obj_tag(v_a_4790_) == 1)
{
lean_object* v_val_4791_; lean_object* v___x_4792_; 
v_val_4791_ = lean_ctor_get(v_a_4790_, 0);
lean_inc(v_val_4791_);
lean_dec_ref_known(v_a_4790_, 1);
v___x_4792_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_4777_, v_handler_4778_, v_val_4791_);
return v___x_4792_;
}
else
{
lean_object* v___x_4793_; 
lean_dec(v_a_4790_);
lean_dec(v_handler_4778_);
lean_dec_ref(v_inst_4777_);
v___x_4793_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_4793_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0___boxed(lean_object* v_inst_4794_, lean_object* v_handler_4795_, lean_object* v_x_4796_, lean_object* v___y_4797_){
_start:
{
lean_object* v_res_4798_; 
v_res_4798_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0(v_inst_4794_, v_handler_4795_, v_x_4796_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(lean_object* v_inst_4799_, lean_object* v_handler_4800_, lean_object* v_outbox_4801_){
_start:
{
lean_object* v___f_4803_; lean_object* v___x_4804_; uint8_t v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___f_4803_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4803_, 0, v_inst_4799_);
lean_closure_set(v___f_4803_, 1, v_handler_4800_);
v___x_4804_ = lean_unsigned_to_nat(0u);
v___x_4805_ = 0;
v___x_4806_ = l_Std_Http_Internal_Outbox_takeError_x3f___redArg(v_outbox_4801_);
v___x_4807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4807_, 0, v___x_4806_);
v___x_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4808_, 0, v___x_4807_);
v___x_4809_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4804_, v___x_4805_, v___x_4808_, v___f_4803_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___boxed(lean_object* v_inst_4810_, lean_object* v_handler_4811_, lean_object* v_outbox_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_inst_4810_, v_handler_4811_, v_outbox_4812_);
lean_dec_ref(v_outbox_4812_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure(lean_object* v_00_u03c3_4815_, lean_object* v_00_u03b1_4816_, lean_object* v_inst_4817_, lean_object* v_handler_4818_, lean_object* v_outbox_4819_){
_start:
{
lean_object* v___x_4821_; 
v___x_4821_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_inst_4817_, v_handler_4818_, v_outbox_4819_);
return v___x_4821_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___boxed(lean_object* v_00_u03c3_4822_, lean_object* v_00_u03b1_4823_, lean_object* v_inst_4824_, lean_object* v_handler_4825_, lean_object* v_outbox_4826_, lean_object* v_a_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure(v_00_u03c3_4822_, v_00_u03b1_4823_, v_inst_4824_, v_handler_4825_, v_outbox_4826_);
lean_dec_ref(v_outbox_4826_);
return v_res_4828_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(lean_object* v_state_4829_){
_start:
{
lean_object* v_machine_4830_; lean_object* v_reader_4831_; uint8_t v_peerClosed_4832_; 
v_machine_4830_ = lean_ctor_get(v_state_4829_, 0);
v_reader_4831_ = lean_ctor_get(v_machine_4830_, 0);
v_peerClosed_4832_ = lean_ctor_get_uint8(v_reader_4831_, sizeof(void*)*6);
if (v_peerClosed_4832_ == 0)
{
uint8_t v_requestEnded_4833_; lean_object* v_error_4834_; lean_object* v_state_4835_; lean_object* v_input_4836_; uint8_t v_inputStopped_4837_; uint8_t v___x_4838_; 
v_requestEnded_4833_ = lean_ctor_get_uint8(v_state_4829_, sizeof(void*)*9);
v_error_4834_ = lean_ctor_get(v_machine_4830_, 4);
v_state_4835_ = lean_ctor_get(v_reader_4831_, 0);
v_input_4836_ = lean_ctor_get(v_reader_4831_, 1);
v_inputStopped_4837_ = lean_ctor_get_uint8(v_reader_4831_, sizeof(void*)*6 + 1);
v___x_4838_ = 1;
if (v_requestEnded_4833_ == 0)
{
return v___x_4838_;
}
else
{
if (v_inputStopped_4837_ == 0)
{
if (lean_obj_tag(v_error_4834_) == 0)
{
lean_object* v_array_4839_; lean_object* v_idx_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; uint8_t v___x_4844_; 
v_array_4839_ = lean_ctor_get(v_input_4836_, 0);
v_idx_4840_ = lean_ctor_get(v_input_4836_, 1);
v___x_4841_ = lean_unsigned_to_nat(0u);
v___x_4842_ = lean_byte_array_size(v_array_4839_);
v___x_4843_ = lean_nat_sub(v___x_4842_, v_idx_4840_);
v___x_4844_ = lean_nat_dec_lt(v___x_4841_, v___x_4843_);
lean_dec(v___x_4843_);
if (v___x_4844_ == 0)
{
if (lean_obj_tag(v_state_4835_) == 2)
{
return v___x_4838_;
}
else
{
return v___x_4844_;
}
}
else
{
return v___x_4844_;
}
}
else
{
return v___x_4838_;
}
}
else
{
return v_peerClosed_4832_;
}
}
}
else
{
uint8_t v___x_4845_; 
v___x_4845_ = 0;
return v___x_4845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg___boxed(lean_object* v_state_4846_){
_start:
{
uint8_t v_res_4847_; lean_object* v_r_4848_; 
v_res_4847_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(v_state_4846_);
lean_dec_ref(v_state_4846_);
v_r_4848_ = lean_box(v_res_4847_);
return v_r_4848_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend(lean_object* v_00_u03b2_4849_, lean_object* v_state_4850_){
_start:
{
uint8_t v___x_4851_; 
v___x_4851_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(v_state_4850_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___boxed(lean_object* v_00_u03b2_4852_, lean_object* v_state_4853_){
_start:
{
uint8_t v_res_4854_; lean_object* v_r_4855_; 
v_res_4854_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend(v_00_u03b2_4852_, v_state_4853_);
lean_dec_ref(v_state_4853_);
v_r_4855_ = lean_box(v_res_4854_);
return v_r_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__0(lean_object* v_x_4856_){
_start:
{
if (lean_obj_tag(v_x_4856_) == 0)
{
lean_object* v___x_4858_; 
v___x_4858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4858_, 0, v_x_4856_);
return v___x_4858_;
}
else
{
lean_object* v___x_4859_; 
lean_dec_ref_known(v_x_4856_, 1);
v___x_4859_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_4859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__0___boxed(lean_object* v_x_4860_, lean_object* v___y_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__0(v_x_4860_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__1(lean_object* v___x_4863_, lean_object* v_x_4864_){
_start:
{
if (lean_obj_tag(v_x_4864_) == 0)
{
lean_object* v_a_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4874_; 
v_a_4866_ = lean_ctor_get(v_x_4864_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v_x_4864_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4868_ = v_x_4864_;
v_isShared_4869_ = v_isSharedCheck_4874_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v_x_4864_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4874_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___x_4871_; 
if (v_isShared_4869_ == 0)
{
v___x_4871_ = v___x_4868_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4866_);
v___x_4871_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
lean_object* v___x_4872_; 
v___x_4872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4871_);
return v___x_4872_;
}
}
}
else
{
lean_object* v_a_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4890_; 
v_a_4875_ = lean_ctor_get(v_x_4864_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v_x_4864_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4877_ = v_x_4864_;
v_isShared_4878_ = v_isSharedCheck_4890_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_a_4875_);
lean_dec(v_x_4864_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4890_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
uint8_t v___x_4879_; 
v___x_4879_ = lean_unbox(v_a_4875_);
lean_dec(v_a_4875_);
if (v___x_4879_ == 0)
{
lean_object* v___x_4880_; lean_object* v___x_4882_; 
v___x_4880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4863_);
if (v_isShared_4878_ == 0)
{
lean_ctor_set(v___x_4877_, 0, v___x_4880_);
v___x_4882_ = v___x_4877_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
lean_object* v___x_4883_; 
v___x_4883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4882_);
return v___x_4883_;
}
}
else
{
lean_object* v___x_4885_; lean_object* v___x_4887_; 
v___x_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4863_);
if (v_isShared_4878_ == 0)
{
lean_ctor_set(v___x_4877_, 0, v___x_4885_);
v___x_4887_ = v___x_4877_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4885_);
v___x_4887_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
lean_object* v___x_4888_; 
v___x_4888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4888_, 0, v___x_4887_);
return v___x_4888_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__1___boxed(lean_object* v___x_4891_, lean_object* v_x_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__1(v___x_4891_, v_x_4892_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2(uint8_t v___x_4895_, lean_object* v_x_4896_){
_start:
{
if (lean_obj_tag(v_x_4896_) == 0)
{
lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4906_; 
v_isSharedCheck_4906_ = !lean_is_exclusive(v_x_4896_);
if (v_isSharedCheck_4906_ == 0)
{
lean_object* v_unused_4907_; 
v_unused_4907_ = lean_ctor_get(v_x_4896_, 0);
lean_dec(v_unused_4907_);
v___x_4899_ = v_x_4896_;
v_isShared_4900_ = v_isSharedCheck_4906_;
goto v_resetjp_4898_;
}
else
{
lean_dec(v_x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4906_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4901_; lean_object* v___x_4903_; 
v___x_4901_ = lean_box(v___x_4895_);
if (v_isShared_4900_ == 0)
{
lean_ctor_set_tag(v___x_4899_, 1);
lean_ctor_set(v___x_4899_, 0, v___x_4901_);
v___x_4903_ = v___x_4899_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v___x_4901_);
v___x_4903_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
lean_object* v___x_4904_; 
v___x_4904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4903_);
return v___x_4904_;
}
}
}
else
{
lean_object* v___x_4908_; 
v___x_4908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4908_, 0, v_x_4896_);
return v___x_4908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2___boxed(lean_object* v___x_4909_, lean_object* v_x_4910_, lean_object* v___y_4911_){
_start:
{
uint8_t v___x_2477__boxed_4912_; lean_object* v_res_4913_; 
v___x_2477__boxed_4912_ = lean_unbox(v___x_4909_);
v_res_4913_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2(v___x_2477__boxed_4912_, v_x_4910_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3(uint8_t v___x_4914_, uint8_t v_a_4915_, lean_object* v_data_4916_){
_start:
{
uint8_t v___y_4919_; 
if (lean_obj_tag(v_data_4916_) == 0)
{
v___y_4919_ = v___x_4914_;
goto v___jp_4918_;
}
else
{
v___y_4919_ = v_a_4915_;
goto v___jp_4918_;
}
v___jp_4918_:
{
lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v___x_4920_ = lean_box(v___y_4919_);
v___x_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4920_);
v___x_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4922_, 0, v___x_4921_);
return v___x_4922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3___boxed(lean_object* v___x_4923_, lean_object* v_a_4924_, lean_object* v_data_4925_, lean_object* v___y_4926_){
_start:
{
uint8_t v___x_2510__boxed_4927_; uint8_t v_a_2511__boxed_4928_; lean_object* v_res_4929_; 
v___x_2510__boxed_4927_ = lean_unbox(v___x_4923_);
v_a_2511__boxed_4928_ = lean_unbox(v_a_4924_);
v_res_4929_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3(v___x_2510__boxed_4927_, v_a_2511__boxed_4928_, v_data_4925_);
lean_dec(v_data_4925_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5(lean_object* v_connectionContext_4930_, lean_object* v_recvSelector_4931_, lean_object* v_socket_4932_, uint64_t v_readSize_4933_, lean_object* v___f_4934_, lean_object* v___f_4935_, lean_object* v_x_4936_){
_start:
{
if (lean_obj_tag(v_x_4936_) == 0)
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4946_; 
lean_dec_ref(v___f_4935_);
lean_dec_ref(v___f_4934_);
lean_dec(v_socket_4932_);
lean_dec_ref(v_recvSelector_4931_);
lean_dec_ref(v_connectionContext_4930_);
v_a_4938_ = lean_ctor_get(v_x_4936_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v_x_4936_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4940_ = v_x_4936_;
v_isShared_4941_ = v_isSharedCheck_4946_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v_x_4936_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4946_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
lean_object* v___x_4944_; 
v___x_4944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4943_);
return v___x_4944_;
}
}
}
else
{
lean_object* v_a_4947_; lean_object* v_token_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; 
v_a_4947_ = lean_ctor_get(v_x_4936_, 0);
lean_inc(v_a_4947_);
lean_dec_ref_known(v_x_4936_, 1);
v_token_4948_ = lean_ctor_get(v_connectionContext_4930_, 1);
lean_inc_ref(v_token_4948_);
lean_dec_ref(v_connectionContext_4930_);
v___x_4949_ = lean_box_uint64(v_readSize_4933_);
v___x_4950_ = lean_apply_2(v_recvSelector_4931_, v_socket_4932_, v___x_4949_);
v___x_4951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4950_);
lean_ctor_set(v___x_4951_, 1, v___f_4934_);
v___x_4952_ = l_Std_CancellationToken_selector(v_token_4948_);
lean_inc_ref(v___f_4935_);
v___x_4953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4953_, 0, v___x_4952_);
lean_ctor_set(v___x_4953_, 1, v___f_4935_);
v___x_4954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4954_, 0, v_a_4947_);
lean_ctor_set(v___x_4954_, 1, v___f_4935_);
v___x_4955_ = lean_unsigned_to_nat(3u);
v___x_4956_ = lean_mk_empty_array_with_capacity(v___x_4955_);
v___x_4957_ = lean_array_push(v___x_4956_, v___x_4951_);
v___x_4958_ = lean_array_push(v___x_4957_, v___x_4953_);
v___x_4959_ = lean_array_push(v___x_4958_, v___x_4954_);
v___x_4960_ = l_Std_Async_Selectable_one___redArg(v___x_4959_);
return v___x_4960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5___boxed(lean_object* v_connectionContext_4961_, lean_object* v_recvSelector_4962_, lean_object* v_socket_4963_, lean_object* v_readSize_4964_, lean_object* v___f_4965_, lean_object* v___f_4966_, lean_object* v_x_4967_, lean_object* v___y_4968_){
_start:
{
uint64_t v_readSize_boxed_4969_; lean_object* v_res_4970_; 
v_readSize_boxed_4969_ = lean_unbox_uint64(v_readSize_4964_);
lean_dec_ref(v_readSize_4964_);
v_res_4970_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5(v_connectionContext_4961_, v_recvSelector_4962_, v_socket_4963_, v_readSize_boxed_4969_, v___f_4965_, v___f_4966_, v_x_4967_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4(lean_object* v___x_4971_, uint8_t v_a_4972_, lean_object* v_connectionContext_4973_, lean_object* v_recvSelector_4974_, lean_object* v_socket_4975_, uint64_t v_readSize_4976_, lean_object* v___f_4977_, lean_object* v___x_4978_, lean_object* v_x_4979_){
_start:
{
if (lean_obj_tag(v_x_4979_) == 0)
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4989_; 
lean_dec_ref(v___f_4977_);
lean_dec(v_socket_4975_);
lean_dec_ref(v_recvSelector_4974_);
lean_dec_ref(v_connectionContext_4973_);
v_a_4981_ = lean_ctor_get(v_x_4979_, 0);
v_isSharedCheck_4989_ = !lean_is_exclusive(v_x_4979_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4983_ = v_x_4979_;
v_isShared_4984_ = v_isSharedCheck_4989_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v_x_4979_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4989_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
lean_object* v___x_4987_; 
v___x_4987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4986_);
return v___x_4987_;
}
}
}
else
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_5016_; 
v_a_4990_ = lean_ctor_get(v_x_4979_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v_x_4979_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_4992_ = v_x_4979_;
v_isShared_4993_ = v_isSharedCheck_5016_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v_x_4979_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_5016_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
uint8_t v___x_4994_; 
v___x_4994_ = lean_nat_dec_le(v___x_4971_, v_a_4990_);
if (v___x_4994_ == 0)
{
lean_object* v___x_4995_; lean_object* v___f_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___f_4999_; lean_object* v___x_5000_; lean_object* v___f_5001_; lean_object* v___x_5002_; lean_object* v___f_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
lean_del_object(v___x_4992_);
v___x_4995_ = lean_box(v___x_4994_);
v___f_4996_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4996_, 0, v___x_4995_);
v___x_4997_ = lean_box(v___x_4994_);
v___x_4998_ = lean_box(v_a_4972_);
v___f_4999_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_4999_, 0, v___x_4997_);
lean_closure_set(v___f_4999_, 1, v___x_4998_);
v___x_5000_ = lean_box(v___x_4994_);
v___f_5001_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_5001_, 0, v___x_5000_);
v___x_5002_ = lean_box_uint64(v_readSize_4976_);
v___f_5003_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_5003_, 0, v_connectionContext_4973_);
lean_closure_set(v___f_5003_, 1, v_recvSelector_4974_);
lean_closure_set(v___f_5003_, 2, v_socket_4975_);
lean_closure_set(v___f_5003_, 3, v___x_5002_);
lean_closure_set(v___f_5003_, 4, v___f_4999_);
lean_closure_set(v___f_5003_, 5, v___f_5001_);
v___x_5004_ = lean_nat_sub(v___x_4971_, v_a_4990_);
lean_dec(v_a_4990_);
v___x_5005_ = lean_nat_to_int(v___x_5004_);
v___x_5006_ = lean_unsigned_to_nat(0u);
v___x_5007_ = l_Std_Async_Selector_sleep(v___x_5005_);
lean_dec(v___x_5005_);
v___x_5008_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5006_, v___x_4994_, v___x_5007_, v___f_5003_);
v___x_5009_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5006_, v___x_4994_, v___x_5008_, v___f_4996_);
v___x_5010_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5006_, v___x_4994_, v___x_5009_, v___f_4977_);
return v___x_5010_;
}
else
{
lean_object* v___x_5011_; lean_object* v___x_5013_; 
lean_dec(v_a_4990_);
lean_dec_ref(v___f_4977_);
lean_dec(v_socket_4975_);
lean_dec_ref(v_recvSelector_4974_);
lean_dec_ref(v_connectionContext_4973_);
v___x_5011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5011_, 0, v___x_4978_);
if (v_isShared_4993_ == 0)
{
lean_ctor_set(v___x_4992_, 0, v___x_5011_);
v___x_5013_ = v___x_4992_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v___x_5011_);
v___x_5013_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
lean_object* v___x_5014_; 
v___x_5014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5014_, 0, v___x_5013_);
return v___x_5014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4___boxed(lean_object* v___x_5017_, lean_object* v_a_5018_, lean_object* v_connectionContext_5019_, lean_object* v_recvSelector_5020_, lean_object* v_socket_5021_, lean_object* v_readSize_5022_, lean_object* v___f_5023_, lean_object* v___x_5024_, lean_object* v_x_5025_, lean_object* v___y_5026_){
_start:
{
uint8_t v_a_2587__boxed_5027_; uint64_t v_readSize_boxed_5028_; lean_object* v_res_5029_; 
v_a_2587__boxed_5027_ = lean_unbox(v_a_5018_);
v_readSize_boxed_5028_ = lean_unbox_uint64(v_readSize_5022_);
lean_dec_ref(v_readSize_5022_);
v_res_5029_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4(v___x_5017_, v_a_2587__boxed_5027_, v_connectionContext_5019_, v_recvSelector_5020_, v_socket_5021_, v_readSize_boxed_5028_, v___f_5023_, v___x_5024_, v_x_5025_);
lean_dec(v___x_5017_);
return v_res_5029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6(lean_object* v___f_5030_, lean_object* v_x_5031_, lean_object* v_____s_5032_){
_start:
{
lean_object* v___x_5034_; uint8_t v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
v___x_5034_ = lean_unsigned_to_nat(0u);
v___x_5035_ = 0;
v___x_5036_ = lean_io_mono_ms_now();
v___x_5037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5036_);
v___x_5038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5037_);
v___x_5039_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5034_, v___x_5035_, v___x_5038_, v___f_5030_);
return v___x_5039_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6___boxed(lean_object* v___f_5040_, lean_object* v_x_5041_, lean_object* v_____s_5042_, lean_object* v___y_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6(v___f_5040_, v_x_5041_, v_____s_5042_);
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7(lean_object* v_a_5045_, lean_object* v_x_5046_){
_start:
{
if (lean_obj_tag(v_x_5046_) == 0)
{
lean_object* v___x_5048_; 
v___x_5048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5048_, 0, v_x_5046_);
return v___x_5048_;
}
else
{
lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5056_; 
v_isSharedCheck_5056_ = !lean_is_exclusive(v_x_5046_);
if (v_isSharedCheck_5056_ == 0)
{
lean_object* v_unused_5057_; 
v_unused_5057_ = lean_ctor_get(v_x_5046_, 0);
lean_dec(v_unused_5057_);
v___x_5050_ = v_x_5046_;
v_isShared_5051_ = v_isSharedCheck_5056_;
goto v_resetjp_5049_;
}
else
{
lean_dec(v_x_5046_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5056_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5052_; lean_object* v___x_5054_; 
v___x_5052_ = l_IO_Promise_result_x21___redArg(v_a_5045_);
if (v_isShared_5051_ == 0)
{
lean_ctor_set(v___x_5050_, 0, v___x_5052_);
v___x_5054_ = v___x_5050_;
goto v_reusejp_5053_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v___x_5052_);
v___x_5054_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5053_;
}
v_reusejp_5053_:
{
return v___x_5054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7___boxed(lean_object* v_a_5058_, lean_object* v_x_5059_, lean_object* v___y_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7(v_a_5058_, v_x_5059_);
lean_dec(v_a_5058_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8(lean_object* v___f_5062_, lean_object* v___x_5063_, lean_object* v___x_5064_, uint8_t v___x_5065_, lean_object* v_x_5066_){
_start:
{
if (lean_obj_tag(v_x_5066_) == 0)
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5076_; 
lean_dec(v___x_5063_);
lean_dec_ref(v___f_5062_);
v_a_5068_ = lean_ctor_get(v_x_5066_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v_x_5066_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5070_ = v_x_5066_;
v_isShared_5071_ = v_isSharedCheck_5076_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v_x_5066_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5076_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
lean_object* v___x_5074_; 
v___x_5074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5074_, 0, v___x_5073_);
return v___x_5074_;
}
}
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5088_; 
v_a_5077_ = lean_ctor_get(v_x_5066_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v_x_5066_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5079_ = v_x_5066_;
v_isShared_5080_ = v_isSharedCheck_5088_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v_x_5066_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5088_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___f_5081_; lean_object* v___x_5082_; lean_object* v___x_5084_; 
lean_inc(v_a_5077_);
v___f_5081_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_5081_, 0, v_a_5077_);
lean_inc(v___x_5063_);
v___x_5082_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_5062_, v___x_5063_, v_a_5077_, v___x_5064_);
if (v_isShared_5080_ == 0)
{
lean_ctor_set(v___x_5079_, 0, v___x_5082_);
v___x_5084_ = v___x_5079_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v___x_5082_);
v___x_5084_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5085_, 0, v___x_5084_);
v___x_5086_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5063_, v___x_5065_, v___x_5085_, v___f_5081_);
return v___x_5086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8___boxed(lean_object* v___f_5089_, lean_object* v___x_5090_, lean_object* v___x_5091_, lean_object* v___x_5092_, lean_object* v_x_5093_, lean_object* v___y_5094_){
_start:
{
uint8_t v___x_2734__boxed_5095_; lean_object* v_res_5096_; 
v___x_2734__boxed_5095_ = lean_unbox(v___x_5092_);
v_res_5096_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8(v___f_5089_, v___x_5090_, v___x_5091_, v___x_2734__boxed_5095_, v_x_5093_);
return v_res_5096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9(lean_object* v_timeout_5099_, uint8_t v_a_5100_, lean_object* v_connectionContext_5101_, lean_object* v_recvSelector_5102_, lean_object* v_socket_5103_, uint64_t v_readSize_5104_, lean_object* v___f_5105_, lean_object* v_x_5106_){
_start:
{
if (lean_obj_tag(v_x_5106_) == 0)
{
lean_object* v_a_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5116_; 
lean_dec_ref(v___f_5105_);
lean_dec(v_socket_5103_);
lean_dec_ref(v_recvSelector_5102_);
lean_dec_ref(v_connectionContext_5101_);
v_a_5108_ = lean_ctor_get(v_x_5106_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v_x_5106_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5110_ = v_x_5106_;
v_isShared_5111_ = v_isSharedCheck_5116_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_a_5108_);
lean_dec(v_x_5106_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5116_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5113_; 
if (v_isShared_5111_ == 0)
{
v___x_5113_ = v___x_5110_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5108_);
v___x_5113_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
lean_object* v___x_5114_; 
v___x_5114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5114_, 0, v___x_5113_);
return v___x_5114_;
}
}
}
else
{
lean_object* v_a_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5140_; 
v_a_5117_ = lean_ctor_get(v_x_5106_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v_x_5106_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5119_ = v_x_5106_;
v_isShared_5120_ = v_isSharedCheck_5140_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_a_5117_);
lean_dec(v_x_5106_);
v___x_5119_ = lean_box(0);
v_isShared_5120_ = v_isSharedCheck_5140_;
goto v_resetjp_5118_;
}
v_resetjp_5118_:
{
lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___f_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___f_5127_; lean_object* v___f_5128_; lean_object* v___x_5129_; uint8_t v___x_5130_; lean_object* v___x_5131_; lean_object* v___f_5132_; lean_object* v___x_5133_; lean_object* v___x_5135_; 
v___x_5121_ = l_Int_toNat(v_timeout_5099_);
v___x_5122_ = lean_nat_add(v_a_5117_, v___x_5121_);
lean_dec(v___x_5121_);
lean_dec(v_a_5117_);
v___x_5123_ = lean_box(0);
v___f_5124_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___closed__0));
v___x_5125_ = lean_box(v_a_5100_);
v___x_5126_ = lean_box_uint64(v_readSize_5104_);
v___f_5127_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_5127_, 0, v___x_5122_);
lean_closure_set(v___f_5127_, 1, v___x_5125_);
lean_closure_set(v___f_5127_, 2, v_connectionContext_5101_);
lean_closure_set(v___f_5127_, 3, v_recvSelector_5102_);
lean_closure_set(v___f_5127_, 4, v_socket_5103_);
lean_closure_set(v___f_5127_, 5, v___x_5126_);
lean_closure_set(v___f_5127_, 6, v___f_5124_);
lean_closure_set(v___f_5127_, 7, v___x_5123_);
v___f_5128_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6___boxed), 4, 1);
lean_closure_set(v___f_5128_, 0, v___f_5127_);
v___x_5129_ = lean_unsigned_to_nat(0u);
v___x_5130_ = 0;
v___x_5131_ = lean_box(v___x_5130_);
v___f_5132_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_5132_, 0, v___f_5128_);
lean_closure_set(v___f_5132_, 1, v___x_5129_);
lean_closure_set(v___f_5132_, 2, v___x_5123_);
lean_closure_set(v___f_5132_, 3, v___x_5131_);
v___x_5133_ = lean_io_promise_new();
if (v_isShared_5120_ == 0)
{
lean_ctor_set(v___x_5119_, 0, v___x_5133_);
v___x_5135_ = v___x_5119_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v___x_5133_);
v___x_5135_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; 
v___x_5136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5136_, 0, v___x_5135_);
v___x_5137_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5129_, v___x_5130_, v___x_5136_, v___f_5132_);
v___x_5138_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5129_, v___x_5130_, v___x_5137_, v___f_5105_);
return v___x_5138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___boxed(lean_object* v_timeout_5141_, lean_object* v_a_5142_, lean_object* v_connectionContext_5143_, lean_object* v_recvSelector_5144_, lean_object* v_socket_5145_, lean_object* v_readSize_5146_, lean_object* v___f_5147_, lean_object* v_x_5148_, lean_object* v___y_5149_){
_start:
{
uint8_t v_a_2795__boxed_5150_; uint64_t v_readSize_boxed_5151_; lean_object* v_res_5152_; 
v_a_2795__boxed_5150_ = lean_unbox(v_a_5142_);
v_readSize_boxed_5151_ = lean_unbox_uint64(v_readSize_5146_);
lean_dec_ref(v_readSize_5146_);
v_res_5152_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9(v_timeout_5141_, v_a_2795__boxed_5150_, v_connectionContext_5143_, v_recvSelector_5144_, v_socket_5145_, v_readSize_boxed_5151_, v___f_5147_, v_x_5148_);
lean_dec(v_timeout_5141_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10(lean_object* v_timeout_5153_, lean_object* v_connectionContext_5154_, lean_object* v_recvSelector_5155_, lean_object* v_socket_5156_, uint64_t v_readSize_5157_, lean_object* v___f_5158_, lean_object* v_x_5159_){
_start:
{
if (lean_obj_tag(v_x_5159_) == 0)
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5169_; 
lean_dec_ref(v___f_5158_);
lean_dec(v_socket_5156_);
lean_dec_ref(v_recvSelector_5155_);
lean_dec_ref(v_connectionContext_5154_);
lean_dec(v_timeout_5153_);
v_a_5161_ = lean_ctor_get(v_x_5159_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v_x_5159_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5163_ = v_x_5159_;
v_isShared_5164_ = v_isSharedCheck_5169_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v_x_5159_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5169_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5166_; 
if (v_isShared_5164_ == 0)
{
v___x_5166_ = v___x_5163_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5161_);
v___x_5166_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
lean_object* v___x_5167_; 
v___x_5167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5167_, 0, v___x_5166_);
return v___x_5167_;
}
}
}
else
{
lean_object* v_a_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5186_; 
v_a_5170_ = lean_ctor_get(v_x_5159_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v_x_5159_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5172_ = v_x_5159_;
v_isShared_5173_ = v_isSharedCheck_5186_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_a_5170_);
lean_dec(v_x_5159_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5186_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
uint8_t v___x_5174_; 
v___x_5174_ = lean_unbox(v_a_5170_);
if (v___x_5174_ == 0)
{
lean_object* v___x_5175_; 
lean_del_object(v___x_5172_);
lean_dec(v_a_5170_);
lean_dec_ref(v___f_5158_);
lean_dec(v_socket_5156_);
lean_dec_ref(v_recvSelector_5155_);
lean_dec_ref(v_connectionContext_5154_);
lean_dec(v_timeout_5153_);
v___x_5175_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_5175_;
}
else
{
lean_object* v___x_5176_; lean_object* v___f_5177_; lean_object* v___x_5178_; uint8_t v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5182_; 
v___x_5176_ = lean_box_uint64(v_readSize_5157_);
v___f_5177_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___boxed), 9, 7);
lean_closure_set(v___f_5177_, 0, v_timeout_5153_);
lean_closure_set(v___f_5177_, 1, v_a_5170_);
lean_closure_set(v___f_5177_, 2, v_connectionContext_5154_);
lean_closure_set(v___f_5177_, 3, v_recvSelector_5155_);
lean_closure_set(v___f_5177_, 4, v_socket_5156_);
lean_closure_set(v___f_5177_, 5, v___x_5176_);
lean_closure_set(v___f_5177_, 6, v___f_5158_);
v___x_5178_ = lean_unsigned_to_nat(0u);
v___x_5179_ = 0;
v___x_5180_ = lean_io_mono_ms_now();
if (v_isShared_5173_ == 0)
{
lean_ctor_set(v___x_5172_, 0, v___x_5180_);
v___x_5182_ = v___x_5172_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v___x_5180_);
v___x_5182_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; 
v___x_5183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5183_, 0, v___x_5182_);
v___x_5184_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5178_, v___x_5179_, v___x_5183_, v___f_5177_);
return v___x_5184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10___boxed(lean_object* v_timeout_5187_, lean_object* v_connectionContext_5188_, lean_object* v_recvSelector_5189_, lean_object* v_socket_5190_, lean_object* v_readSize_5191_, lean_object* v___f_5192_, lean_object* v_x_5193_, lean_object* v___y_5194_){
_start:
{
uint64_t v_readSize_boxed_5195_; lean_object* v_res_5196_; 
v_readSize_boxed_5195_ = lean_unbox_uint64(v_readSize_5191_);
lean_dec_ref(v_readSize_5191_);
v_res_5196_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10(v_timeout_5187_, v_connectionContext_5188_, v_recvSelector_5189_, v_socket_5190_, v_readSize_boxed_5195_, v___f_5192_, v_x_5193_);
return v_res_5196_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11(lean_object* v_x_5202_){
_start:
{
if (lean_obj_tag(v_x_5202_) == 0)
{
lean_object* v___x_5204_; 
lean_dec_ref_known(v_x_5202_, 1);
v___x_5204_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___closed__1));
return v___x_5204_;
}
else
{
lean_object* v___x_5205_; 
v___x_5205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5205_, 0, v_x_5202_);
return v___x_5205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___boxed(lean_object* v_x_5206_, lean_object* v___y_5207_){
_start:
{
lean_object* v_res_5208_; 
v_res_5208_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11(v_x_5206_);
return v_res_5208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(lean_object* v_inst_5211_, lean_object* v_socket_5212_, lean_object* v_timeout_5213_, uint64_t v_readSize_5214_, lean_object* v_connectionContext_5215_){
_start:
{
lean_object* v_recvSelector_5217_; lean_object* v_shutdown_5218_; lean_object* v___f_5219_; lean_object* v___x_5220_; lean_object* v___f_5221_; lean_object* v___f_5222_; lean_object* v___x_5223_; uint8_t v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; 
v_recvSelector_5217_ = lean_ctor_get(v_inst_5211_, 2);
lean_inc_ref(v_recvSelector_5217_);
v_shutdown_5218_ = lean_ctor_get(v_inst_5211_, 4);
lean_inc_ref(v_shutdown_5218_);
lean_dec_ref(v_inst_5211_);
v___f_5219_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___closed__0));
v___x_5220_ = lean_box_uint64(v_readSize_5214_);
lean_inc(v_socket_5212_);
v___f_5221_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_5221_, 0, v_timeout_5213_);
lean_closure_set(v___f_5221_, 1, v_connectionContext_5215_);
lean_closure_set(v___f_5221_, 2, v_recvSelector_5217_);
lean_closure_set(v___f_5221_, 3, v_socket_5212_);
lean_closure_set(v___f_5221_, 4, v___x_5220_);
lean_closure_set(v___f_5221_, 5, v___f_5219_);
v___f_5222_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___closed__1));
v___x_5223_ = lean_unsigned_to_nat(0u);
v___x_5224_ = 0;
v___x_5225_ = lean_apply_2(v_shutdown_5218_, v_socket_5212_, lean_box(0));
v___x_5226_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5223_, v___x_5224_, v___x_5225_, v___f_5222_);
v___x_5227_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5223_, v___x_5224_, v___x_5226_, v___f_5221_);
return v___x_5227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___boxed(lean_object* v_inst_5228_, lean_object* v_socket_5229_, lean_object* v_timeout_5230_, lean_object* v_readSize_5231_, lean_object* v_connectionContext_5232_, lean_object* v_a_5233_){
_start:
{
uint64_t v_readSize_boxed_5234_; lean_object* v_res_5235_; 
v_readSize_boxed_5234_ = lean_unbox_uint64(v_readSize_5231_);
lean_dec_ref(v_readSize_5231_);
v_res_5235_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(v_inst_5228_, v_socket_5229_, v_timeout_5230_, v_readSize_boxed_5234_, v_connectionContext_5232_);
return v_res_5235_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger(lean_object* v_00_u03b1_5236_, lean_object* v_inst_5237_, lean_object* v_socket_5238_, lean_object* v_timeout_5239_, uint64_t v_readSize_5240_, lean_object* v_connectionContext_5241_){
_start:
{
lean_object* v___x_5243_; 
v___x_5243_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(v_inst_5237_, v_socket_5238_, v_timeout_5239_, v_readSize_5240_, v_connectionContext_5241_);
return v___x_5243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___boxed(lean_object* v_00_u03b1_5244_, lean_object* v_inst_5245_, lean_object* v_socket_5246_, lean_object* v_timeout_5247_, lean_object* v_readSize_5248_, lean_object* v_connectionContext_5249_, lean_object* v_a_5250_){
_start:
{
uint64_t v_readSize_boxed_5251_; lean_object* v_res_5252_; 
v_readSize_boxed_5251_ = lean_unbox_uint64(v_readSize_5248_);
lean_dec_ref(v_readSize_5248_);
v_res_5252_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger(v_00_u03b1_5244_, v_inst_5245_, v_socket_5246_, v_timeout_5247_, v_readSize_boxed_5251_, v_connectionContext_5249_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_5253_){
_start:
{
if (lean_obj_tag(v_x_5253_) == 0)
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5263_; 
v_a_5255_ = lean_ctor_get(v_x_5253_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v_x_5253_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5257_ = v_x_5253_;
v_isShared_5258_ = v_isSharedCheck_5263_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v_x_5253_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5263_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v___x_5260_; 
if (v_isShared_5258_ == 0)
{
v___x_5260_ = v___x_5257_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5262_; 
v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5255_);
v___x_5260_ = v_reuseFailAlloc_5262_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
lean_object* v___x_5261_; 
v___x_5261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5261_, 0, v___x_5260_);
return v___x_5261_;
}
}
}
else
{
lean_object* v_a_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5282_; 
v_a_5264_ = lean_ctor_get(v_x_5253_, 0);
v_isSharedCheck_5282_ = !lean_is_exclusive(v_x_5253_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5266_ = v_x_5253_;
v_isShared_5267_ = v_isSharedCheck_5282_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_a_5264_);
lean_dec(v_x_5253_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5282_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
lean_object* v_snd_5268_; uint8_t v___x_5269_; 
v_snd_5268_ = lean_ctor_get(v_a_5264_, 1);
v___x_5269_ = lean_unbox(v_snd_5268_);
if (v___x_5269_ == 0)
{
lean_object* v_fst_5270_; lean_object* v___x_5271_; lean_object* v___x_5273_; 
v_fst_5270_ = lean_ctor_get(v_a_5264_, 0);
lean_inc(v_fst_5270_);
lean_dec(v_a_5264_);
v___x_5271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5271_, 0, v_fst_5270_);
if (v_isShared_5267_ == 0)
{
lean_ctor_set(v___x_5266_, 0, v___x_5271_);
v___x_5273_ = v___x_5266_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v___x_5271_);
v___x_5273_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
lean_object* v___x_5274_; 
v___x_5274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5274_, 0, v___x_5273_);
return v___x_5274_;
}
}
else
{
lean_object* v_fst_5276_; lean_object* v___x_5277_; lean_object* v___x_5279_; 
v_fst_5276_ = lean_ctor_get(v_a_5264_, 0);
lean_inc(v_fst_5276_);
lean_dec(v_a_5264_);
v___x_5277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5277_, 0, v_fst_5276_);
if (v_isShared_5267_ == 0)
{
lean_ctor_set(v___x_5266_, 0, v___x_5277_);
v___x_5279_ = v___x_5266_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v___x_5277_);
v___x_5279_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
lean_object* v___x_5280_; 
v___x_5280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5279_);
return v___x_5280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_5283_, lean_object* v___y_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_5283_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_5286_){
_start:
{
lean_object* v_fst_5287_; 
v_fst_5287_ = lean_ctor_get(v_x_5286_, 0);
lean_inc(v_fst_5287_);
return v_fst_5287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_5288_){
_start:
{
lean_object* v_res_5289_; 
v_res_5289_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_5288_);
lean_dec_ref(v_x_5288_);
return v_res_5289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_responseBodyInstance_5290_, lean_object* v_____do__lift_5291_){
_start:
{
if (lean_obj_tag(v_____do__lift_5291_) == 1)
{
lean_object* v_a_5293_; lean_object* v_close_5294_; lean_object* v_body_5295_; lean_object* v___x_5296_; 
v_a_5293_ = lean_ctor_get(v_____do__lift_5291_, 0);
lean_inc(v_a_5293_);
lean_dec_ref_known(v_____do__lift_5291_, 1);
v_close_5294_ = lean_ctor_get(v_responseBodyInstance_5290_, 1);
lean_inc_ref(v_close_5294_);
lean_dec_ref(v_responseBodyInstance_5290_);
v_body_5295_ = lean_ctor_get(v_a_5293_, 1);
lean_inc(v_body_5295_);
lean_dec(v_a_5293_);
v___x_5296_ = lean_apply_2(v_close_5294_, v_body_5295_, lean_box(0));
return v___x_5296_;
}
else
{
lean_object* v___x_5297_; 
lean_dec_ref(v_____do__lift_5291_);
lean_dec_ref(v_responseBodyInstance_5290_);
v___x_5297_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_5297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_responseBodyInstance_5298_, lean_object* v_____do__lift_5299_, lean_object* v___y_5300_){
_start:
{
lean_object* v_res_5301_; 
v_res_5301_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_responseBodyInstance_5298_, v_____do__lift_5299_);
return v_res_5301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v___x_5302_, lean_object* v_x_5303_){
_start:
{
if (lean_obj_tag(v_x_5303_) == 0)
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5313_; 
lean_dec_ref(v___x_5302_);
v_a_5305_ = lean_ctor_get(v_x_5303_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v_x_5303_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5307_ = v_x_5303_;
v_isShared_5308_ = v_isSharedCheck_5313_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v_x_5303_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5313_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5310_; 
if (v_isShared_5308_ == 0)
{
v___x_5310_ = v___x_5307_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v_a_5305_);
v___x_5310_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
lean_object* v___x_5311_; 
v___x_5311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5311_, 0, v___x_5310_);
return v___x_5311_;
}
}
}
else
{
lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5322_; 
v_isSharedCheck_5322_ = !lean_is_exclusive(v_x_5303_);
if (v_isSharedCheck_5322_ == 0)
{
lean_object* v_unused_5323_; 
v_unused_5323_ = lean_ctor_get(v_x_5303_, 0);
lean_dec(v_unused_5323_);
v___x_5315_ = v_x_5303_;
v_isShared_5316_ = v_isSharedCheck_5322_;
goto v_resetjp_5314_;
}
else
{
lean_dec(v_x_5303_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5322_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
lean_object* v___x_5317_; lean_object* v___x_5319_; 
v___x_5317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5317_, 0, v___x_5302_);
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 0, v___x_5317_);
v___x_5319_ = v___x_5315_;
goto v_reusejp_5318_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v___x_5317_);
v___x_5319_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5318_;
}
v_reusejp_5318_:
{
lean_object* v___x_5320_; 
v___x_5320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5320_, 0, v___x_5319_);
return v___x_5320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object* v___x_5324_, lean_object* v_x_5325_, lean_object* v___y_5326_){
_start:
{
lean_object* v_res_5327_; 
v_res_5327_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v___x_5324_, v_x_5325_);
return v_res_5327_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_h_5328_, lean_object* v_responseBodyInstance_5329_, lean_object* v_handler_5330_, lean_object* v_config_5331_, lean_object* v_a_5332_, lean_object* v___f_5333_, lean_object* v_____r_5334_, lean_object* v_state_5335_){
_start:
{
lean_object* v___x_5337_; uint8_t v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; 
v___x_5337_ = lean_unsigned_to_nat(0u);
v___x_5338_ = 0;
v___x_5339_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_5328_, v_responseBodyInstance_5329_, v_handler_5330_, v_config_5331_, v_a_5332_, v_state_5335_);
v___x_5340_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5337_, v___x_5338_, v___x_5339_, v___f_5333_);
return v___x_5340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_h_5341_, lean_object* v_responseBodyInstance_5342_, lean_object* v_handler_5343_, lean_object* v_config_5344_, lean_object* v_a_5345_, lean_object* v___f_5346_, lean_object* v_____r_5347_, lean_object* v_state_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_h_5341_, v_responseBodyInstance_5342_, v_handler_5343_, v_config_5344_, v_a_5345_, v___f_5346_, v_____r_5347_, v_state_5348_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_a_5351_, lean_object* v___f_5352_, lean_object* v_keepAliveTimeout_5353_, lean_object* v___f_5354_, lean_object* v___x_5355_, lean_object* v_machine_5356_, lean_object* v_requestStream_5357_, lean_object* v_response_5358_, lean_object* v_respStream_5359_, lean_object* v___x_5360_, lean_object* v_handler_5361_, lean_object* v_pendingHead_5362_, lean_object* v_dateSecond_5363_, uint8_t v_requestEnded_5364_, lean_object* v_x_5365_){
_start:
{
if (lean_obj_tag(v_x_5365_) == 0)
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5375_; 
lean_dec(v_dateSecond_5363_);
lean_dec(v_pendingHead_5362_);
lean_dec(v_handler_5361_);
lean_dec(v___x_5360_);
lean_dec(v_respStream_5359_);
lean_dec_ref(v_response_5358_);
lean_dec_ref(v_requestStream_5357_);
lean_dec_ref(v_machine_5356_);
lean_dec_ref(v___x_5355_);
lean_dec_ref(v___f_5354_);
lean_dec_ref(v___f_5352_);
lean_dec_ref(v_a_5351_);
v_a_5367_ = lean_ctor_get(v_x_5365_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v_x_5365_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5369_ = v_x_5365_;
v_isShared_5370_ = v_isSharedCheck_5375_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v_x_5365_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5375_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5367_);
v___x_5372_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
lean_object* v___x_5373_; 
v___x_5373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5373_, 0, v___x_5372_);
return v___x_5373_;
}
}
}
else
{
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5404_; 
v_a_5376_ = lean_ctor_get(v_x_5365_, 0);
v_isSharedCheck_5404_ = !lean_is_exclusive(v_x_5365_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5378_ = v_x_5365_;
v_isShared_5379_ = v_isSharedCheck_5404_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v_x_5365_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5404_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
if (lean_obj_tag(v_a_5376_) == 0)
{
lean_object* v___x_5380_; uint8_t v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; 
lean_del_object(v___x_5378_);
lean_dec(v_dateSecond_5363_);
lean_dec(v_pendingHead_5362_);
lean_dec(v_handler_5361_);
lean_dec(v___x_5360_);
lean_dec(v_respStream_5359_);
lean_dec_ref(v_response_5358_);
lean_dec_ref(v_requestStream_5357_);
lean_dec_ref(v_machine_5356_);
lean_dec_ref(v___x_5355_);
lean_dec_ref(v___f_5354_);
v___x_5380_ = lean_unsigned_to_nat(0u);
v___x_5381_ = 0;
v___x_5382_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_a_5351_);
v___x_5383_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5380_, v___x_5381_, v___x_5382_, v___f_5352_);
return v___x_5383_;
}
else
{
lean_object* v_val_5384_; lean_object* v___x_5386_; uint8_t v_isShared_5387_; uint8_t v_isSharedCheck_5403_; 
lean_dec_ref(v___f_5352_);
lean_dec_ref(v_a_5351_);
v_val_5384_ = lean_ctor_get(v_a_5376_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v_a_5376_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5386_ = v_a_5376_;
v_isShared_5387_ = v_isSharedCheck_5403_;
goto v_resetjp_5385_;
}
else
{
lean_inc(v_val_5384_);
lean_dec(v_a_5376_);
v___x_5386_ = lean_box(0);
v_isShared_5387_ = v_isSharedCheck_5403_;
goto v_resetjp_5385_;
}
v_resetjp_5385_:
{
lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; uint8_t v___x_5391_; 
v___x_5388_ = lean_nat_to_int(v_val_5384_);
v___x_5389_ = lean_int_sub(v_keepAliveTimeout_5353_, v___x_5388_);
lean_dec(v___x_5388_);
v___x_5390_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0);
v___x_5391_ = lean_int_dec_lt(v___x_5390_, v___x_5389_);
if (v___x_5391_ == 0)
{
lean_object* v___x_5392_; lean_object* v___x_5393_; 
lean_dec(v___x_5389_);
lean_del_object(v___x_5386_);
lean_del_object(v___x_5378_);
lean_dec(v_dateSecond_5363_);
lean_dec(v_pendingHead_5362_);
lean_dec(v_handler_5361_);
lean_dec(v___x_5360_);
lean_dec(v_respStream_5359_);
lean_dec_ref(v_response_5358_);
lean_dec_ref(v_requestStream_5357_);
lean_dec_ref(v_machine_5356_);
v___x_5392_ = lean_box(0);
v___x_5393_ = lean_apply_3(v___f_5354_, v___x_5392_, v___x_5355_, lean_box(0));
return v___x_5393_;
}
else
{
lean_object* v___x_5395_; 
lean_dec_ref(v___x_5355_);
lean_dec_ref(v___f_5354_);
if (v_isShared_5387_ == 0)
{
lean_ctor_set_tag(v___x_5386_, 0);
lean_ctor_set(v___x_5386_, 0, v___x_5389_);
v___x_5395_ = v___x_5386_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v___x_5389_);
v___x_5395_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5399_; 
v___x_5396_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_5396_, 0, v_machine_5356_);
lean_ctor_set(v___x_5396_, 1, v_requestStream_5357_);
lean_ctor_set(v___x_5396_, 2, v___x_5395_);
lean_ctor_set(v___x_5396_, 3, v_response_5358_);
lean_ctor_set(v___x_5396_, 4, v_respStream_5359_);
lean_ctor_set(v___x_5396_, 5, v___x_5360_);
lean_ctor_set(v___x_5396_, 6, v_handler_5361_);
lean_ctor_set(v___x_5396_, 7, v_pendingHead_5362_);
lean_ctor_set(v___x_5396_, 8, v_dateSecond_5363_);
lean_ctor_set_uint8(v___x_5396_, sizeof(void*)*9, v_requestEnded_5364_);
v___x_5397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5397_, 0, v___x_5396_);
if (v_isShared_5379_ == 0)
{
lean_ctor_set(v___x_5378_, 0, v___x_5397_);
v___x_5399_ = v___x_5378_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5397_);
v___x_5399_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
lean_object* v___x_5400_; 
v___x_5400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5400_, 0, v___x_5399_);
return v___x_5400_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_a_5405_, lean_object* v___f_5406_, lean_object* v_keepAliveTimeout_5407_, lean_object* v___f_5408_, lean_object* v___x_5409_, lean_object* v_machine_5410_, lean_object* v_requestStream_5411_, lean_object* v_response_5412_, lean_object* v_respStream_5413_, lean_object* v___x_5414_, lean_object* v_handler_5415_, lean_object* v_pendingHead_5416_, lean_object* v_dateSecond_5417_, lean_object* v_requestEnded_5418_, lean_object* v_x_5419_, lean_object* v___y_5420_){
_start:
{
uint8_t v_requestEnded_boxed_5421_; lean_object* v_res_5422_; 
v_requestEnded_boxed_5421_ = lean_unbox(v_requestEnded_5418_);
v_res_5422_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_a_5405_, v___f_5406_, v_keepAliveTimeout_5407_, v___f_5408_, v___x_5409_, v_machine_5410_, v_requestStream_5411_, v_response_5412_, v_respStream_5413_, v___x_5414_, v_handler_5415_, v_pendingHead_5416_, v_dateSecond_5417_, v_requestEnded_boxed_5421_, v_x_5419_);
lean_dec(v_keepAliveTimeout_5407_);
return v_res_5422_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v_h_5423_, lean_object* v_responseBodyInstance_5424_, lean_object* v_handler_5425_, lean_object* v_config_5426_, lean_object* v___f_5427_, lean_object* v_a_5428_, lean_object* v___f_5429_, lean_object* v_keepAliveTimeout_5430_, lean_object* v___x_5431_, lean_object* v_machine_5432_, lean_object* v_requestStream_5433_, lean_object* v_response_5434_, lean_object* v_respStream_5435_, lean_object* v___x_5436_, lean_object* v_handler_5437_, lean_object* v_pendingHead_5438_, lean_object* v_dateSecond_5439_, uint8_t v_requestEnded_5440_, lean_object* v_x_5441_){
_start:
{
if (lean_obj_tag(v_x_5441_) == 0)
{
lean_object* v_a_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5451_; 
lean_dec(v_dateSecond_5439_);
lean_dec(v_pendingHead_5438_);
lean_dec(v_handler_5437_);
lean_dec(v___x_5436_);
lean_dec(v_respStream_5435_);
lean_dec_ref(v_response_5434_);
lean_dec_ref(v_requestStream_5433_);
lean_dec_ref(v_machine_5432_);
lean_dec_ref(v___x_5431_);
lean_dec(v_keepAliveTimeout_5430_);
lean_dec_ref(v___f_5429_);
lean_dec_ref(v_a_5428_);
lean_dec_ref(v___f_5427_);
lean_dec_ref(v_config_5426_);
lean_dec(v_handler_5425_);
lean_dec_ref(v_responseBodyInstance_5424_);
lean_dec_ref(v_h_5423_);
v_a_5443_ = lean_ctor_get(v_x_5441_, 0);
v_isSharedCheck_5451_ = !lean_is_exclusive(v_x_5441_);
if (v_isSharedCheck_5451_ == 0)
{
v___x_5445_ = v_x_5441_;
v_isShared_5446_ = v_isSharedCheck_5451_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_a_5443_);
lean_dec(v_x_5441_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5451_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
lean_object* v___x_5448_; 
if (v_isShared_5446_ == 0)
{
v___x_5448_ = v___x_5445_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v_a_5443_);
v___x_5448_ = v_reuseFailAlloc_5450_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
lean_object* v___x_5449_; 
v___x_5449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5449_, 0, v___x_5448_);
return v___x_5449_;
}
}
}
else
{
lean_object* v_a_5452_; lean_object* v___x_5454_; uint8_t v_isShared_5455_; uint8_t v_isSharedCheck_5469_; 
v_a_5452_ = lean_ctor_get(v_x_5441_, 0);
v_isSharedCheck_5469_ = !lean_is_exclusive(v_x_5441_);
if (v_isSharedCheck_5469_ == 0)
{
v___x_5454_ = v_x_5441_;
v_isShared_5455_ = v_isSharedCheck_5469_;
goto v_resetjp_5453_;
}
else
{
lean_inc(v_a_5452_);
lean_dec(v_x_5441_);
v___x_5454_ = lean_box(0);
v_isShared_5455_ = v_isSharedCheck_5469_;
goto v_resetjp_5453_;
}
v_resetjp_5453_:
{
lean_object* v___f_5456_; 
lean_inc_ref(v___f_5427_);
lean_inc(v_a_5452_);
lean_inc_ref(v_config_5426_);
lean_inc(v_handler_5425_);
lean_inc_ref(v_responseBodyInstance_5424_);
lean_inc_ref(v_h_5423_);
v___f_5456_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 9, 6);
lean_closure_set(v___f_5456_, 0, v_h_5423_);
lean_closure_set(v___f_5456_, 1, v_responseBodyInstance_5424_);
lean_closure_set(v___f_5456_, 2, v_handler_5425_);
lean_closure_set(v___f_5456_, 3, v_config_5426_);
lean_closure_set(v___f_5456_, 4, v_a_5452_);
lean_closure_set(v___f_5456_, 5, v___f_5427_);
if (lean_obj_tag(v_a_5452_) == 5)
{
lean_object* v___x_5457_; lean_object* v___f_5458_; lean_object* v___x_5459_; uint8_t v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5463_; 
lean_dec_ref(v___f_5427_);
lean_dec_ref(v_config_5426_);
lean_dec(v_handler_5425_);
lean_dec_ref(v_responseBodyInstance_5424_);
lean_dec_ref(v_h_5423_);
v___x_5457_ = lean_box(v_requestEnded_5440_);
lean_inc_ref(v_a_5428_);
v___f_5458_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 16, 14);
lean_closure_set(v___f_5458_, 0, v_a_5428_);
lean_closure_set(v___f_5458_, 1, v___f_5429_);
lean_closure_set(v___f_5458_, 2, v_keepAliveTimeout_5430_);
lean_closure_set(v___f_5458_, 3, v___f_5456_);
lean_closure_set(v___f_5458_, 4, v___x_5431_);
lean_closure_set(v___f_5458_, 5, v_machine_5432_);
lean_closure_set(v___f_5458_, 6, v_requestStream_5433_);
lean_closure_set(v___f_5458_, 7, v_response_5434_);
lean_closure_set(v___f_5458_, 8, v_respStream_5435_);
lean_closure_set(v___f_5458_, 9, v___x_5436_);
lean_closure_set(v___f_5458_, 10, v_handler_5437_);
lean_closure_set(v___f_5458_, 11, v_pendingHead_5438_);
lean_closure_set(v___f_5458_, 12, v_dateSecond_5439_);
lean_closure_set(v___f_5458_, 13, v___x_5457_);
v___x_5459_ = lean_unsigned_to_nat(0u);
v___x_5460_ = 0;
v___x_5461_ = l_Std_Http_Internal_Outbox_idleFor_x3f___redArg(v_a_5428_);
lean_dec_ref(v_a_5428_);
if (v_isShared_5455_ == 0)
{
lean_ctor_set(v___x_5454_, 0, v___x_5461_);
v___x_5463_ = v___x_5454_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v___x_5461_);
v___x_5463_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
lean_object* v___x_5464_; lean_object* v___x_5465_; 
v___x_5464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5464_, 0, v___x_5463_);
v___x_5465_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5459_, v___x_5460_, v___x_5464_, v___f_5458_);
return v___x_5465_;
}
}
else
{
lean_object* v___x_5467_; lean_object* v___x_5468_; 
lean_dec_ref(v___f_5456_);
lean_del_object(v___x_5454_);
lean_dec(v_dateSecond_5439_);
lean_dec(v_pendingHead_5438_);
lean_dec(v_handler_5437_);
lean_dec(v___x_5436_);
lean_dec(v_respStream_5435_);
lean_dec_ref(v_response_5434_);
lean_dec_ref(v_requestStream_5433_);
lean_dec_ref(v_machine_5432_);
lean_dec(v_keepAliveTimeout_5430_);
lean_dec_ref(v___f_5429_);
lean_dec_ref(v_a_5428_);
v___x_5467_ = lean_box(0);
v___x_5468_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_h_5423_, v_responseBodyInstance_5424_, v_handler_5425_, v_config_5426_, v_a_5452_, v___f_5427_, v___x_5467_, v___x_5431_);
return v___x_5468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_h_5470_ = _args[0];
lean_object* v_responseBodyInstance_5471_ = _args[1];
lean_object* v_handler_5472_ = _args[2];
lean_object* v_config_5473_ = _args[3];
lean_object* v___f_5474_ = _args[4];
lean_object* v_a_5475_ = _args[5];
lean_object* v___f_5476_ = _args[6];
lean_object* v_keepAliveTimeout_5477_ = _args[7];
lean_object* v___x_5478_ = _args[8];
lean_object* v_machine_5479_ = _args[9];
lean_object* v_requestStream_5480_ = _args[10];
lean_object* v_response_5481_ = _args[11];
lean_object* v_respStream_5482_ = _args[12];
lean_object* v___x_5483_ = _args[13];
lean_object* v_handler_5484_ = _args[14];
lean_object* v_pendingHead_5485_ = _args[15];
lean_object* v_dateSecond_5486_ = _args[16];
lean_object* v_requestEnded_5487_ = _args[17];
lean_object* v_x_5488_ = _args[18];
lean_object* v___y_5489_ = _args[19];
_start:
{
uint8_t v_requestEnded_boxed_5490_; lean_object* v_res_5491_; 
v_requestEnded_boxed_5490_ = lean_unbox(v_requestEnded_5487_);
v_res_5491_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v_h_5470_, v_responseBodyInstance_5471_, v_handler_5472_, v_config_5473_, v___f_5474_, v_a_5475_, v___f_5476_, v_keepAliveTimeout_5477_, v___x_5478_, v_machine_5479_, v_requestStream_5480_, v_response_5481_, v_respStream_5482_, v___x_5483_, v_handler_5484_, v_pendingHead_5485_, v_dateSecond_5486_, v_requestEnded_boxed_5490_, v_x_5488_);
return v_res_5491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(lean_object* v_inst_5492_, lean_object* v_h_5493_, lean_object* v_responseBodyInstance_5494_, lean_object* v_config_5495_, lean_object* v_handler_5496_, lean_object* v___f_5497_, lean_object* v_x_5498_){
_start:
{
if (lean_obj_tag(v_x_5498_) == 0)
{
lean_object* v_a_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5508_; 
lean_dec_ref(v___f_5497_);
lean_dec(v_handler_5496_);
lean_dec_ref(v_config_5495_);
lean_dec_ref(v_responseBodyInstance_5494_);
lean_dec_ref(v_h_5493_);
lean_dec_ref(v_inst_5492_);
v_a_5500_ = lean_ctor_get(v_x_5498_, 0);
v_isSharedCheck_5508_ = !lean_is_exclusive(v_x_5498_);
if (v_isSharedCheck_5508_ == 0)
{
v___x_5502_ = v_x_5498_;
v_isShared_5503_ = v_isSharedCheck_5508_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_a_5500_);
lean_dec(v_x_5498_);
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5508_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v___x_5505_; 
if (v_isShared_5503_ == 0)
{
v___x_5505_ = v___x_5502_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5507_; 
v_reuseFailAlloc_5507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5507_, 0, v_a_5500_);
v___x_5505_ = v_reuseFailAlloc_5507_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
lean_object* v___x_5506_; 
v___x_5506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5506_, 0, v___x_5505_);
return v___x_5506_;
}
}
}
else
{
lean_object* v_a_5509_; lean_object* v___x_5510_; uint8_t v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; 
v_a_5509_ = lean_ctor_get(v_x_5498_, 0);
lean_inc(v_a_5509_);
lean_dec_ref_known(v_x_5498_, 1);
v___x_5510_ = lean_unsigned_to_nat(0u);
v___x_5511_ = 0;
v___x_5512_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_5492_, v_h_5493_, v_responseBodyInstance_5494_, v_config_5495_, v_handler_5496_, v_a_5509_);
v___x_5513_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5510_, v___x_5511_, v___x_5512_, v___f_5497_);
return v___x_5513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v_inst_5514_, lean_object* v_h_5515_, lean_object* v_responseBodyInstance_5516_, lean_object* v_config_5517_, lean_object* v_handler_5518_, lean_object* v___f_5519_, lean_object* v_x_5520_, lean_object* v___y_5521_){
_start:
{
lean_object* v_res_5522_; 
v_res_5522_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v_inst_5514_, v_h_5515_, v_responseBodyInstance_5516_, v_config_5517_, v_handler_5518_, v___f_5519_, v_x_5520_);
return v_res_5522_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v___x_5523_, lean_object* v_h_5524_, lean_object* v_responseBodyInstance_5525_, lean_object* v_handler_5526_, lean_object* v_config_5527_, lean_object* v___f_5528_, lean_object* v_a_5529_, lean_object* v_keepAliveTimeout_5530_, lean_object* v_inst_5531_, lean_object* v_socket_5532_, lean_object* v_connectionContext_5533_, lean_object* v_maximumRecvSize_5534_, lean_object* v_x_5535_){
_start:
{
if (lean_obj_tag(v_x_5535_) == 0)
{
lean_object* v_a_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5545_; 
lean_dec(v_maximumRecvSize_5534_);
lean_dec_ref(v_connectionContext_5533_);
lean_dec(v_socket_5532_);
lean_dec_ref(v_inst_5531_);
lean_dec(v_keepAliveTimeout_5530_);
lean_dec_ref(v_a_5529_);
lean_dec_ref(v___f_5528_);
lean_dec_ref(v_config_5527_);
lean_dec(v_handler_5526_);
lean_dec_ref(v_responseBodyInstance_5525_);
lean_dec_ref(v_h_5524_);
lean_dec(v___x_5523_);
v_a_5537_ = lean_ctor_get(v_x_5535_, 0);
v_isSharedCheck_5545_ = !lean_is_exclusive(v_x_5535_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5539_ = v_x_5535_;
v_isShared_5540_ = v_isSharedCheck_5545_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_a_5537_);
lean_dec(v_x_5535_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5545_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v___x_5542_; 
if (v_isShared_5540_ == 0)
{
v___x_5542_ = v___x_5539_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_a_5537_);
v___x_5542_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
lean_object* v___x_5543_; 
v___x_5543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5543_, 0, v___x_5542_);
return v___x_5543_;
}
}
}
else
{
lean_object* v_a_5546_; lean_object* v___x_5548_; uint8_t v_isShared_5549_; uint8_t v_isSharedCheck_5589_; 
v_a_5546_ = lean_ctor_get(v_x_5535_, 0);
v_isSharedCheck_5589_ = !lean_is_exclusive(v_x_5535_);
if (v_isSharedCheck_5589_ == 0)
{
v___x_5548_ = v_x_5535_;
v_isShared_5549_ = v_isSharedCheck_5589_;
goto v_resetjp_5547_;
}
else
{
lean_inc(v_a_5546_);
lean_dec(v_x_5535_);
v___x_5548_ = lean_box(0);
v_isShared_5549_ = v_isSharedCheck_5589_;
goto v_resetjp_5547_;
}
v_resetjp_5547_:
{
lean_object* v_machine_5556_; lean_object* v_requestStream_5557_; lean_object* v_timer_5558_; lean_object* v_response_5559_; lean_object* v_respStream_5560_; lean_object* v_inputWanted_5561_; lean_object* v_handler_5562_; lean_object* v_pendingHead_5563_; lean_object* v_dateSecond_5564_; uint8_t v_requestEnded_5565_; uint8_t v___y_5577_; 
v_machine_5556_ = lean_ctor_get(v_a_5546_, 0);
v_requestStream_5557_ = lean_ctor_get(v_a_5546_, 1);
v_timer_5558_ = lean_ctor_get(v_a_5546_, 2);
v_response_5559_ = lean_ctor_get(v_a_5546_, 3);
v_respStream_5560_ = lean_ctor_get(v_a_5546_, 4);
v_inputWanted_5561_ = lean_ctor_get(v_a_5546_, 5);
v_handler_5562_ = lean_ctor_get(v_a_5546_, 6);
v_pendingHead_5563_ = lean_ctor_get(v_a_5546_, 7);
v_dateSecond_5564_ = lean_ctor_get(v_a_5546_, 8);
v_requestEnded_5565_ = lean_ctor_get_uint8(v_a_5546_, sizeof(void*)*9);
if (lean_obj_tag(v_inputWanted_5561_) == 0)
{
uint8_t v___x_5580_; 
v___x_5580_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg(v_handler_5562_);
if (v___x_5580_ == 0)
{
if (lean_obj_tag(v_respStream_5560_) == 0)
{
lean_object* v_writer_5581_; lean_object* v_state_5582_; 
v_writer_5581_ = lean_ctor_get(v_machine_5556_, 1);
v_state_5582_ = lean_ctor_get(v_writer_5581_, 2);
switch(lean_obj_tag(v_state_5582_))
{
case 6:
{
lean_dec(v_maximumRecvSize_5534_);
lean_dec_ref(v_connectionContext_5533_);
lean_dec(v_socket_5532_);
lean_dec_ref(v_inst_5531_);
lean_dec(v_keepAliveTimeout_5530_);
lean_dec_ref(v_a_5529_);
lean_dec_ref(v___f_5528_);
lean_dec_ref(v_config_5527_);
lean_dec(v_handler_5526_);
lean_dec_ref(v_responseBodyInstance_5525_);
lean_dec_ref(v_h_5524_);
lean_dec(v___x_5523_);
goto v___jp_5550_;
}
case 7:
{
lean_dec(v_maximumRecvSize_5534_);
lean_dec_ref(v_connectionContext_5533_);
lean_dec(v_socket_5532_);
lean_dec_ref(v_inst_5531_);
lean_dec(v_keepAliveTimeout_5530_);
lean_dec_ref(v_a_5529_);
lean_dec_ref(v___f_5528_);
lean_dec_ref(v_config_5527_);
lean_dec(v_handler_5526_);
lean_dec_ref(v_responseBodyInstance_5525_);
lean_dec_ref(v_h_5524_);
lean_dec(v___x_5523_);
goto v___jp_5550_;
}
default: 
{
switch(lean_obj_tag(v_state_5582_))
{
case 0:
{
v___y_5577_ = v___x_5580_;
goto v___jp_5576_;
}
case 1:
{
v___y_5577_ = v___x_5580_;
goto v___jp_5576_;
}
default: 
{
lean_object* v_reader_5583_; lean_object* v_state_5584_; 
v_reader_5583_ = lean_ctor_get(v_machine_5556_, 0);
v_state_5584_ = lean_ctor_get(v_reader_5583_, 0);
if (lean_obj_tag(v_state_5584_) == 2)
{
lean_object* v_a_5585_; 
v_a_5585_ = lean_ctor_get(v_state_5584_, 0);
if (lean_obj_tag(v_a_5585_) == 0)
{
lean_object* v_remaining_5586_; lean_object* v___x_5587_; uint8_t v___x_5588_; 
v_remaining_5586_ = lean_ctor_get(v_a_5585_, 0);
v___x_5587_ = lean_unsigned_to_nat(0u);
v___x_5588_ = lean_nat_dec_eq(v_remaining_5586_, v___x_5587_);
if (v___x_5588_ == 0)
{
v___y_5577_ = v___x_5588_;
goto v___jp_5576_;
}
else
{
lean_dec(v_maximumRecvSize_5534_);
lean_dec_ref(v_connectionContext_5533_);
lean_dec(v_socket_5532_);
lean_dec_ref(v_inst_5531_);
lean_dec(v_keepAliveTimeout_5530_);
lean_dec_ref(v_a_5529_);
lean_dec_ref(v___f_5528_);
lean_dec_ref(v_config_5527_);
lean_dec(v_handler_5526_);
lean_dec_ref(v_responseBodyInstance_5525_);
lean_dec_ref(v_h_5524_);
lean_dec(v___x_5523_);
goto v___jp_5550_;
}
}
else
{
v___y_5577_ = v___x_5580_;
goto v___jp_5576_;
}
}
else
{
v___y_5577_ = v___x_5580_;
goto v___jp_5576_;
}
}
}
}
}
}
else
{
lean_inc_ref(v_respStream_5560_);
lean_inc(v_inputWanted_5561_);
lean_inc(v_dateSecond_5564_);
lean_inc(v_pendingHead_5563_);
lean_inc(v_handler_5562_);
lean_inc_ref(v_response_5559_);
lean_inc_ref(v_timer_5558_);
lean_inc_ref(v_requestStream_5557_);
lean_inc_ref(v_machine_5556_);
lean_del_object(v___x_5548_);
lean_dec(v_a_5546_);
goto v___jp_5566_;
}
}
else
{
lean_inc(v_inputWanted_5561_);
lean_inc(v_dateSecond_5564_);
lean_inc(v_pendingHead_5563_);
lean_inc(v_handler_5562_);
lean_inc(v_respStream_5560_);
lean_inc_ref(v_response_5559_);
lean_inc_ref(v_timer_5558_);
lean_inc_ref(v_requestStream_5557_);
lean_inc_ref(v_machine_5556_);
lean_del_object(v___x_5548_);
lean_dec(v_a_5546_);
goto v___jp_5566_;
}
}
else
{
lean_inc_ref(v_inputWanted_5561_);
lean_inc(v_dateSecond_5564_);
lean_inc(v_pendingHead_5563_);
lean_inc(v_handler_5562_);
lean_inc(v_respStream_5560_);
lean_inc_ref(v_response_5559_);
lean_inc_ref(v_timer_5558_);
lean_inc_ref(v_requestStream_5557_);
lean_inc_ref(v_machine_5556_);
lean_del_object(v___x_5548_);
lean_dec(v_a_5546_);
goto v___jp_5566_;
}
v___jp_5550_:
{
lean_object* v___x_5551_; lean_object* v___x_5553_; 
v___x_5551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5551_, 0, v_a_5546_);
if (v_isShared_5549_ == 0)
{
lean_ctor_set(v___x_5548_, 0, v___x_5551_);
v___x_5553_ = v___x_5548_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v___x_5551_);
v___x_5553_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
lean_object* v___x_5554_; 
v___x_5554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5554_, 0, v___x_5553_);
return v___x_5554_;
}
}
v___jp_5566_:
{
lean_object* v___x_5567_; lean_object* v___f_5568_; lean_object* v___x_5569_; lean_object* v___f_5570_; lean_object* v___f_5571_; lean_object* v___x_5572_; uint8_t v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; 
lean_inc(v_dateSecond_5564_);
lean_inc(v_pendingHead_5563_);
lean_inc(v_handler_5562_);
lean_inc(v___x_5523_);
lean_inc(v_respStream_5560_);
lean_inc_ref(v_response_5559_);
lean_inc_ref(v_requestStream_5557_);
lean_inc_ref(v_machine_5556_);
v___x_5567_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_5567_, 0, v_machine_5556_);
lean_ctor_set(v___x_5567_, 1, v_requestStream_5557_);
lean_ctor_set(v___x_5567_, 2, v_timer_5558_);
lean_ctor_set(v___x_5567_, 3, v_response_5559_);
lean_ctor_set(v___x_5567_, 4, v_respStream_5560_);
lean_ctor_set(v___x_5567_, 5, v___x_5523_);
lean_ctor_set(v___x_5567_, 6, v_handler_5562_);
lean_ctor_set(v___x_5567_, 7, v_pendingHead_5563_);
lean_ctor_set(v___x_5567_, 8, v_dateSecond_5564_);
lean_ctor_set_uint8(v___x_5567_, sizeof(void*)*9, v_requestEnded_5565_);
lean_inc_ref_n(v___x_5567_, 2);
v___f_5568_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5568_, 0, v___x_5567_);
v___x_5569_ = lean_box(v_requestEnded_5565_);
lean_inc_ref(v_config_5527_);
lean_inc(v_handler_5526_);
lean_inc_ref(v_responseBodyInstance_5525_);
lean_inc_ref(v_h_5524_);
v___f_5570_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 20, 18);
lean_closure_set(v___f_5570_, 0, v_h_5524_);
lean_closure_set(v___f_5570_, 1, v_responseBodyInstance_5525_);
lean_closure_set(v___f_5570_, 2, v_handler_5526_);
lean_closure_set(v___f_5570_, 3, v_config_5527_);
lean_closure_set(v___f_5570_, 4, v___f_5528_);
lean_closure_set(v___f_5570_, 5, v_a_5529_);
lean_closure_set(v___f_5570_, 6, v___f_5568_);
lean_closure_set(v___f_5570_, 7, v_keepAliveTimeout_5530_);
lean_closure_set(v___f_5570_, 8, v___x_5567_);
lean_closure_set(v___f_5570_, 9, v_machine_5556_);
lean_closure_set(v___f_5570_, 10, v_requestStream_5557_);
lean_closure_set(v___f_5570_, 11, v_response_5559_);
lean_closure_set(v___f_5570_, 12, v_respStream_5560_);
lean_closure_set(v___f_5570_, 13, v___x_5523_);
lean_closure_set(v___f_5570_, 14, v_handler_5562_);
lean_closure_set(v___f_5570_, 15, v_pendingHead_5563_);
lean_closure_set(v___f_5570_, 16, v_dateSecond_5564_);
lean_closure_set(v___f_5570_, 17, v___x_5569_);
v___f_5571_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 8, 6);
lean_closure_set(v___f_5571_, 0, v_inst_5531_);
lean_closure_set(v___f_5571_, 1, v_h_5524_);
lean_closure_set(v___f_5571_, 2, v_responseBodyInstance_5525_);
lean_closure_set(v___f_5571_, 3, v_config_5527_);
lean_closure_set(v___f_5571_, 4, v_handler_5526_);
lean_closure_set(v___f_5571_, 5, v___f_5570_);
v___x_5572_ = lean_unsigned_to_nat(0u);
v___x_5573_ = 0;
v___x_5574_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_5532_, v_connectionContext_5533_, v___x_5567_, v_inputWanted_5561_, v_maximumRecvSize_5534_);
v___x_5575_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5572_, v___x_5573_, v___x_5574_, v___f_5571_);
return v___x_5575_;
}
v___jp_5576_:
{
lean_object* v_reader_5578_; lean_object* v_state_5579_; 
v_reader_5578_ = lean_ctor_get(v_machine_5556_, 0);
v_state_5579_ = lean_ctor_get(v_reader_5578_, 0);
if (lean_obj_tag(v_state_5579_) == 2)
{
lean_inc(v_dateSecond_5564_);
lean_inc(v_pendingHead_5563_);
lean_inc(v_handler_5562_);
lean_inc(v_inputWanted_5561_);
lean_inc(v_respStream_5560_);
lean_inc_ref(v_response_5559_);
lean_inc_ref(v_timer_5558_);
lean_inc_ref(v_requestStream_5557_);
lean_inc_ref(v_machine_5556_);
lean_del_object(v___x_5548_);
lean_dec(v_a_5546_);
goto v___jp_5566_;
}
else
{
if (v___y_5577_ == 0)
{
lean_dec(v_maximumRecvSize_5534_);
lean_dec_ref(v_connectionContext_5533_);
lean_dec(v_socket_5532_);
lean_dec_ref(v_inst_5531_);
lean_dec(v_keepAliveTimeout_5530_);
lean_dec_ref(v_a_5529_);
lean_dec_ref(v___f_5528_);
lean_dec_ref(v_config_5527_);
lean_dec(v_handler_5526_);
lean_dec_ref(v_responseBodyInstance_5525_);
lean_dec_ref(v_h_5524_);
lean_dec(v___x_5523_);
goto v___jp_5550_;
}
else
{
lean_inc(v_dateSecond_5564_);
lean_inc(v_pendingHead_5563_);
lean_inc(v_handler_5562_);
lean_inc(v_inputWanted_5561_);
lean_inc(v_respStream_5560_);
lean_inc_ref(v_response_5559_);
lean_inc_ref(v_timer_5558_);
lean_inc_ref(v_requestStream_5557_);
lean_inc_ref(v_machine_5556_);
lean_del_object(v___x_5548_);
lean_dec(v_a_5546_);
goto v___jp_5566_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v___x_5590_, lean_object* v_h_5591_, lean_object* v_responseBodyInstance_5592_, lean_object* v_handler_5593_, lean_object* v_config_5594_, lean_object* v___f_5595_, lean_object* v_a_5596_, lean_object* v_keepAliveTimeout_5597_, lean_object* v_inst_5598_, lean_object* v_socket_5599_, lean_object* v_connectionContext_5600_, lean_object* v_maximumRecvSize_5601_, lean_object* v_x_5602_, lean_object* v___y_5603_){
_start:
{
lean_object* v_res_5604_; 
v_res_5604_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v___x_5590_, v_h_5591_, v_responseBodyInstance_5592_, v_handler_5593_, v_config_5594_, v___f_5595_, v_a_5596_, v_keepAliveTimeout_5597_, v_inst_5598_, v_socket_5599_, v_connectionContext_5600_, v_maximumRecvSize_5601_, v_x_5602_);
return v_res_5604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v_h_5605_, lean_object* v_handler_5606_, lean_object* v_extensions_5607_, lean_object* v_connectionContext_5608_, lean_object* v___f_5609_, lean_object* v_x_5610_){
_start:
{
if (lean_obj_tag(v_x_5610_) == 0)
{
lean_object* v_a_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5620_; 
lean_dec_ref(v___f_5609_);
lean_dec_ref(v_connectionContext_5608_);
lean_dec(v_extensions_5607_);
lean_dec(v_handler_5606_);
lean_dec_ref(v_h_5605_);
v_a_5612_ = lean_ctor_get(v_x_5610_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v_x_5610_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5614_ = v_x_5610_;
v_isShared_5615_ = v_isSharedCheck_5620_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v_x_5610_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5620_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___x_5617_; 
if (v_isShared_5615_ == 0)
{
v___x_5617_ = v___x_5614_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5612_);
v___x_5617_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
lean_object* v___x_5618_; 
v___x_5618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5618_, 0, v___x_5617_);
return v___x_5618_;
}
}
}
else
{
lean_object* v_a_5621_; lean_object* v___x_5622_; uint8_t v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; 
v_a_5621_ = lean_ctor_get(v_x_5610_, 0);
lean_inc(v_a_5621_);
lean_dec_ref_known(v_x_5610_, 1);
v___x_5622_ = lean_unsigned_to_nat(0u);
v___x_5623_ = 0;
v___x_5624_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_5605_, v_handler_5606_, v_extensions_5607_, v_connectionContext_5608_, v_a_5621_);
v___x_5625_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5622_, v___x_5623_, v___x_5624_, v___f_5609_);
return v___x_5625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v_h_5626_, lean_object* v_handler_5627_, lean_object* v_extensions_5628_, lean_object* v_connectionContext_5629_, lean_object* v___f_5630_, lean_object* v_x_5631_, lean_object* v___y_5632_){
_start:
{
lean_object* v_res_5633_; 
v_res_5633_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v_h_5626_, v_handler_5627_, v_extensions_5628_, v_connectionContext_5629_, v___f_5630_, v_x_5631_);
return v_res_5633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_5634_, lean_object* v_responseBodyInstance_5635_, lean_object* v_handler_5636_, lean_object* v_config_5637_, lean_object* v_connectionContext_5638_, lean_object* v_events_5639_, lean_object* v___x_5640_, lean_object* v___f_5641_, lean_object* v_____r_5642_){
_start:
{
lean_object* v___x_5644_; uint8_t v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; 
v___x_5644_ = lean_unsigned_to_nat(0u);
v___x_5645_ = 0;
v___x_5646_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_5634_, v_responseBodyInstance_5635_, v_handler_5636_, v_config_5637_, v_connectionContext_5638_, v_events_5639_, v___x_5640_);
v___x_5647_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5644_, v___x_5645_, v___x_5646_, v___f_5641_);
return v___x_5647_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_5648_, lean_object* v_responseBodyInstance_5649_, lean_object* v_handler_5650_, lean_object* v_config_5651_, lean_object* v_connectionContext_5652_, lean_object* v_events_5653_, lean_object* v___x_5654_, lean_object* v___f_5655_, lean_object* v_____r_5656_, lean_object* v___y_5657_){
_start:
{
lean_object* v_res_5658_; 
v_res_5658_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_5648_, v_responseBodyInstance_5649_, v_handler_5650_, v_config_5651_, v_connectionContext_5652_, v_events_5653_, v___x_5654_, v___f_5655_, v_____r_5656_);
return v_res_5658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_h_5659_, lean_object* v_handler_5660_, lean_object* v_a_5661_, lean_object* v___f_5662_, lean_object* v___f_5663_, lean_object* v_x_5664_){
_start:
{
if (lean_obj_tag(v_x_5664_) == 0)
{
lean_object* v_a_5666_; lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5674_; 
lean_dec_ref(v___f_5663_);
lean_dec_ref(v___f_5662_);
lean_dec(v_handler_5660_);
lean_dec_ref(v_h_5659_);
v_a_5666_ = lean_ctor_get(v_x_5664_, 0);
v_isSharedCheck_5674_ = !lean_is_exclusive(v_x_5664_);
if (v_isSharedCheck_5674_ == 0)
{
v___x_5668_ = v_x_5664_;
v_isShared_5669_ = v_isSharedCheck_5674_;
goto v_resetjp_5667_;
}
else
{
lean_inc(v_a_5666_);
lean_dec(v_x_5664_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5674_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5671_; 
if (v_isShared_5669_ == 0)
{
v___x_5671_ = v___x_5668_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5673_; 
v_reuseFailAlloc_5673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5673_, 0, v_a_5666_);
v___x_5671_ = v_reuseFailAlloc_5673_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
lean_object* v___x_5672_; 
v___x_5672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5672_, 0, v___x_5671_);
return v___x_5672_;
}
}
}
else
{
lean_object* v_a_5675_; uint8_t v___x_5676_; 
v_a_5675_ = lean_ctor_get(v_x_5664_, 0);
lean_inc(v_a_5675_);
lean_dec_ref_known(v_x_5664_, 1);
v___x_5676_ = lean_unbox(v_a_5675_);
if (v___x_5676_ == 0)
{
lean_object* v___x_5677_; lean_object* v___x_5678_; uint8_t v___x_5679_; lean_object* v___x_5680_; 
lean_dec_ref(v___f_5663_);
v___x_5677_ = lean_unsigned_to_nat(0u);
v___x_5678_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_h_5659_, v_handler_5660_, v_a_5661_);
v___x_5679_ = lean_unbox(v_a_5675_);
lean_dec(v_a_5675_);
v___x_5680_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5677_, v___x_5679_, v___x_5678_, v___f_5662_);
return v___x_5680_;
}
else
{
lean_object* v___x_5681_; lean_object* v___x_5682_; 
lean_dec(v_a_5675_);
lean_dec_ref(v___f_5662_);
lean_dec(v_handler_5660_);
lean_dec_ref(v_h_5659_);
v___x_5681_ = lean_box(0);
v___x_5682_ = lean_apply_2(v___f_5663_, v___x_5681_, lean_box(0));
return v___x_5682_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_h_5683_, lean_object* v_handler_5684_, lean_object* v_a_5685_, lean_object* v___f_5686_, lean_object* v___f_5687_, lean_object* v_x_5688_, lean_object* v___y_5689_){
_start:
{
lean_object* v_res_5690_; 
v_res_5690_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_h_5683_, v_handler_5684_, v_a_5685_, v___f_5686_, v___f_5687_, v_x_5688_);
lean_dec_ref(v_a_5685_);
return v_res_5690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(lean_object* v_h_5691_, lean_object* v_handler_5692_, lean_object* v_a_5693_, lean_object* v___f_5694_, lean_object* v___x_5695_, lean_object* v_responseBodyInstance_5696_, lean_object* v_config_5697_, lean_object* v___f_5698_, lean_object* v_keepAliveTimeout_5699_, lean_object* v_inst_5700_, lean_object* v_socket_5701_, lean_object* v_connectionContext_5702_, lean_object* v_maximumRecvSize_5703_, lean_object* v_extensions_5704_, lean_object* v_events_5705_, lean_object* v___x_5706_, lean_object* v___f_5707_, lean_object* v___f_5708_, lean_object* v_x_5709_){
_start:
{
if (lean_obj_tag(v_x_5709_) == 0)
{
lean_object* v_a_5711_; lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5719_; 
lean_dec_ref(v___f_5708_);
lean_dec_ref(v___f_5707_);
lean_dec_ref(v___x_5706_);
lean_dec_ref(v_events_5705_);
lean_dec(v_extensions_5704_);
lean_dec(v_maximumRecvSize_5703_);
lean_dec_ref(v_connectionContext_5702_);
lean_dec(v_socket_5701_);
lean_dec_ref(v_inst_5700_);
lean_dec(v_keepAliveTimeout_5699_);
lean_dec_ref(v___f_5698_);
lean_dec_ref(v_config_5697_);
lean_dec_ref(v_responseBodyInstance_5696_);
lean_dec(v___x_5695_);
lean_dec_ref(v___f_5694_);
lean_dec_ref(v_a_5693_);
lean_dec(v_handler_5692_);
lean_dec_ref(v_h_5691_);
v_a_5711_ = lean_ctor_get(v_x_5709_, 0);
v_isSharedCheck_5719_ = !lean_is_exclusive(v_x_5709_);
if (v_isSharedCheck_5719_ == 0)
{
v___x_5713_ = v_x_5709_;
v_isShared_5714_ = v_isSharedCheck_5719_;
goto v_resetjp_5712_;
}
else
{
lean_inc(v_a_5711_);
lean_dec(v_x_5709_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5719_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
lean_object* v___x_5716_; 
if (v_isShared_5714_ == 0)
{
v___x_5716_ = v___x_5713_;
goto v_reusejp_5715_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v_a_5711_);
v___x_5716_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5715_;
}
v_reusejp_5715_:
{
lean_object* v___x_5717_; 
v___x_5717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5716_);
return v___x_5717_;
}
}
}
else
{
lean_object* v_a_5720_; uint8_t v___x_5721_; 
v_a_5720_ = lean_ctor_get(v_x_5709_, 0);
lean_inc(v_a_5720_);
lean_dec_ref_known(v_x_5709_, 1);
v___x_5721_ = lean_unbox(v_a_5720_);
if (v___x_5721_ == 0)
{
lean_object* v___x_5722_; lean_object* v___x_5723_; uint8_t v___x_5724_; lean_object* v___x_5725_; 
lean_dec_ref(v___f_5708_);
lean_dec_ref(v___f_5707_);
lean_dec_ref(v___x_5706_);
lean_dec_ref(v_events_5705_);
lean_dec(v_extensions_5704_);
lean_dec(v_maximumRecvSize_5703_);
lean_dec_ref(v_connectionContext_5702_);
lean_dec(v_socket_5701_);
lean_dec_ref(v_inst_5700_);
lean_dec(v_keepAliveTimeout_5699_);
lean_dec_ref(v___f_5698_);
lean_dec_ref(v_config_5697_);
lean_dec_ref(v_responseBodyInstance_5696_);
lean_dec(v___x_5695_);
v___x_5722_ = lean_unsigned_to_nat(0u);
v___x_5723_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_h_5691_, v_handler_5692_, v_a_5693_);
lean_dec_ref(v_a_5693_);
v___x_5724_ = lean_unbox(v_a_5720_);
lean_dec(v_a_5720_);
v___x_5725_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5722_, v___x_5724_, v___x_5723_, v___f_5694_);
return v___x_5725_;
}
else
{
lean_object* v___f_5726_; lean_object* v___f_5727_; lean_object* v___f_5728_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; uint8_t v___x_5735_; 
lean_dec(v_a_5720_);
lean_dec_ref(v___f_5694_);
lean_inc_ref_n(v_connectionContext_5702_, 3);
lean_inc_ref(v_a_5693_);
lean_inc_ref_n(v_config_5697_, 2);
lean_inc_n(v_handler_5692_, 3);
lean_inc_ref_n(v_responseBodyInstance_5696_, 2);
lean_inc_ref_n(v_h_5691_, 3);
v___f_5726_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 14, 12);
lean_closure_set(v___f_5726_, 0, v___x_5695_);
lean_closure_set(v___f_5726_, 1, v_h_5691_);
lean_closure_set(v___f_5726_, 2, v_responseBodyInstance_5696_);
lean_closure_set(v___f_5726_, 3, v_handler_5692_);
lean_closure_set(v___f_5726_, 4, v_config_5697_);
lean_closure_set(v___f_5726_, 5, v___f_5698_);
lean_closure_set(v___f_5726_, 6, v_a_5693_);
lean_closure_set(v___f_5726_, 7, v_keepAliveTimeout_5699_);
lean_closure_set(v___f_5726_, 8, v_inst_5700_);
lean_closure_set(v___f_5726_, 9, v_socket_5701_);
lean_closure_set(v___f_5726_, 10, v_connectionContext_5702_);
lean_closure_set(v___f_5726_, 11, v_maximumRecvSize_5703_);
v___f_5727_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 7, 5);
lean_closure_set(v___f_5727_, 0, v_h_5691_);
lean_closure_set(v___f_5727_, 1, v_handler_5692_);
lean_closure_set(v___f_5727_, 2, v_extensions_5704_);
lean_closure_set(v___f_5727_, 3, v_connectionContext_5702_);
lean_closure_set(v___f_5727_, 4, v___f_5726_);
lean_inc_ref(v___f_5727_);
lean_inc_ref(v___x_5706_);
lean_inc_ref(v_events_5705_);
v___f_5728_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 10, 8);
lean_closure_set(v___f_5728_, 0, v_h_5691_);
lean_closure_set(v___f_5728_, 1, v_responseBodyInstance_5696_);
lean_closure_set(v___f_5728_, 2, v_handler_5692_);
lean_closure_set(v___f_5728_, 3, v_config_5697_);
lean_closure_set(v___f_5728_, 4, v_connectionContext_5702_);
lean_closure_set(v___f_5728_, 5, v_events_5705_);
lean_closure_set(v___f_5728_, 6, v___x_5706_);
lean_closure_set(v___f_5728_, 7, v___f_5727_);
v___x_5732_ = lean_unsigned_to_nat(0u);
v___x_5733_ = lean_array_get_size(v_events_5705_);
v___x_5734_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_5735_ = lean_nat_dec_lt(v___x_5732_, v___x_5733_);
if (v___x_5735_ == 0)
{
lean_dec_ref(v___f_5728_);
lean_dec_ref(v___f_5708_);
lean_dec_ref(v___f_5707_);
lean_dec_ref(v_a_5693_);
goto v___jp_5729_;
}
else
{
if (v___x_5735_ == 0)
{
lean_dec_ref(v___f_5728_);
lean_dec_ref(v___f_5708_);
lean_dec_ref(v___f_5707_);
lean_dec_ref(v_a_5693_);
goto v___jp_5729_;
}
else
{
size_t v___x_5736_; size_t v___x_5737_; lean_object* v___x_5738_; uint8_t v___x_5739_; 
v___x_5736_ = ((size_t)0ULL);
v___x_5737_ = lean_usize_of_nat(v___x_5733_);
lean_inc_ref(v_events_5705_);
v___x_5738_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_5734_, v___f_5707_, v_events_5705_, v___x_5736_, v___x_5737_);
v___x_5739_ = lean_unbox(v___x_5738_);
lean_dec(v___x_5738_);
if (v___x_5739_ == 0)
{
lean_dec_ref(v___f_5728_);
lean_dec_ref(v___f_5708_);
lean_dec_ref(v_a_5693_);
goto v___jp_5729_;
}
else
{
lean_object* v___f_5740_; uint8_t v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; 
lean_dec_ref(v___f_5727_);
lean_dec_ref(v___x_5706_);
lean_dec_ref(v_events_5705_);
lean_dec_ref(v_connectionContext_5702_);
lean_dec_ref(v_config_5697_);
lean_dec_ref(v_responseBodyInstance_5696_);
lean_inc_ref(v_a_5693_);
v___f_5740_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 7, 5);
lean_closure_set(v___f_5740_, 0, v_h_5691_);
lean_closure_set(v___f_5740_, 1, v_handler_5692_);
lean_closure_set(v___f_5740_, 2, v_a_5693_);
lean_closure_set(v___f_5740_, 3, v___f_5708_);
lean_closure_set(v___f_5740_, 4, v___f_5728_);
v___x_5741_ = 0;
v___x_5742_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg(v_a_5693_);
v___x_5743_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5732_, v___x_5741_, v___x_5742_, v___f_5740_);
return v___x_5743_;
}
}
}
v___jp_5729_:
{
lean_object* v___x_5730_; lean_object* v___x_5731_; 
v___x_5730_ = lean_box(0);
v___x_5731_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_5691_, v_responseBodyInstance_5696_, v_handler_5692_, v_config_5697_, v_connectionContext_5702_, v_events_5705_, v___x_5706_, v___f_5727_, v___x_5730_);
return v___x_5731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object** _args){
lean_object* v_h_5744_ = _args[0];
lean_object* v_handler_5745_ = _args[1];
lean_object* v_a_5746_ = _args[2];
lean_object* v___f_5747_ = _args[3];
lean_object* v___x_5748_ = _args[4];
lean_object* v_responseBodyInstance_5749_ = _args[5];
lean_object* v_config_5750_ = _args[6];
lean_object* v___f_5751_ = _args[7];
lean_object* v_keepAliveTimeout_5752_ = _args[8];
lean_object* v_inst_5753_ = _args[9];
lean_object* v_socket_5754_ = _args[10];
lean_object* v_connectionContext_5755_ = _args[11];
lean_object* v_maximumRecvSize_5756_ = _args[12];
lean_object* v_extensions_5757_ = _args[13];
lean_object* v_events_5758_ = _args[14];
lean_object* v___x_5759_ = _args[15];
lean_object* v___f_5760_ = _args[16];
lean_object* v___f_5761_ = _args[17];
lean_object* v_x_5762_ = _args[18];
lean_object* v___y_5763_ = _args[19];
_start:
{
lean_object* v_res_5764_; 
v_res_5764_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v_h_5744_, v_handler_5745_, v_a_5746_, v___f_5747_, v___x_5748_, v_responseBodyInstance_5749_, v_config_5750_, v___f_5751_, v_keepAliveTimeout_5752_, v_inst_5753_, v_socket_5754_, v_connectionContext_5755_, v_maximumRecvSize_5756_, v_extensions_5757_, v_events_5758_, v___x_5759_, v___f_5760_, v___f_5761_, v_x_5762_);
return v_res_5764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(uint8_t v___x_5765_, lean_object* v_h_5766_, lean_object* v_handler_5767_, lean_object* v_a_5768_, lean_object* v___x_5769_, lean_object* v_responseBodyInstance_5770_, lean_object* v_config_5771_, lean_object* v___f_5772_, lean_object* v_keepAliveTimeout_5773_, lean_object* v_inst_5774_, lean_object* v_socket_5775_, lean_object* v_connectionContext_5776_, lean_object* v_maximumRecvSize_5777_, lean_object* v_extensions_5778_, lean_object* v___f_5779_, lean_object* v_x_5780_){
_start:
{
if (lean_obj_tag(v_x_5780_) == 0)
{
lean_object* v_a_5782_; lean_object* v___x_5784_; uint8_t v_isShared_5785_; uint8_t v_isSharedCheck_5790_; 
lean_dec_ref(v___f_5779_);
lean_dec(v_extensions_5778_);
lean_dec(v_maximumRecvSize_5777_);
lean_dec_ref(v_connectionContext_5776_);
lean_dec(v_socket_5775_);
lean_dec_ref(v_inst_5774_);
lean_dec(v_keepAliveTimeout_5773_);
lean_dec_ref(v___f_5772_);
lean_dec_ref(v_config_5771_);
lean_dec_ref(v_responseBodyInstance_5770_);
lean_dec(v___x_5769_);
lean_dec_ref(v_a_5768_);
lean_dec(v_handler_5767_);
lean_dec_ref(v_h_5766_);
v_a_5782_ = lean_ctor_get(v_x_5780_, 0);
v_isSharedCheck_5790_ = !lean_is_exclusive(v_x_5780_);
if (v_isSharedCheck_5790_ == 0)
{
v___x_5784_ = v_x_5780_;
v_isShared_5785_ = v_isSharedCheck_5790_;
goto v_resetjp_5783_;
}
else
{
lean_inc(v_a_5782_);
lean_dec(v_x_5780_);
v___x_5784_ = lean_box(0);
v_isShared_5785_ = v_isSharedCheck_5790_;
goto v_resetjp_5783_;
}
v_resetjp_5783_:
{
lean_object* v___x_5787_; 
if (v_isShared_5785_ == 0)
{
v___x_5787_ = v___x_5784_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5789_; 
v_reuseFailAlloc_5789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5789_, 0, v_a_5782_);
v___x_5787_ = v_reuseFailAlloc_5789_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
lean_object* v___x_5788_; 
v___x_5788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5788_, 0, v___x_5787_);
return v___x_5788_;
}
}
}
else
{
lean_object* v_a_5791_; lean_object* v_machine_5792_; lean_object* v_requestStream_5793_; lean_object* v_timer_5794_; lean_object* v_response_5795_; lean_object* v_respStream_5796_; lean_object* v_inputWanted_5797_; lean_object* v_handler_5798_; lean_object* v_pendingHead_5799_; lean_object* v_dateSecond_5800_; uint8_t v_requestEnded_5801_; lean_object* v___x_5803_; uint8_t v_isShared_5804_; uint8_t v_isSharedCheck_5820_; 
v_a_5791_ = lean_ctor_get(v_x_5780_, 0);
lean_inc(v_a_5791_);
lean_dec_ref_known(v_x_5780_, 1);
v_machine_5792_ = lean_ctor_get(v_a_5791_, 0);
v_requestStream_5793_ = lean_ctor_get(v_a_5791_, 1);
v_timer_5794_ = lean_ctor_get(v_a_5791_, 2);
v_response_5795_ = lean_ctor_get(v_a_5791_, 3);
v_respStream_5796_ = lean_ctor_get(v_a_5791_, 4);
v_inputWanted_5797_ = lean_ctor_get(v_a_5791_, 5);
v_handler_5798_ = lean_ctor_get(v_a_5791_, 6);
v_pendingHead_5799_ = lean_ctor_get(v_a_5791_, 7);
v_dateSecond_5800_ = lean_ctor_get(v_a_5791_, 8);
v_requestEnded_5801_ = lean_ctor_get_uint8(v_a_5791_, sizeof(void*)*9);
v_isSharedCheck_5820_ = !lean_is_exclusive(v_a_5791_);
if (v_isSharedCheck_5820_ == 0)
{
v___x_5803_ = v_a_5791_;
v_isShared_5804_ = v_isSharedCheck_5820_;
goto v_resetjp_5802_;
}
else
{
lean_inc(v_dateSecond_5800_);
lean_inc(v_pendingHead_5799_);
lean_inc(v_handler_5798_);
lean_inc(v_inputWanted_5797_);
lean_inc(v_respStream_5796_);
lean_inc(v_response_5795_);
lean_inc(v_timer_5794_);
lean_inc(v_requestStream_5793_);
lean_inc(v_machine_5792_);
lean_dec(v_a_5791_);
v___x_5803_ = lean_box(0);
v_isShared_5804_ = v_isSharedCheck_5820_;
goto v_resetjp_5802_;
}
v_resetjp_5802_:
{
lean_object* v___x_5805_; lean_object* v_snd_5806_; lean_object* v_fst_5807_; lean_object* v_events_5808_; lean_object* v_output_5809_; lean_object* v___x_5811_; 
v___x_5805_ = l_Std_Http_Protocol_H1_Machine_step(v___x_5765_, v_machine_5792_);
v_snd_5806_ = lean_ctor_get(v___x_5805_, 1);
lean_inc(v_snd_5806_);
v_fst_5807_ = lean_ctor_get(v___x_5805_, 0);
lean_inc(v_fst_5807_);
lean_dec_ref(v___x_5805_);
v_events_5808_ = lean_ctor_get(v_snd_5806_, 0);
lean_inc_ref(v_events_5808_);
v_output_5809_ = lean_ctor_get(v_snd_5806_, 1);
lean_inc_ref(v_output_5809_);
lean_dec(v_snd_5806_);
if (v_isShared_5804_ == 0)
{
lean_ctor_set(v___x_5803_, 0, v_fst_5807_);
v___x_5811_ = v___x_5803_;
goto v_reusejp_5810_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_fst_5807_);
lean_ctor_set(v_reuseFailAlloc_5819_, 1, v_requestStream_5793_);
lean_ctor_set(v_reuseFailAlloc_5819_, 2, v_timer_5794_);
lean_ctor_set(v_reuseFailAlloc_5819_, 3, v_response_5795_);
lean_ctor_set(v_reuseFailAlloc_5819_, 4, v_respStream_5796_);
lean_ctor_set(v_reuseFailAlloc_5819_, 5, v_inputWanted_5797_);
lean_ctor_set(v_reuseFailAlloc_5819_, 6, v_handler_5798_);
lean_ctor_set(v_reuseFailAlloc_5819_, 7, v_pendingHead_5799_);
lean_ctor_set(v_reuseFailAlloc_5819_, 8, v_dateSecond_5800_);
lean_ctor_set_uint8(v_reuseFailAlloc_5819_, sizeof(void*)*9, v_requestEnded_5801_);
v___x_5811_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5810_;
}
v_reusejp_5810_:
{
lean_object* v___f_5812_; lean_object* v___f_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; uint8_t v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; 
lean_inc_ref(v___x_5811_);
v___f_5812_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_5812_, 0, v___x_5811_);
lean_inc_ref(v_inst_5774_);
lean_inc_ref(v___f_5812_);
lean_inc_ref(v_a_5768_);
v___f_5813_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 20, 18);
lean_closure_set(v___f_5813_, 0, v_h_5766_);
lean_closure_set(v___f_5813_, 1, v_handler_5767_);
lean_closure_set(v___f_5813_, 2, v_a_5768_);
lean_closure_set(v___f_5813_, 3, v___f_5812_);
lean_closure_set(v___f_5813_, 4, v___x_5769_);
lean_closure_set(v___f_5813_, 5, v_responseBodyInstance_5770_);
lean_closure_set(v___f_5813_, 6, v_config_5771_);
lean_closure_set(v___f_5813_, 7, v___f_5772_);
lean_closure_set(v___f_5813_, 8, v_keepAliveTimeout_5773_);
lean_closure_set(v___f_5813_, 9, v_inst_5774_);
lean_closure_set(v___f_5813_, 10, v_socket_5775_);
lean_closure_set(v___f_5813_, 11, v_connectionContext_5776_);
lean_closure_set(v___f_5813_, 12, v_maximumRecvSize_5777_);
lean_closure_set(v___f_5813_, 13, v_extensions_5778_);
lean_closure_set(v___f_5813_, 14, v_events_5808_);
lean_closure_set(v___f_5813_, 15, v___x_5811_);
lean_closure_set(v___f_5813_, 16, v___f_5779_);
lean_closure_set(v___f_5813_, 17, v___f_5812_);
v___x_5814_ = lean_unsigned_to_nat(65536u);
v___x_5815_ = lean_unsigned_to_nat(0u);
v___x_5816_ = 0;
v___x_5817_ = l_Std_Http_Internal_Outbox_push___redArg(v_inst_5774_, v_a_5768_, v_output_5809_, v___x_5814_);
v___x_5818_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5815_, v___x_5816_, v___x_5817_, v___f_5813_);
return v___x_5818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object** _args){
lean_object* v___x_5821_ = _args[0];
lean_object* v_h_5822_ = _args[1];
lean_object* v_handler_5823_ = _args[2];
lean_object* v_a_5824_ = _args[3];
lean_object* v___x_5825_ = _args[4];
lean_object* v_responseBodyInstance_5826_ = _args[5];
lean_object* v_config_5827_ = _args[6];
lean_object* v___f_5828_ = _args[7];
lean_object* v_keepAliveTimeout_5829_ = _args[8];
lean_object* v_inst_5830_ = _args[9];
lean_object* v_socket_5831_ = _args[10];
lean_object* v_connectionContext_5832_ = _args[11];
lean_object* v_maximumRecvSize_5833_ = _args[12];
lean_object* v_extensions_5834_ = _args[13];
lean_object* v___f_5835_ = _args[14];
lean_object* v_x_5836_ = _args[15];
lean_object* v___y_5837_ = _args[16];
_start:
{
uint8_t v___x_9479__boxed_5838_; lean_object* v_res_5839_; 
v___x_9479__boxed_5838_ = lean_unbox(v___x_5821_);
v_res_5839_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v___x_9479__boxed_5838_, v_h_5822_, v_handler_5823_, v_a_5824_, v___x_5825_, v_responseBodyInstance_5826_, v_config_5827_, v___f_5828_, v_keepAliveTimeout_5829_, v_inst_5830_, v_socket_5831_, v_connectionContext_5832_, v_maximumRecvSize_5833_, v_extensions_5834_, v___f_5835_, v_x_5836_);
return v_res_5839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_5840_, lean_object* v_handler_5841_, lean_object* v_a_5842_, lean_object* v___x_5843_, lean_object* v_responseBodyInstance_5844_, lean_object* v_config_5845_, lean_object* v___f_5846_, lean_object* v_keepAliveTimeout_5847_, lean_object* v_inst_5848_, lean_object* v_socket_5849_, lean_object* v_connectionContext_5850_, lean_object* v_maximumRecvSize_5851_, lean_object* v_extensions_5852_, lean_object* v___f_5853_, lean_object* v_x_5854_, lean_object* v_____s_5855_){
_start:
{
lean_object* v_machine_5857_; lean_object* v_reader_5858_; lean_object* v_writer_5859_; lean_object* v_state_5860_; uint8_t v___x_5861_; lean_object* v___x_5862_; lean_object* v___f_5863_; uint8_t v___y_5865_; lean_object* v___y_5866_; lean_object* v_val_5867_; uint8_t v___y_5871_; 
v_machine_5857_ = lean_ctor_get(v_____s_5855_, 0);
v_reader_5858_ = lean_ctor_get(v_machine_5857_, 0);
v_writer_5859_ = lean_ctor_get(v_machine_5857_, 1);
v_state_5860_ = lean_ctor_get(v_reader_5858_, 0);
v___x_5861_ = 0;
v___x_5862_ = lean_box(v___x_5861_);
lean_inc_ref(v_config_5845_);
v___f_5863_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 17, 15);
lean_closure_set(v___f_5863_, 0, v___x_5862_);
lean_closure_set(v___f_5863_, 1, v_h_5840_);
lean_closure_set(v___f_5863_, 2, v_handler_5841_);
lean_closure_set(v___f_5863_, 3, v_a_5842_);
lean_closure_set(v___f_5863_, 4, v___x_5843_);
lean_closure_set(v___f_5863_, 5, v_responseBodyInstance_5844_);
lean_closure_set(v___f_5863_, 6, v_config_5845_);
lean_closure_set(v___f_5863_, 7, v___f_5846_);
lean_closure_set(v___f_5863_, 8, v_keepAliveTimeout_5847_);
lean_closure_set(v___f_5863_, 9, v_inst_5848_);
lean_closure_set(v___f_5863_, 10, v_socket_5849_);
lean_closure_set(v___f_5863_, 11, v_connectionContext_5850_);
lean_closure_set(v___f_5863_, 12, v_maximumRecvSize_5851_);
lean_closure_set(v___f_5863_, 13, v_extensions_5852_);
lean_closure_set(v___f_5863_, 14, v___f_5853_);
if (lean_obj_tag(v_state_5860_) == 6)
{
lean_object* v_state_5890_; 
v_state_5890_ = lean_ctor_get(v_writer_5859_, 2);
if (lean_obj_tag(v_state_5890_) == 7)
{
lean_object* v_outputData_5891_; lean_object* v_size_5892_; lean_object* v___x_5893_; uint8_t v___x_5894_; 
v_outputData_5891_ = lean_ctor_get(v_writer_5859_, 1);
v_size_5892_ = lean_ctor_get(v_outputData_5891_, 1);
v___x_5893_ = lean_unsigned_to_nat(0u);
v___x_5894_ = lean_nat_dec_eq(v_size_5892_, v___x_5893_);
if (v___x_5894_ == 0)
{
v___y_5871_ = v___x_5894_;
goto v___jp_5870_;
}
else
{
lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; 
lean_dec_ref(v___f_5863_);
lean_dec_ref(v_config_5845_);
v___x_5895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5895_, 0, v_____s_5855_);
v___x_5896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5896_, 0, v___x_5895_);
v___x_5897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5896_);
return v___x_5897_;
}
}
else
{
uint8_t v___x_5898_; 
v___x_5898_ = 0;
v___y_5871_ = v___x_5898_;
goto v___jp_5870_;
}
}
else
{
uint8_t v___x_5899_; 
v___x_5899_ = 0;
v___y_5871_ = v___x_5899_;
goto v___jp_5870_;
}
v___jp_5864_:
{
lean_object* v___x_5868_; lean_object* v___x_5869_; 
v___x_5868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5868_, 0, v_val_5867_);
v___x_5869_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_5866_, v___y_5865_, v___x_5868_, v___f_5863_);
return v___x_5869_;
}
v___jp_5870_:
{
lean_object* v___x_5872_; lean_object* v___x_5873_; 
v___x_5872_ = lean_unsigned_to_nat(0u);
v___x_5873_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(v_config_5845_, v_____s_5855_);
lean_dec_ref(v_config_5845_);
if (lean_obj_tag(v___x_5873_) == 0)
{
lean_object* v_a_5874_; lean_object* v___x_5876_; uint8_t v_isShared_5877_; uint8_t v_isSharedCheck_5881_; 
v_a_5874_ = lean_ctor_get(v___x_5873_, 0);
v_isSharedCheck_5881_ = !lean_is_exclusive(v___x_5873_);
if (v_isSharedCheck_5881_ == 0)
{
v___x_5876_ = v___x_5873_;
v_isShared_5877_ = v_isSharedCheck_5881_;
goto v_resetjp_5875_;
}
else
{
lean_inc(v_a_5874_);
lean_dec(v___x_5873_);
v___x_5876_ = lean_box(0);
v_isShared_5877_ = v_isSharedCheck_5881_;
goto v_resetjp_5875_;
}
v_resetjp_5875_:
{
lean_object* v___x_5879_; 
if (v_isShared_5877_ == 0)
{
lean_ctor_set_tag(v___x_5876_, 1);
v___x_5879_ = v___x_5876_;
goto v_reusejp_5878_;
}
else
{
lean_object* v_reuseFailAlloc_5880_; 
v_reuseFailAlloc_5880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5880_, 0, v_a_5874_);
v___x_5879_ = v_reuseFailAlloc_5880_;
goto v_reusejp_5878_;
}
v_reusejp_5878_:
{
v___y_5865_ = v___y_5871_;
v___y_5866_ = v___x_5872_;
v_val_5867_ = v___x_5879_;
goto v___jp_5864_;
}
}
}
else
{
lean_object* v_a_5882_; lean_object* v___x_5884_; uint8_t v_isShared_5885_; uint8_t v_isSharedCheck_5889_; 
v_a_5882_ = lean_ctor_get(v___x_5873_, 0);
v_isSharedCheck_5889_ = !lean_is_exclusive(v___x_5873_);
if (v_isSharedCheck_5889_ == 0)
{
v___x_5884_ = v___x_5873_;
v_isShared_5885_ = v_isSharedCheck_5889_;
goto v_resetjp_5883_;
}
else
{
lean_inc(v_a_5882_);
lean_dec(v___x_5873_);
v___x_5884_ = lean_box(0);
v_isShared_5885_ = v_isSharedCheck_5889_;
goto v_resetjp_5883_;
}
v_resetjp_5883_:
{
lean_object* v___x_5887_; 
if (v_isShared_5885_ == 0)
{
lean_ctor_set_tag(v___x_5884_, 0);
v___x_5887_ = v___x_5884_;
goto v_reusejp_5886_;
}
else
{
lean_object* v_reuseFailAlloc_5888_; 
v_reuseFailAlloc_5888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5888_, 0, v_a_5882_);
v___x_5887_ = v_reuseFailAlloc_5888_;
goto v_reusejp_5886_;
}
v_reusejp_5886_:
{
v___y_5865_ = v___y_5871_;
v___y_5866_ = v___x_5872_;
v_val_5867_ = v___x_5887_;
goto v___jp_5864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object** _args){
lean_object* v_h_5900_ = _args[0];
lean_object* v_handler_5901_ = _args[1];
lean_object* v_a_5902_ = _args[2];
lean_object* v___x_5903_ = _args[3];
lean_object* v_responseBodyInstance_5904_ = _args[4];
lean_object* v_config_5905_ = _args[5];
lean_object* v___f_5906_ = _args[6];
lean_object* v_keepAliveTimeout_5907_ = _args[7];
lean_object* v_inst_5908_ = _args[8];
lean_object* v_socket_5909_ = _args[9];
lean_object* v_connectionContext_5910_ = _args[10];
lean_object* v_maximumRecvSize_5911_ = _args[11];
lean_object* v_extensions_5912_ = _args[12];
lean_object* v___f_5913_ = _args[13];
lean_object* v_x_5914_ = _args[14];
lean_object* v_____s_5915_ = _args[15];
lean_object* v___y_5916_ = _args[16];
_start:
{
lean_object* v_res_5917_; 
v_res_5917_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_5900_, v_handler_5901_, v_a_5902_, v___x_5903_, v_responseBodyInstance_5904_, v_config_5905_, v___f_5906_, v_keepAliveTimeout_5907_, v_inst_5908_, v_socket_5909_, v_connectionContext_5910_, v_maximumRecvSize_5911_, v_extensions_5912_, v___f_5913_, v_x_5914_, v_____s_5915_);
return v_res_5917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v_a_5918_, lean_object* v_maximumRecvSize_5919_, lean_object* v_inst_5920_, lean_object* v_socket_5921_, lean_object* v_lingeringTimeout_5922_, lean_object* v_connectionContext_5923_, lean_object* v_x_5924_){
_start:
{
if (lean_obj_tag(v_x_5924_) == 0)
{
lean_object* v_a_5928_; lean_object* v___x_5930_; uint8_t v_isShared_5931_; uint8_t v_isSharedCheck_5936_; 
lean_dec_ref(v_connectionContext_5923_);
lean_dec(v_lingeringTimeout_5922_);
lean_dec(v_socket_5921_);
lean_dec_ref(v_inst_5920_);
v_a_5928_ = lean_ctor_get(v_x_5924_, 0);
v_isSharedCheck_5936_ = !lean_is_exclusive(v_x_5924_);
if (v_isSharedCheck_5936_ == 0)
{
v___x_5930_ = v_x_5924_;
v_isShared_5931_ = v_isSharedCheck_5936_;
goto v_resetjp_5929_;
}
else
{
lean_inc(v_a_5928_);
lean_dec(v_x_5924_);
v___x_5930_ = lean_box(0);
v_isShared_5931_ = v_isSharedCheck_5936_;
goto v_resetjp_5929_;
}
v_resetjp_5929_:
{
lean_object* v___x_5933_; 
if (v_isShared_5931_ == 0)
{
v___x_5933_ = v___x_5930_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5935_; 
v_reuseFailAlloc_5935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5935_, 0, v_a_5928_);
v___x_5933_ = v_reuseFailAlloc_5935_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
lean_object* v___x_5934_; 
v___x_5934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5933_);
return v___x_5934_;
}
}
}
else
{
lean_object* v_a_5937_; uint8_t v___x_5938_; 
v_a_5937_ = lean_ctor_get(v_x_5924_, 0);
lean_inc(v_a_5937_);
lean_dec_ref_known(v_x_5924_, 1);
v___x_5938_ = lean_unbox(v_a_5937_);
lean_dec(v_a_5937_);
if (v___x_5938_ == 0)
{
uint8_t v___x_5939_; 
v___x_5939_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(v_a_5918_);
if (v___x_5939_ == 0)
{
lean_dec_ref(v_connectionContext_5923_);
lean_dec(v_lingeringTimeout_5922_);
lean_dec(v_socket_5921_);
lean_dec_ref(v_inst_5920_);
goto v___jp_5926_;
}
else
{
uint64_t v___x_5940_; lean_object* v___x_5941_; 
v___x_5940_ = lean_uint64_of_nat(v_maximumRecvSize_5919_);
v___x_5941_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(v_inst_5920_, v_socket_5921_, v_lingeringTimeout_5922_, v___x_5940_, v_connectionContext_5923_);
return v___x_5941_;
}
}
else
{
lean_dec_ref(v_connectionContext_5923_);
lean_dec(v_lingeringTimeout_5922_);
lean_dec(v_socket_5921_);
lean_dec_ref(v_inst_5920_);
goto v___jp_5926_;
}
}
v___jp_5926_:
{
lean_object* v___x_5927_; 
v___x_5927_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_5927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v_a_5942_, lean_object* v_maximumRecvSize_5943_, lean_object* v_inst_5944_, lean_object* v_socket_5945_, lean_object* v_lingeringTimeout_5946_, lean_object* v_connectionContext_5947_, lean_object* v_x_5948_, lean_object* v___y_5949_){
_start:
{
lean_object* v_res_5950_; 
v_res_5950_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v_a_5942_, v_maximumRecvSize_5943_, v_inst_5944_, v_socket_5945_, v_lingeringTimeout_5946_, v_connectionContext_5947_, v_x_5948_);
lean_dec(v_maximumRecvSize_5943_);
lean_dec_ref(v_a_5942_);
return v_res_5950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_a_5951_, lean_object* v___f_5952_, lean_object* v_x_5953_){
_start:
{
if (lean_obj_tag(v_x_5953_) == 0)
{
lean_object* v___x_5955_; 
lean_dec_ref(v___f_5952_);
v___x_5955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5955_, 0, v_x_5953_);
return v___x_5955_;
}
else
{
lean_object* v___x_5957_; uint8_t v_isShared_5958_; uint8_t v_isSharedCheck_5968_; 
v_isSharedCheck_5968_ = !lean_is_exclusive(v_x_5953_);
if (v_isSharedCheck_5968_ == 0)
{
lean_object* v_unused_5969_; 
v_unused_5969_ = lean_ctor_get(v_x_5953_, 0);
lean_dec(v_unused_5969_);
v___x_5957_ = v_x_5953_;
v_isShared_5958_ = v_isSharedCheck_5968_;
goto v_resetjp_5956_;
}
else
{
lean_dec(v_x_5953_);
v___x_5957_ = lean_box(0);
v_isShared_5958_ = v_isSharedCheck_5968_;
goto v_resetjp_5956_;
}
v_resetjp_5956_:
{
lean_object* v___x_5959_; uint8_t v___x_5960_; uint8_t v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5964_; 
v___x_5959_ = lean_unsigned_to_nat(0u);
v___x_5960_ = 0;
v___x_5961_ = l_Std_Http_Internal_Outbox_failed___redArg(v_a_5951_);
v___x_5962_ = lean_box(v___x_5961_);
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 0, v___x_5962_);
v___x_5964_ = v___x_5957_;
goto v_reusejp_5963_;
}
else
{
lean_object* v_reuseFailAlloc_5967_; 
v_reuseFailAlloc_5967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5967_, 0, v___x_5962_);
v___x_5964_ = v_reuseFailAlloc_5967_;
goto v_reusejp_5963_;
}
v_reusejp_5963_:
{
lean_object* v___x_5965_; lean_object* v___x_5966_; 
v___x_5965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5964_);
v___x_5966_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5959_, v___x_5960_, v___x_5965_, v___f_5952_);
return v___x_5966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_a_5970_, lean_object* v___f_5971_, lean_object* v_x_5972_, lean_object* v___y_5973_){
_start:
{
lean_object* v_res_5974_; 
v_res_5974_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_a_5970_, v___f_5971_, v_x_5972_);
lean_dec_ref(v_a_5970_);
return v_res_5974_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_h_5975_, lean_object* v_handler_5976_, lean_object* v_a_5977_, lean_object* v___f_5978_, lean_object* v_x_5979_){
_start:
{
if (lean_obj_tag(v_x_5979_) == 0)
{
lean_object* v___x_5981_; 
lean_dec_ref(v___f_5978_);
lean_dec(v_handler_5976_);
lean_dec_ref(v_h_5975_);
v___x_5981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5981_, 0, v_x_5979_);
return v___x_5981_;
}
else
{
lean_object* v___x_5982_; uint8_t v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; 
lean_dec_ref_known(v_x_5979_, 1);
v___x_5982_ = lean_unsigned_to_nat(0u);
v___x_5983_ = 0;
v___x_5984_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_h_5975_, v_handler_5976_, v_a_5977_);
v___x_5985_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5982_, v___x_5983_, v___x_5984_, v___f_5978_);
return v___x_5985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_h_5986_, lean_object* v_handler_5987_, lean_object* v_a_5988_, lean_object* v___f_5989_, lean_object* v_x_5990_, lean_object* v___y_5991_){
_start:
{
lean_object* v_res_5992_; 
v_res_5992_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_h_5986_, v_handler_5987_, v_a_5988_, v___f_5989_, v_x_5990_);
lean_dec_ref(v_a_5988_);
return v_res_5992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v_a_5993_, lean_object* v___f_5994_, lean_object* v_____r_5995_){
_start:
{
lean_object* v___x_5997_; uint8_t v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; 
v___x_5997_ = lean_unsigned_to_nat(0u);
v___x_5998_ = 0;
v___x_5999_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_a_5993_);
v___x_6000_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5997_, v___x_5998_, v___x_5999_, v___f_5994_);
return v___x_6000_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v_a_6001_, lean_object* v___f_6002_, lean_object* v_____r_6003_, lean_object* v___y_6004_){
_start:
{
lean_object* v_res_6005_; 
v_res_6005_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v_a_6001_, v___f_6002_, v_____r_6003_);
return v_res_6005_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v___f_6006_, lean_object* v_x_6007_){
_start:
{
if (lean_obj_tag(v_x_6007_) == 0)
{
lean_object* v___x_6009_; 
lean_dec_ref(v___f_6006_);
v___x_6009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6009_, 0, v_x_6007_);
return v___x_6009_;
}
else
{
lean_object* v_a_6010_; lean_object* v___x_6011_; 
v_a_6010_ = lean_ctor_get(v_x_6007_, 0);
lean_inc(v_a_6010_);
lean_dec_ref_known(v_x_6007_, 1);
v___x_6011_ = lean_apply_2(v___f_6006_, v_a_6010_, lean_box(0));
return v___x_6011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object* v___f_6012_, lean_object* v_x_6013_, lean_object* v___y_6014_){
_start:
{
lean_object* v_res_6015_; 
v_res_6015_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v___f_6012_, v_x_6013_);
return v_res_6015_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_a_6016_, lean_object* v___f_6017_, lean_object* v___f_6018_, lean_object* v___f_6019_, lean_object* v_____r_6020_){
_start:
{
lean_object* v_handler_6022_; lean_object* v___x_6023_; 
v_handler_6022_ = lean_ctor_get(v_a_6016_, 6);
lean_inc(v_handler_6022_);
lean_dec_ref(v_a_6016_);
v___x_6023_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_task_x3f___redArg(v_handler_6022_);
if (lean_obj_tag(v___x_6023_) == 1)
{
lean_object* v_val_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; uint8_t v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; 
lean_dec_ref(v___f_6019_);
v_val_6024_ = lean_ctor_get(v___x_6023_, 0);
lean_inc(v_val_6024_);
lean_dec_ref_known(v___x_6023_, 1);
v___x_6025_ = lean_alloc_closure((void*)(l_Std_Async_Async_ofTask___boxed), 3, 2);
lean_closure_set(v___x_6025_, 0, lean_box(0));
lean_closure_set(v___x_6025_, 1, v_val_6024_);
v___x_6026_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___boxed), 6, 5);
lean_closure_set(v___x_6026_, 0, lean_box(0));
lean_closure_set(v___x_6026_, 1, lean_box(0));
lean_closure_set(v___x_6026_, 2, lean_box(0));
lean_closure_set(v___x_6026_, 3, v___x_6025_);
lean_closure_set(v___x_6026_, 4, v___f_6017_);
v___x_6027_ = lean_unsigned_to_nat(0u);
v___x_6028_ = 0;
v___x_6029_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_6029_, 0, lean_box(0));
lean_closure_set(v___x_6029_, 1, v___x_6026_);
v___x_6030_ = lean_io_as_task(v___x_6029_, v___x_6027_);
lean_dec_ref(v___x_6030_);
v___x_6031_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
v___x_6032_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6027_, v___x_6028_, v___x_6031_, v___f_6018_);
return v___x_6032_;
}
else
{
lean_object* v___x_6033_; lean_object* v___x_6034_; 
lean_dec(v___x_6023_);
lean_dec_ref(v___f_6018_);
lean_dec_ref(v___f_6017_);
v___x_6033_ = lean_box(0);
v___x_6034_ = lean_apply_2(v___f_6019_, v___x_6033_, lean_box(0));
return v___x_6034_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_a_6035_, lean_object* v___f_6036_, lean_object* v___f_6037_, lean_object* v___f_6038_, lean_object* v_____r_6039_, lean_object* v___y_6040_){
_start:
{
lean_object* v_res_6041_; 
v_res_6041_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_a_6035_, v___f_6036_, v___f_6037_, v___f_6038_, v_____r_6039_);
return v_res_6041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__22(lean_object* v_close_6042_, lean_object* v_val_6043_, lean_object* v___f_6044_, lean_object* v___f_6045_, lean_object* v_x_6046_){
_start:
{
if (lean_obj_tag(v_x_6046_) == 0)
{
lean_object* v_a_6048_; lean_object* v___x_6050_; uint8_t v_isShared_6051_; uint8_t v_isSharedCheck_6056_; 
lean_dec_ref(v___f_6045_);
lean_dec_ref(v___f_6044_);
lean_dec(v_val_6043_);
lean_dec_ref(v_close_6042_);
v_a_6048_ = lean_ctor_get(v_x_6046_, 0);
v_isSharedCheck_6056_ = !lean_is_exclusive(v_x_6046_);
if (v_isSharedCheck_6056_ == 0)
{
v___x_6050_ = v_x_6046_;
v_isShared_6051_ = v_isSharedCheck_6056_;
goto v_resetjp_6049_;
}
else
{
lean_inc(v_a_6048_);
lean_dec(v_x_6046_);
v___x_6050_ = lean_box(0);
v_isShared_6051_ = v_isSharedCheck_6056_;
goto v_resetjp_6049_;
}
v_resetjp_6049_:
{
lean_object* v___x_6053_; 
if (v_isShared_6051_ == 0)
{
v___x_6053_ = v___x_6050_;
goto v_reusejp_6052_;
}
else
{
lean_object* v_reuseFailAlloc_6055_; 
v_reuseFailAlloc_6055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6055_, 0, v_a_6048_);
v___x_6053_ = v_reuseFailAlloc_6055_;
goto v_reusejp_6052_;
}
v_reusejp_6052_:
{
lean_object* v___x_6054_; 
v___x_6054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6054_, 0, v___x_6053_);
return v___x_6054_;
}
}
}
else
{
lean_object* v_a_6057_; uint8_t v___x_6058_; 
v_a_6057_ = lean_ctor_get(v_x_6046_, 0);
lean_inc(v_a_6057_);
lean_dec_ref_known(v_x_6046_, 1);
v___x_6058_ = lean_unbox(v_a_6057_);
if (v___x_6058_ == 0)
{
lean_object* v___x_6059_; lean_object* v___x_6060_; uint8_t v___x_6061_; lean_object* v___x_6062_; 
lean_dec_ref(v___f_6045_);
v___x_6059_ = lean_unsigned_to_nat(0u);
v___x_6060_ = lean_apply_2(v_close_6042_, v_val_6043_, lean_box(0));
v___x_6061_ = lean_unbox(v_a_6057_);
lean_dec(v_a_6057_);
v___x_6062_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6059_, v___x_6061_, v___x_6060_, v___f_6044_);
return v___x_6062_;
}
else
{
lean_object* v___x_6063_; lean_object* v___x_6064_; 
lean_dec(v_a_6057_);
lean_dec_ref(v___f_6044_);
lean_dec(v_val_6043_);
lean_dec_ref(v_close_6042_);
v___x_6063_ = lean_box(0);
v___x_6064_ = lean_apply_2(v___f_6045_, v___x_6063_, lean_box(0));
return v___x_6064_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__22___boxed(lean_object* v_close_6065_, lean_object* v_val_6066_, lean_object* v___f_6067_, lean_object* v___f_6068_, lean_object* v_x_6069_, lean_object* v___y_6070_){
_start:
{
lean_object* v_res_6071_; 
v_res_6071_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__22(v_close_6065_, v_val_6066_, v___f_6067_, v___f_6068_, v_x_6069_);
return v_res_6071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__21(lean_object* v_a_6072_, lean_object* v_responseBodyInstance_6073_, lean_object* v___f_6074_, lean_object* v___f_6075_, lean_object* v_____r_6076_){
_start:
{
lean_object* v_respStream_6078_; 
v_respStream_6078_ = lean_ctor_get(v_a_6072_, 4);
lean_inc(v_respStream_6078_);
lean_dec_ref(v_a_6072_);
if (lean_obj_tag(v_respStream_6078_) == 1)
{
lean_object* v_val_6079_; lean_object* v_close_6080_; lean_object* v_isClosed_6081_; lean_object* v___f_6082_; lean_object* v___x_6083_; uint8_t v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; 
v_val_6079_ = lean_ctor_get(v_respStream_6078_, 0);
lean_inc_n(v_val_6079_, 2);
lean_dec_ref_known(v_respStream_6078_, 1);
v_close_6080_ = lean_ctor_get(v_responseBodyInstance_6073_, 1);
lean_inc_ref(v_close_6080_);
v_isClosed_6081_ = lean_ctor_get(v_responseBodyInstance_6073_, 2);
lean_inc_ref(v_isClosed_6081_);
lean_dec_ref(v_responseBodyInstance_6073_);
v___f_6082_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__22___boxed), 6, 4);
lean_closure_set(v___f_6082_, 0, v_close_6080_);
lean_closure_set(v___f_6082_, 1, v_val_6079_);
lean_closure_set(v___f_6082_, 2, v___f_6074_);
lean_closure_set(v___f_6082_, 3, v___f_6075_);
v___x_6083_ = lean_unsigned_to_nat(0u);
v___x_6084_ = 0;
v___x_6085_ = lean_apply_2(v_isClosed_6081_, v_val_6079_, lean_box(0));
v___x_6086_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6083_, v___x_6084_, v___x_6085_, v___f_6082_);
return v___x_6086_;
}
else
{
lean_object* v___x_6087_; lean_object* v___x_6088_; 
lean_dec(v_respStream_6078_);
lean_dec_ref(v___f_6074_);
lean_dec_ref(v_responseBodyInstance_6073_);
v___x_6087_ = lean_box(0);
v___x_6088_ = lean_apply_2(v___f_6075_, v___x_6087_, lean_box(0));
return v___x_6088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__21___boxed(lean_object* v_a_6089_, lean_object* v_responseBodyInstance_6090_, lean_object* v___f_6091_, lean_object* v___f_6092_, lean_object* v_____r_6093_, lean_object* v___y_6094_){
_start:
{
lean_object* v_res_6095_; 
v_res_6095_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__21(v_a_6089_, v_responseBodyInstance_6090_, v___f_6091_, v___f_6092_, v_____r_6093_);
return v_res_6095_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__23(lean_object* v_close_6096_, lean_object* v_socket_6097_, lean_object* v_x_6098_){
_start:
{
lean_object* v_val_6101_; lean_object* v___x_6103_; 
v___x_6103_ = lean_apply_2(v_close_6096_, v_socket_6097_, lean_box(0));
if (lean_obj_tag(v___x_6103_) == 0)
{
lean_object* v_a_6104_; lean_object* v___x_6106_; uint8_t v_isShared_6107_; uint8_t v_isSharedCheck_6111_; 
v_a_6104_ = lean_ctor_get(v___x_6103_, 0);
v_isSharedCheck_6111_ = !lean_is_exclusive(v___x_6103_);
if (v_isSharedCheck_6111_ == 0)
{
v___x_6106_ = v___x_6103_;
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
else
{
lean_inc(v_a_6104_);
lean_dec(v___x_6103_);
v___x_6106_ = lean_box(0);
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
v_resetjp_6105_:
{
lean_object* v___x_6109_; 
if (v_isShared_6107_ == 0)
{
lean_ctor_set_tag(v___x_6106_, 1);
v___x_6109_ = v___x_6106_;
goto v_reusejp_6108_;
}
else
{
lean_object* v_reuseFailAlloc_6110_; 
v_reuseFailAlloc_6110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6110_, 0, v_a_6104_);
v___x_6109_ = v_reuseFailAlloc_6110_;
goto v_reusejp_6108_;
}
v_reusejp_6108_:
{
v_val_6101_ = v___x_6109_;
goto v___jp_6100_;
}
}
}
else
{
lean_object* v_a_6112_; lean_object* v___x_6114_; uint8_t v_isShared_6115_; uint8_t v_isSharedCheck_6119_; 
v_a_6112_ = lean_ctor_get(v___x_6103_, 0);
v_isSharedCheck_6119_ = !lean_is_exclusive(v___x_6103_);
if (v_isSharedCheck_6119_ == 0)
{
v___x_6114_ = v___x_6103_;
v_isShared_6115_ = v_isSharedCheck_6119_;
goto v_resetjp_6113_;
}
else
{
lean_inc(v_a_6112_);
lean_dec(v___x_6103_);
v___x_6114_ = lean_box(0);
v_isShared_6115_ = v_isSharedCheck_6119_;
goto v_resetjp_6113_;
}
v_resetjp_6113_:
{
lean_object* v___x_6117_; 
if (v_isShared_6115_ == 0)
{
lean_ctor_set_tag(v___x_6114_, 0);
v___x_6117_ = v___x_6114_;
goto v_reusejp_6116_;
}
else
{
lean_object* v_reuseFailAlloc_6118_; 
v_reuseFailAlloc_6118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6118_, 0, v_a_6112_);
v___x_6117_ = v_reuseFailAlloc_6118_;
goto v_reusejp_6116_;
}
v_reusejp_6116_:
{
v_val_6101_ = v___x_6117_;
goto v___jp_6100_;
}
}
}
v___jp_6100_:
{
lean_object* v___x_6102_; 
v___x_6102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6102_, 0, v_val_6101_);
return v___x_6102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__23___boxed(lean_object* v_close_6120_, lean_object* v_socket_6121_, lean_object* v_x_6122_, lean_object* v___y_6123_){
_start:
{
lean_object* v_res_6124_; 
v_res_6124_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__23(v_close_6120_, v_socket_6121_, v_x_6122_);
lean_dec(v_x_6122_);
return v_res_6124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24(lean_object* v_inst_6126_, lean_object* v_maximumRecvSize_6127_, lean_object* v_socket_6128_, lean_object* v_lingeringTimeout_6129_, lean_object* v_connectionContext_6130_, lean_object* v_a_6131_, lean_object* v_h_6132_, lean_object* v_handler_6133_, lean_object* v___f_6134_, lean_object* v_responseBodyInstance_6135_, lean_object* v___f_6136_, lean_object* v_x_6137_){
_start:
{
if (lean_obj_tag(v_x_6137_) == 0)
{
lean_object* v_a_6139_; lean_object* v___x_6141_; uint8_t v_isShared_6142_; uint8_t v_isSharedCheck_6147_; 
lean_dec_ref(v___f_6136_);
lean_dec_ref(v_responseBodyInstance_6135_);
lean_dec_ref(v___f_6134_);
lean_dec(v_handler_6133_);
lean_dec_ref(v_h_6132_);
lean_dec_ref(v_a_6131_);
lean_dec_ref(v_connectionContext_6130_);
lean_dec(v_lingeringTimeout_6129_);
lean_dec(v_socket_6128_);
lean_dec(v_maximumRecvSize_6127_);
lean_dec_ref(v_inst_6126_);
v_a_6139_ = lean_ctor_get(v_x_6137_, 0);
v_isSharedCheck_6147_ = !lean_is_exclusive(v_x_6137_);
if (v_isSharedCheck_6147_ == 0)
{
v___x_6141_ = v_x_6137_;
v_isShared_6142_ = v_isSharedCheck_6147_;
goto v_resetjp_6140_;
}
else
{
lean_inc(v_a_6139_);
lean_dec(v_x_6137_);
v___x_6141_ = lean_box(0);
v_isShared_6142_ = v_isSharedCheck_6147_;
goto v_resetjp_6140_;
}
v_resetjp_6140_:
{
lean_object* v___x_6144_; 
if (v_isShared_6142_ == 0)
{
v___x_6144_ = v___x_6141_;
goto v_reusejp_6143_;
}
else
{
lean_object* v_reuseFailAlloc_6146_; 
v_reuseFailAlloc_6146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6146_, 0, v_a_6139_);
v___x_6144_ = v_reuseFailAlloc_6146_;
goto v_reusejp_6143_;
}
v_reusejp_6143_:
{
lean_object* v___x_6145_; 
v___x_6145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6145_, 0, v___x_6144_);
return v___x_6145_;
}
}
}
else
{
lean_object* v_a_6148_; lean_object* v_close_6149_; lean_object* v___f_6150_; lean_object* v___f_6151_; lean_object* v___f_6152_; lean_object* v___f_6153_; lean_object* v___f_6154_; lean_object* v___f_6155_; lean_object* v___f_6156_; lean_object* v___f_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___f_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; uint8_t v___x_6164_; lean_object* v___x_6165_; lean_object* v___y_6167_; 
v_a_6148_ = lean_ctor_get(v_x_6137_, 0);
lean_inc_n(v_a_6148_, 4);
lean_dec_ref_known(v_x_6137_, 1);
v_close_6149_ = lean_ctor_get(v_inst_6126_, 3);
lean_inc_ref(v_close_6149_);
lean_inc(v_socket_6128_);
v___f_6150_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 8, 6);
lean_closure_set(v___f_6150_, 0, v_a_6148_);
lean_closure_set(v___f_6150_, 1, v_maximumRecvSize_6127_);
lean_closure_set(v___f_6150_, 2, v_inst_6126_);
lean_closure_set(v___f_6150_, 3, v_socket_6128_);
lean_closure_set(v___f_6150_, 4, v_lingeringTimeout_6129_);
lean_closure_set(v___f_6150_, 5, v_connectionContext_6130_);
lean_inc_ref_n(v_a_6131_, 2);
v___f_6151_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 4, 2);
lean_closure_set(v___f_6151_, 0, v_a_6131_);
lean_closure_set(v___f_6151_, 1, v___f_6150_);
v___f_6152_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 6, 4);
lean_closure_set(v___f_6152_, 0, v_h_6132_);
lean_closure_set(v___f_6152_, 1, v_handler_6133_);
lean_closure_set(v___f_6152_, 2, v_a_6131_);
lean_closure_set(v___f_6152_, 3, v___f_6151_);
v___f_6153_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 4, 2);
lean_closure_set(v___f_6153_, 0, v_a_6131_);
lean_closure_set(v___f_6153_, 1, v___f_6152_);
lean_inc_ref(v___f_6153_);
v___f_6154_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 3, 1);
lean_closure_set(v___f_6154_, 0, v___f_6153_);
v___f_6155_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 6, 4);
lean_closure_set(v___f_6155_, 0, v_a_6148_);
lean_closure_set(v___f_6155_, 1, v___f_6134_);
lean_closure_set(v___f_6155_, 2, v___f_6154_);
lean_closure_set(v___f_6155_, 3, v___f_6153_);
lean_inc_ref(v___f_6155_);
v___f_6156_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 3, 1);
lean_closure_set(v___f_6156_, 0, v___f_6155_);
v___f_6157_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__21___boxed), 6, 4);
lean_closure_set(v___f_6157_, 0, v_a_6148_);
lean_closure_set(v___f_6157_, 1, v_responseBodyInstance_6135_);
lean_closure_set(v___f_6157_, 2, v___f_6156_);
lean_closure_set(v___f_6157_, 3, v___f_6155_);
v___x_6158_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___closed__0));
v___x_6159_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___boxed), 4, 3);
lean_closure_set(v___x_6159_, 0, lean_box(0));
lean_closure_set(v___x_6159_, 1, v_a_6148_);
lean_closure_set(v___x_6159_, 2, v___x_6158_);
v___x_6160_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___boxed), 6, 5);
lean_closure_set(v___x_6160_, 0, lean_box(0));
lean_closure_set(v___x_6160_, 1, lean_box(0));
lean_closure_set(v___x_6160_, 2, lean_box(0));
lean_closure_set(v___x_6160_, 3, v___x_6159_);
lean_closure_set(v___x_6160_, 4, v___f_6157_);
v___f_6161_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__23___boxed), 4, 2);
lean_closure_set(v___f_6161_, 0, v_close_6149_);
lean_closure_set(v___f_6161_, 1, v_socket_6128_);
v___x_6162_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_6162_, 0, lean_box(0));
lean_closure_set(v___x_6162_, 1, lean_box(0));
lean_closure_set(v___x_6162_, 2, lean_box(0));
lean_closure_set(v___x_6162_, 3, v___f_6136_);
v___x_6163_ = lean_unsigned_to_nat(0u);
v___x_6164_ = 0;
v___x_6165_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_6160_, v___f_6161_, v___x_6163_, v___x_6164_);
if (lean_obj_tag(v___x_6165_) == 0)
{
lean_object* v_a_6169_; 
lean_dec_ref(v___x_6162_);
v_a_6169_ = lean_ctor_get(v___x_6165_, 0);
lean_inc(v_a_6169_);
lean_dec_ref_known(v___x_6165_, 1);
if (lean_obj_tag(v_a_6169_) == 0)
{
lean_object* v_a_6170_; lean_object* v___x_6172_; uint8_t v_isShared_6173_; uint8_t v_isSharedCheck_6177_; 
v_a_6170_ = lean_ctor_get(v_a_6169_, 0);
v_isSharedCheck_6177_ = !lean_is_exclusive(v_a_6169_);
if (v_isSharedCheck_6177_ == 0)
{
v___x_6172_ = v_a_6169_;
v_isShared_6173_ = v_isSharedCheck_6177_;
goto v_resetjp_6171_;
}
else
{
lean_inc(v_a_6170_);
lean_dec(v_a_6169_);
v___x_6172_ = lean_box(0);
v_isShared_6173_ = v_isSharedCheck_6177_;
goto v_resetjp_6171_;
}
v_resetjp_6171_:
{
lean_object* v___x_6175_; 
if (v_isShared_6173_ == 0)
{
v___x_6175_ = v___x_6172_;
goto v_reusejp_6174_;
}
else
{
lean_object* v_reuseFailAlloc_6176_; 
v_reuseFailAlloc_6176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6176_, 0, v_a_6170_);
v___x_6175_ = v_reuseFailAlloc_6176_;
goto v_reusejp_6174_;
}
v_reusejp_6174_:
{
v___y_6167_ = v___x_6175_;
goto v___jp_6166_;
}
}
}
else
{
lean_object* v_a_6178_; lean_object* v___x_6180_; uint8_t v_isShared_6181_; uint8_t v_isSharedCheck_6186_; 
v_a_6178_ = lean_ctor_get(v_a_6169_, 0);
v_isSharedCheck_6186_ = !lean_is_exclusive(v_a_6169_);
if (v_isSharedCheck_6186_ == 0)
{
v___x_6180_ = v_a_6169_;
v_isShared_6181_ = v_isSharedCheck_6186_;
goto v_resetjp_6179_;
}
else
{
lean_inc(v_a_6178_);
lean_dec(v_a_6169_);
v___x_6180_ = lean_box(0);
v_isShared_6181_ = v_isSharedCheck_6186_;
goto v_resetjp_6179_;
}
v_resetjp_6179_:
{
lean_object* v_fst_6182_; lean_object* v___x_6184_; 
v_fst_6182_ = lean_ctor_get(v_a_6178_, 0);
lean_inc(v_fst_6182_);
lean_dec(v_a_6178_);
if (v_isShared_6181_ == 0)
{
lean_ctor_set(v___x_6180_, 0, v_fst_6182_);
v___x_6184_ = v___x_6180_;
goto v_reusejp_6183_;
}
else
{
lean_object* v_reuseFailAlloc_6185_; 
v_reuseFailAlloc_6185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6185_, 0, v_fst_6182_);
v___x_6184_ = v_reuseFailAlloc_6185_;
goto v_reusejp_6183_;
}
v_reusejp_6183_:
{
v___y_6167_ = v___x_6184_;
goto v___jp_6166_;
}
}
}
}
else
{
lean_object* v_a_6187_; lean_object* v___x_6189_; uint8_t v_isShared_6190_; uint8_t v_isSharedCheck_6195_; 
v_a_6187_ = lean_ctor_get(v___x_6165_, 0);
v_isSharedCheck_6195_ = !lean_is_exclusive(v___x_6165_);
if (v_isSharedCheck_6195_ == 0)
{
v___x_6189_ = v___x_6165_;
v_isShared_6190_ = v_isSharedCheck_6195_;
goto v_resetjp_6188_;
}
else
{
lean_inc(v_a_6187_);
lean_dec(v___x_6165_);
v___x_6189_ = lean_box(0);
v_isShared_6190_ = v_isSharedCheck_6195_;
goto v_resetjp_6188_;
}
v_resetjp_6188_:
{
lean_object* v___x_6191_; lean_object* v___x_6193_; 
v___x_6191_ = lean_task_map(v___x_6162_, v_a_6187_, v___x_6163_, v___x_6164_);
if (v_isShared_6190_ == 0)
{
lean_ctor_set(v___x_6189_, 0, v___x_6191_);
v___x_6193_ = v___x_6189_;
goto v_reusejp_6192_;
}
else
{
lean_object* v_reuseFailAlloc_6194_; 
v_reuseFailAlloc_6194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6194_, 0, v___x_6191_);
v___x_6193_ = v_reuseFailAlloc_6194_;
goto v_reusejp_6192_;
}
v_reusejp_6192_:
{
return v___x_6193_;
}
}
}
v___jp_6166_:
{
lean_object* v___x_6168_; 
v___x_6168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6168_, 0, v___y_6167_);
return v___x_6168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___boxed(lean_object* v_inst_6196_, lean_object* v_maximumRecvSize_6197_, lean_object* v_socket_6198_, lean_object* v_lingeringTimeout_6199_, lean_object* v_connectionContext_6200_, lean_object* v_a_6201_, lean_object* v_h_6202_, lean_object* v_handler_6203_, lean_object* v___f_6204_, lean_object* v_responseBodyInstance_6205_, lean_object* v___f_6206_, lean_object* v_x_6207_, lean_object* v___y_6208_){
_start:
{
lean_object* v_res_6209_; 
v_res_6209_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24(v_inst_6196_, v_maximumRecvSize_6197_, v_socket_6198_, v_lingeringTimeout_6199_, v_connectionContext_6200_, v_a_6201_, v_h_6202_, v_handler_6203_, v___f_6204_, v_responseBodyInstance_6205_, v___f_6206_, v_x_6207_);
return v_res_6209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__25(lean_object* v_a_6210_, lean_object* v_x_6211_){
_start:
{
if (lean_obj_tag(v_x_6211_) == 0)
{
lean_object* v_a_6213_; lean_object* v___x_6215_; uint8_t v_isShared_6216_; uint8_t v_isSharedCheck_6221_; 
v_a_6213_ = lean_ctor_get(v_x_6211_, 0);
v_isSharedCheck_6221_ = !lean_is_exclusive(v_x_6211_);
if (v_isSharedCheck_6221_ == 0)
{
v___x_6215_ = v_x_6211_;
v_isShared_6216_ = v_isSharedCheck_6221_;
goto v_resetjp_6214_;
}
else
{
lean_inc(v_a_6213_);
lean_dec(v_x_6211_);
v___x_6215_ = lean_box(0);
v_isShared_6216_ = v_isSharedCheck_6221_;
goto v_resetjp_6214_;
}
v_resetjp_6214_:
{
lean_object* v___x_6218_; 
if (v_isShared_6216_ == 0)
{
v___x_6218_ = v___x_6215_;
goto v_reusejp_6217_;
}
else
{
lean_object* v_reuseFailAlloc_6220_; 
v_reuseFailAlloc_6220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6220_, 0, v_a_6213_);
v___x_6218_ = v_reuseFailAlloc_6220_;
goto v_reusejp_6217_;
}
v_reusejp_6217_:
{
lean_object* v___x_6219_; 
v___x_6219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6219_, 0, v___x_6218_);
return v___x_6219_;
}
}
}
else
{
lean_object* v___x_6222_; lean_object* v___x_6223_; 
lean_dec_ref_known(v_x_6211_, 1);
v___x_6222_ = l_IO_Promise_result_x21___redArg(v_a_6210_);
v___x_6223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6223_, 0, v___x_6222_);
return v___x_6223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__25___boxed(lean_object* v_a_6224_, lean_object* v_x_6225_, lean_object* v___y_6226_){
_start:
{
lean_object* v_res_6227_; 
v_res_6227_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__25(v_a_6224_, v_x_6225_);
lean_dec(v_a_6224_);
return v_res_6227_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__26(lean_object* v___f_6228_, lean_object* v___x_6229_, lean_object* v___x_6230_, uint8_t v___x_6231_, lean_object* v_x_6232_){
_start:
{
if (lean_obj_tag(v_x_6232_) == 0)
{
lean_object* v_a_6234_; lean_object* v___x_6236_; uint8_t v_isShared_6237_; uint8_t v_isSharedCheck_6242_; 
lean_dec_ref(v___x_6230_);
lean_dec(v___x_6229_);
lean_dec_ref(v___f_6228_);
v_a_6234_ = lean_ctor_get(v_x_6232_, 0);
v_isSharedCheck_6242_ = !lean_is_exclusive(v_x_6232_);
if (v_isSharedCheck_6242_ == 0)
{
v___x_6236_ = v_x_6232_;
v_isShared_6237_ = v_isSharedCheck_6242_;
goto v_resetjp_6235_;
}
else
{
lean_inc(v_a_6234_);
lean_dec(v_x_6232_);
v___x_6236_ = lean_box(0);
v_isShared_6237_ = v_isSharedCheck_6242_;
goto v_resetjp_6235_;
}
v_resetjp_6235_:
{
lean_object* v___x_6239_; 
if (v_isShared_6237_ == 0)
{
v___x_6239_ = v___x_6236_;
goto v_reusejp_6238_;
}
else
{
lean_object* v_reuseFailAlloc_6241_; 
v_reuseFailAlloc_6241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6241_, 0, v_a_6234_);
v___x_6239_ = v_reuseFailAlloc_6241_;
goto v_reusejp_6238_;
}
v_reusejp_6238_:
{
lean_object* v___x_6240_; 
v___x_6240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6240_, 0, v___x_6239_);
return v___x_6240_;
}
}
}
else
{
lean_object* v_a_6243_; lean_object* v___x_6245_; uint8_t v_isShared_6246_; uint8_t v_isSharedCheck_6254_; 
v_a_6243_ = lean_ctor_get(v_x_6232_, 0);
v_isSharedCheck_6254_ = !lean_is_exclusive(v_x_6232_);
if (v_isSharedCheck_6254_ == 0)
{
v___x_6245_ = v_x_6232_;
v_isShared_6246_ = v_isSharedCheck_6254_;
goto v_resetjp_6244_;
}
else
{
lean_inc(v_a_6243_);
lean_dec(v_x_6232_);
v___x_6245_ = lean_box(0);
v_isShared_6246_ = v_isSharedCheck_6254_;
goto v_resetjp_6244_;
}
v_resetjp_6244_:
{
lean_object* v___f_6247_; lean_object* v___x_6248_; lean_object* v___x_6250_; 
lean_inc(v_a_6243_);
v___f_6247_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__25___boxed), 3, 1);
lean_closure_set(v___f_6247_, 0, v_a_6243_);
lean_inc(v___x_6229_);
v___x_6248_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_6228_, v___x_6229_, v_a_6243_, v___x_6230_);
if (v_isShared_6246_ == 0)
{
lean_ctor_set(v___x_6245_, 0, v___x_6248_);
v___x_6250_ = v___x_6245_;
goto v_reusejp_6249_;
}
else
{
lean_object* v_reuseFailAlloc_6253_; 
v_reuseFailAlloc_6253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6253_, 0, v___x_6248_);
v___x_6250_ = v_reuseFailAlloc_6253_;
goto v_reusejp_6249_;
}
v_reusejp_6249_:
{
lean_object* v___x_6251_; lean_object* v___x_6252_; 
v___x_6251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6251_, 0, v___x_6250_);
v___x_6252_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6229_, v___x_6231_, v___x_6251_, v___f_6247_);
return v___x_6252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__26___boxed(lean_object* v___f_6255_, lean_object* v___x_6256_, lean_object* v___x_6257_, lean_object* v___x_6258_, lean_object* v_x_6259_, lean_object* v___y_6260_){
_start:
{
uint8_t v___x_10147__boxed_6261_; lean_object* v_res_6262_; 
v___x_10147__boxed_6261_ = lean_unbox(v___x_6258_);
v_res_6262_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__26(v___f_6255_, v___x_6256_, v___x_6257_, v___x_10147__boxed_6261_, v_x_6259_);
return v_res_6262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__27(lean_object* v_h_6263_, lean_object* v_handler_6264_, lean_object* v___x_6265_, lean_object* v_responseBodyInstance_6266_, lean_object* v_config_6267_, lean_object* v___f_6268_, lean_object* v_keepAliveTimeout_6269_, lean_object* v_inst_6270_, lean_object* v_socket_6271_, lean_object* v_connectionContext_6272_, lean_object* v_maximumRecvSize_6273_, lean_object* v_extensions_6274_, lean_object* v___f_6275_, lean_object* v_lingeringTimeout_6276_, lean_object* v___f_6277_, lean_object* v___f_6278_, lean_object* v___x_6279_, lean_object* v_x_6280_){
_start:
{
if (lean_obj_tag(v_x_6280_) == 0)
{
lean_object* v_a_6282_; lean_object* v___x_6284_; uint8_t v_isShared_6285_; uint8_t v_isSharedCheck_6290_; 
lean_dec_ref(v___x_6279_);
lean_dec_ref(v___f_6278_);
lean_dec_ref(v___f_6277_);
lean_dec(v_lingeringTimeout_6276_);
lean_dec_ref(v___f_6275_);
lean_dec(v_extensions_6274_);
lean_dec(v_maximumRecvSize_6273_);
lean_dec_ref(v_connectionContext_6272_);
lean_dec(v_socket_6271_);
lean_dec_ref(v_inst_6270_);
lean_dec(v_keepAliveTimeout_6269_);
lean_dec_ref(v___f_6268_);
lean_dec_ref(v_config_6267_);
lean_dec_ref(v_responseBodyInstance_6266_);
lean_dec(v___x_6265_);
lean_dec(v_handler_6264_);
lean_dec_ref(v_h_6263_);
v_a_6282_ = lean_ctor_get(v_x_6280_, 0);
v_isSharedCheck_6290_ = !lean_is_exclusive(v_x_6280_);
if (v_isSharedCheck_6290_ == 0)
{
v___x_6284_ = v_x_6280_;
v_isShared_6285_ = v_isSharedCheck_6290_;
goto v_resetjp_6283_;
}
else
{
lean_inc(v_a_6282_);
lean_dec(v_x_6280_);
v___x_6284_ = lean_box(0);
v_isShared_6285_ = v_isSharedCheck_6290_;
goto v_resetjp_6283_;
}
v_resetjp_6283_:
{
lean_object* v___x_6287_; 
if (v_isShared_6285_ == 0)
{
v___x_6287_ = v___x_6284_;
goto v_reusejp_6286_;
}
else
{
lean_object* v_reuseFailAlloc_6289_; 
v_reuseFailAlloc_6289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6289_, 0, v_a_6282_);
v___x_6287_ = v_reuseFailAlloc_6289_;
goto v_reusejp_6286_;
}
v_reusejp_6286_:
{
lean_object* v___x_6288_; 
v___x_6288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6288_, 0, v___x_6287_);
return v___x_6288_;
}
}
}
else
{
lean_object* v_a_6291_; lean_object* v___x_6293_; uint8_t v_isShared_6294_; uint8_t v_isSharedCheck_6308_; 
v_a_6291_ = lean_ctor_get(v_x_6280_, 0);
v_isSharedCheck_6308_ = !lean_is_exclusive(v_x_6280_);
if (v_isSharedCheck_6308_ == 0)
{
v___x_6293_ = v_x_6280_;
v_isShared_6294_ = v_isSharedCheck_6308_;
goto v_resetjp_6292_;
}
else
{
lean_inc(v_a_6291_);
lean_dec(v_x_6280_);
v___x_6293_ = lean_box(0);
v_isShared_6294_ = v_isSharedCheck_6308_;
goto v_resetjp_6292_;
}
v_resetjp_6292_:
{
lean_object* v___f_6295_; lean_object* v___f_6296_; lean_object* v___x_6297_; uint8_t v___x_6298_; lean_object* v___x_6299_; lean_object* v___f_6300_; lean_object* v___x_6301_; lean_object* v___x_6303_; 
lean_inc(v_maximumRecvSize_6273_);
lean_inc_ref(v_connectionContext_6272_);
lean_inc(v_socket_6271_);
lean_inc_ref(v_inst_6270_);
lean_inc_ref(v_responseBodyInstance_6266_);
lean_inc(v_a_6291_);
lean_inc(v_handler_6264_);
lean_inc_ref(v_h_6263_);
v___f_6295_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 17, 14);
lean_closure_set(v___f_6295_, 0, v_h_6263_);
lean_closure_set(v___f_6295_, 1, v_handler_6264_);
lean_closure_set(v___f_6295_, 2, v_a_6291_);
lean_closure_set(v___f_6295_, 3, v___x_6265_);
lean_closure_set(v___f_6295_, 4, v_responseBodyInstance_6266_);
lean_closure_set(v___f_6295_, 5, v_config_6267_);
lean_closure_set(v___f_6295_, 6, v___f_6268_);
lean_closure_set(v___f_6295_, 7, v_keepAliveTimeout_6269_);
lean_closure_set(v___f_6295_, 8, v_inst_6270_);
lean_closure_set(v___f_6295_, 9, v_socket_6271_);
lean_closure_set(v___f_6295_, 10, v_connectionContext_6272_);
lean_closure_set(v___f_6295_, 11, v_maximumRecvSize_6273_);
lean_closure_set(v___f_6295_, 12, v_extensions_6274_);
lean_closure_set(v___f_6295_, 13, v___f_6275_);
v___f_6296_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___boxed), 13, 11);
lean_closure_set(v___f_6296_, 0, v_inst_6270_);
lean_closure_set(v___f_6296_, 1, v_maximumRecvSize_6273_);
lean_closure_set(v___f_6296_, 2, v_socket_6271_);
lean_closure_set(v___f_6296_, 3, v_lingeringTimeout_6276_);
lean_closure_set(v___f_6296_, 4, v_connectionContext_6272_);
lean_closure_set(v___f_6296_, 5, v_a_6291_);
lean_closure_set(v___f_6296_, 6, v_h_6263_);
lean_closure_set(v___f_6296_, 7, v_handler_6264_);
lean_closure_set(v___f_6296_, 8, v___f_6277_);
lean_closure_set(v___f_6296_, 9, v_responseBodyInstance_6266_);
lean_closure_set(v___f_6296_, 10, v___f_6278_);
v___x_6297_ = lean_unsigned_to_nat(0u);
v___x_6298_ = 0;
v___x_6299_ = lean_box(v___x_6298_);
v___f_6300_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__26___boxed), 6, 4);
lean_closure_set(v___f_6300_, 0, v___f_6295_);
lean_closure_set(v___f_6300_, 1, v___x_6297_);
lean_closure_set(v___f_6300_, 2, v___x_6279_);
lean_closure_set(v___f_6300_, 3, v___x_6299_);
v___x_6301_ = lean_io_promise_new();
if (v_isShared_6294_ == 0)
{
lean_ctor_set(v___x_6293_, 0, v___x_6301_);
v___x_6303_ = v___x_6293_;
goto v_reusejp_6302_;
}
else
{
lean_object* v_reuseFailAlloc_6307_; 
v_reuseFailAlloc_6307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6307_, 0, v___x_6301_);
v___x_6303_ = v_reuseFailAlloc_6307_;
goto v_reusejp_6302_;
}
v_reusejp_6302_:
{
lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; 
v___x_6304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6304_, 0, v___x_6303_);
v___x_6305_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6297_, v___x_6298_, v___x_6304_, v___f_6300_);
v___x_6306_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6297_, v___x_6298_, v___x_6305_, v___f_6296_);
return v___x_6306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__27___boxed(lean_object** _args){
lean_object* v_h_6309_ = _args[0];
lean_object* v_handler_6310_ = _args[1];
lean_object* v___x_6311_ = _args[2];
lean_object* v_responseBodyInstance_6312_ = _args[3];
lean_object* v_config_6313_ = _args[4];
lean_object* v___f_6314_ = _args[5];
lean_object* v_keepAliveTimeout_6315_ = _args[6];
lean_object* v_inst_6316_ = _args[7];
lean_object* v_socket_6317_ = _args[8];
lean_object* v_connectionContext_6318_ = _args[9];
lean_object* v_maximumRecvSize_6319_ = _args[10];
lean_object* v_extensions_6320_ = _args[11];
lean_object* v___f_6321_ = _args[12];
lean_object* v_lingeringTimeout_6322_ = _args[13];
lean_object* v___f_6323_ = _args[14];
lean_object* v___f_6324_ = _args[15];
lean_object* v___x_6325_ = _args[16];
lean_object* v_x_6326_ = _args[17];
lean_object* v___y_6327_ = _args[18];
_start:
{
lean_object* v_res_6328_; 
v_res_6328_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__27(v_h_6309_, v_handler_6310_, v___x_6311_, v_responseBodyInstance_6312_, v_config_6313_, v___f_6314_, v_keepAliveTimeout_6315_, v_inst_6316_, v_socket_6317_, v_connectionContext_6318_, v_maximumRecvSize_6319_, v_extensions_6320_, v___f_6321_, v_lingeringTimeout_6322_, v___f_6323_, v___f_6324_, v___x_6325_, v_x_6326_);
return v_res_6328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__28(lean_object* v_config_6329_, lean_object* v_machine_6330_, lean_object* v_a_6331_, lean_object* v_h_6332_, lean_object* v_handler_6333_, lean_object* v_responseBodyInstance_6334_, lean_object* v___f_6335_, lean_object* v_inst_6336_, lean_object* v_socket_6337_, lean_object* v_connectionContext_6338_, lean_object* v_extensions_6339_, lean_object* v___f_6340_, lean_object* v___f_6341_, lean_object* v___f_6342_, lean_object* v_x_6343_){
_start:
{
if (lean_obj_tag(v_x_6343_) == 0)
{
lean_object* v_a_6345_; lean_object* v___x_6347_; uint8_t v_isShared_6348_; uint8_t v_isSharedCheck_6353_; 
lean_dec_ref(v___f_6342_);
lean_dec_ref(v___f_6341_);
lean_dec_ref(v___f_6340_);
lean_dec(v_extensions_6339_);
lean_dec_ref(v_connectionContext_6338_);
lean_dec(v_socket_6337_);
lean_dec_ref(v_inst_6336_);
lean_dec_ref(v___f_6335_);
lean_dec_ref(v_responseBodyInstance_6334_);
lean_dec(v_handler_6333_);
lean_dec_ref(v_h_6332_);
lean_dec_ref(v_a_6331_);
lean_dec_ref(v_machine_6330_);
lean_dec_ref(v_config_6329_);
v_a_6345_ = lean_ctor_get(v_x_6343_, 0);
v_isSharedCheck_6353_ = !lean_is_exclusive(v_x_6343_);
if (v_isSharedCheck_6353_ == 0)
{
v___x_6347_ = v_x_6343_;
v_isShared_6348_ = v_isSharedCheck_6353_;
goto v_resetjp_6346_;
}
else
{
lean_inc(v_a_6345_);
lean_dec(v_x_6343_);
v___x_6347_ = lean_box(0);
v_isShared_6348_ = v_isSharedCheck_6353_;
goto v_resetjp_6346_;
}
v_resetjp_6346_:
{
lean_object* v___x_6350_; 
if (v_isShared_6348_ == 0)
{
v___x_6350_ = v___x_6347_;
goto v_reusejp_6349_;
}
else
{
lean_object* v_reuseFailAlloc_6352_; 
v_reuseFailAlloc_6352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6352_, 0, v_a_6345_);
v___x_6350_ = v_reuseFailAlloc_6352_;
goto v_reusejp_6349_;
}
v_reusejp_6349_:
{
lean_object* v___x_6351_; 
v___x_6351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6351_, 0, v___x_6350_);
return v___x_6351_;
}
}
}
else
{
lean_object* v_a_6354_; lean_object* v___x_6356_; uint8_t v_isShared_6357_; uint8_t v_isSharedCheck_6377_; 
v_a_6354_ = lean_ctor_get(v_x_6343_, 0);
v_isSharedCheck_6377_ = !lean_is_exclusive(v_x_6343_);
if (v_isSharedCheck_6377_ == 0)
{
v___x_6356_ = v_x_6343_;
v_isShared_6357_ = v_isSharedCheck_6377_;
goto v_resetjp_6355_;
}
else
{
lean_inc(v_a_6354_);
lean_dec(v_x_6343_);
v___x_6356_ = lean_box(0);
v_isShared_6357_ = v_isSharedCheck_6377_;
goto v_resetjp_6355_;
}
v_resetjp_6355_:
{
lean_object* v_lingeringTimeout_6358_; lean_object* v_keepAliveTimeout_6359_; lean_object* v_writeTimeout_6360_; lean_object* v_maximumRecvSize_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; lean_object* v___x_6364_; uint8_t v___x_6365_; lean_object* v___x_6366_; lean_object* v___f_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; uint8_t v___x_6370_; lean_object* v___x_6371_; lean_object* v___x_6373_; 
v_lingeringTimeout_6358_ = lean_ctor_get(v_config_6329_, 4);
lean_inc(v_lingeringTimeout_6358_);
v_keepAliveTimeout_6359_ = lean_ctor_get(v_config_6329_, 5);
lean_inc_n(v_keepAliveTimeout_6359_, 2);
v_writeTimeout_6360_ = lean_ctor_get(v_config_6329_, 7);
lean_inc(v_writeTimeout_6360_);
v_maximumRecvSize_6361_ = lean_ctor_get(v_config_6329_, 8);
lean_inc(v_maximumRecvSize_6361_);
v___x_6362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6362_, 0, v_keepAliveTimeout_6359_);
v___x_6363_ = lean_box(0);
v___x_6364_ = lean_box(0);
v___x_6365_ = 1;
v___x_6366_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_6366_, 0, v_machine_6330_);
lean_ctor_set(v___x_6366_, 1, v_a_6331_);
lean_ctor_set(v___x_6366_, 2, v___x_6362_);
lean_ctor_set(v___x_6366_, 3, v_a_6354_);
lean_ctor_set(v___x_6366_, 4, v___x_6363_);
lean_ctor_set(v___x_6366_, 5, v___x_6363_);
lean_ctor_set(v___x_6366_, 6, v___x_6364_);
lean_ctor_set(v___x_6366_, 7, v___x_6363_);
lean_ctor_set(v___x_6366_, 8, v___x_6363_);
lean_ctor_set_uint8(v___x_6366_, sizeof(void*)*9, v___x_6365_);
lean_inc(v_socket_6337_);
v___f_6367_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__27___boxed), 19, 17);
lean_closure_set(v___f_6367_, 0, v_h_6332_);
lean_closure_set(v___f_6367_, 1, v_handler_6333_);
lean_closure_set(v___f_6367_, 2, v___x_6363_);
lean_closure_set(v___f_6367_, 3, v_responseBodyInstance_6334_);
lean_closure_set(v___f_6367_, 4, v_config_6329_);
lean_closure_set(v___f_6367_, 5, v___f_6335_);
lean_closure_set(v___f_6367_, 6, v_keepAliveTimeout_6359_);
lean_closure_set(v___f_6367_, 7, v_inst_6336_);
lean_closure_set(v___f_6367_, 8, v_socket_6337_);
lean_closure_set(v___f_6367_, 9, v_connectionContext_6338_);
lean_closure_set(v___f_6367_, 10, v_maximumRecvSize_6361_);
lean_closure_set(v___f_6367_, 11, v_extensions_6339_);
lean_closure_set(v___f_6367_, 12, v___f_6340_);
lean_closure_set(v___f_6367_, 13, v_lingeringTimeout_6358_);
lean_closure_set(v___f_6367_, 14, v___f_6341_);
lean_closure_set(v___f_6367_, 15, v___f_6342_);
lean_closure_set(v___f_6367_, 16, v___x_6366_);
v___x_6368_ = l_Int_toNat(v_writeTimeout_6360_);
lean_dec(v_writeTimeout_6360_);
v___x_6369_ = lean_unsigned_to_nat(0u);
v___x_6370_ = 0;
v___x_6371_ = l_Std_Http_Internal_Outbox_new___redArg(v_socket_6337_, v___x_6368_);
if (v_isShared_6357_ == 0)
{
lean_ctor_set(v___x_6356_, 0, v___x_6371_);
v___x_6373_ = v___x_6356_;
goto v_reusejp_6372_;
}
else
{
lean_object* v_reuseFailAlloc_6376_; 
v_reuseFailAlloc_6376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6376_, 0, v___x_6371_);
v___x_6373_ = v_reuseFailAlloc_6376_;
goto v_reusejp_6372_;
}
v_reusejp_6372_:
{
lean_object* v___x_6374_; lean_object* v___x_6375_; 
v___x_6374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6374_, 0, v___x_6373_);
v___x_6375_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6369_, v___x_6370_, v___x_6374_, v___f_6367_);
return v___x_6375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__28___boxed(lean_object* v_config_6378_, lean_object* v_machine_6379_, lean_object* v_a_6380_, lean_object* v_h_6381_, lean_object* v_handler_6382_, lean_object* v_responseBodyInstance_6383_, lean_object* v___f_6384_, lean_object* v_inst_6385_, lean_object* v_socket_6386_, lean_object* v_connectionContext_6387_, lean_object* v_extensions_6388_, lean_object* v___f_6389_, lean_object* v___f_6390_, lean_object* v___f_6391_, lean_object* v_x_6392_, lean_object* v___y_6393_){
_start:
{
lean_object* v_res_6394_; 
v_res_6394_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__28(v_config_6378_, v_machine_6379_, v_a_6380_, v_h_6381_, v_handler_6382_, v_responseBodyInstance_6383_, v___f_6384_, v_inst_6385_, v_socket_6386_, v_connectionContext_6387_, v_extensions_6388_, v___f_6389_, v___f_6390_, v___f_6391_, v_x_6392_);
return v_res_6394_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__29(lean_object* v_config_6395_, lean_object* v_machine_6396_, lean_object* v_h_6397_, lean_object* v_handler_6398_, lean_object* v_responseBodyInstance_6399_, lean_object* v___f_6400_, lean_object* v_inst_6401_, lean_object* v_socket_6402_, lean_object* v_connectionContext_6403_, lean_object* v_extensions_6404_, lean_object* v___f_6405_, lean_object* v___f_6406_, lean_object* v___f_6407_, lean_object* v_x_6408_){
_start:
{
if (lean_obj_tag(v_x_6408_) == 0)
{
lean_object* v_a_6410_; lean_object* v___x_6412_; uint8_t v_isShared_6413_; uint8_t v_isSharedCheck_6418_; 
lean_dec_ref(v___f_6407_);
lean_dec_ref(v___f_6406_);
lean_dec_ref(v___f_6405_);
lean_dec(v_extensions_6404_);
lean_dec_ref(v_connectionContext_6403_);
lean_dec(v_socket_6402_);
lean_dec_ref(v_inst_6401_);
lean_dec_ref(v___f_6400_);
lean_dec_ref(v_responseBodyInstance_6399_);
lean_dec(v_handler_6398_);
lean_dec_ref(v_h_6397_);
lean_dec_ref(v_machine_6396_);
lean_dec_ref(v_config_6395_);
v_a_6410_ = lean_ctor_get(v_x_6408_, 0);
v_isSharedCheck_6418_ = !lean_is_exclusive(v_x_6408_);
if (v_isSharedCheck_6418_ == 0)
{
v___x_6412_ = v_x_6408_;
v_isShared_6413_ = v_isSharedCheck_6418_;
goto v_resetjp_6411_;
}
else
{
lean_inc(v_a_6410_);
lean_dec(v_x_6408_);
v___x_6412_ = lean_box(0);
v_isShared_6413_ = v_isSharedCheck_6418_;
goto v_resetjp_6411_;
}
v_resetjp_6411_:
{
lean_object* v___x_6415_; 
if (v_isShared_6413_ == 0)
{
v___x_6415_ = v___x_6412_;
goto v_reusejp_6414_;
}
else
{
lean_object* v_reuseFailAlloc_6417_; 
v_reuseFailAlloc_6417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6417_, 0, v_a_6410_);
v___x_6415_ = v_reuseFailAlloc_6417_;
goto v_reusejp_6414_;
}
v_reusejp_6414_:
{
lean_object* v___x_6416_; 
v___x_6416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6416_, 0, v___x_6415_);
return v___x_6416_;
}
}
}
else
{
lean_object* v_a_6419_; lean_object* v___x_6421_; uint8_t v_isShared_6422_; uint8_t v_isSharedCheck_6433_; 
v_a_6419_ = lean_ctor_get(v_x_6408_, 0);
v_isSharedCheck_6433_ = !lean_is_exclusive(v_x_6408_);
if (v_isSharedCheck_6433_ == 0)
{
v___x_6421_ = v_x_6408_;
v_isShared_6422_ = v_isSharedCheck_6433_;
goto v_resetjp_6420_;
}
else
{
lean_inc(v_a_6419_);
lean_dec(v_x_6408_);
v___x_6421_ = lean_box(0);
v_isShared_6422_ = v_isSharedCheck_6433_;
goto v_resetjp_6420_;
}
v_resetjp_6420_:
{
lean_object* v___f_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; uint8_t v___x_6426_; lean_object* v___x_6427_; lean_object* v___x_6429_; 
v___f_6423_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__28___boxed), 16, 14);
lean_closure_set(v___f_6423_, 0, v_config_6395_);
lean_closure_set(v___f_6423_, 1, v_machine_6396_);
lean_closure_set(v___f_6423_, 2, v_a_6419_);
lean_closure_set(v___f_6423_, 3, v_h_6397_);
lean_closure_set(v___f_6423_, 4, v_handler_6398_);
lean_closure_set(v___f_6423_, 5, v_responseBodyInstance_6399_);
lean_closure_set(v___f_6423_, 6, v___f_6400_);
lean_closure_set(v___f_6423_, 7, v_inst_6401_);
lean_closure_set(v___f_6423_, 8, v_socket_6402_);
lean_closure_set(v___f_6423_, 9, v_connectionContext_6403_);
lean_closure_set(v___f_6423_, 10, v_extensions_6404_);
lean_closure_set(v___f_6423_, 11, v___f_6405_);
lean_closure_set(v___f_6423_, 12, v___f_6406_);
lean_closure_set(v___f_6423_, 13, v___f_6407_);
v___x_6424_ = lean_box(0);
v___x_6425_ = lean_unsigned_to_nat(0u);
v___x_6426_ = 0;
v___x_6427_ = l_Std_CloseableChannel_new___redArg(v___x_6424_);
if (v_isShared_6422_ == 0)
{
lean_ctor_set(v___x_6421_, 0, v___x_6427_);
v___x_6429_ = v___x_6421_;
goto v_reusejp_6428_;
}
else
{
lean_object* v_reuseFailAlloc_6432_; 
v_reuseFailAlloc_6432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6432_, 0, v___x_6427_);
v___x_6429_ = v_reuseFailAlloc_6432_;
goto v_reusejp_6428_;
}
v_reusejp_6428_:
{
lean_object* v___x_6430_; lean_object* v___x_6431_; 
v___x_6430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6430_, 0, v___x_6429_);
v___x_6431_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6425_, v___x_6426_, v___x_6430_, v___f_6423_);
return v___x_6431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__29___boxed(lean_object* v_config_6434_, lean_object* v_machine_6435_, lean_object* v_h_6436_, lean_object* v_handler_6437_, lean_object* v_responseBodyInstance_6438_, lean_object* v___f_6439_, lean_object* v_inst_6440_, lean_object* v_socket_6441_, lean_object* v_connectionContext_6442_, lean_object* v_extensions_6443_, lean_object* v___f_6444_, lean_object* v___f_6445_, lean_object* v___f_6446_, lean_object* v_x_6447_, lean_object* v___y_6448_){
_start:
{
lean_object* v_res_6449_; 
v_res_6449_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__29(v_config_6434_, v_machine_6435_, v_h_6436_, v_handler_6437_, v_responseBodyInstance_6438_, v___f_6439_, v_inst_6440_, v_socket_6441_, v_connectionContext_6442_, v_extensions_6443_, v___f_6444_, v___f_6445_, v___f_6446_, v_x_6447_);
return v_res_6449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_6453_, lean_object* v_h_6454_, lean_object* v_connection_6455_, lean_object* v_config_6456_, lean_object* v_connectionContext_6457_, lean_object* v_handler_6458_){
_start:
{
lean_object* v_responseBodyInstance_6460_; lean_object* v_socket_6461_; lean_object* v_machine_6462_; lean_object* v_extensions_6463_; lean_object* v___f_6464_; lean_object* v___f_6465_; lean_object* v___f_6466_; lean_object* v___f_6467_; lean_object* v___f_6468_; lean_object* v___x_6469_; uint8_t v___x_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; 
v_responseBodyInstance_6460_ = lean_ctor_get(v_h_6454_, 0);
lean_inc_ref_n(v_responseBodyInstance_6460_, 2);
v_socket_6461_ = lean_ctor_get(v_connection_6455_, 0);
lean_inc(v_socket_6461_);
v_machine_6462_ = lean_ctor_get(v_connection_6455_, 1);
lean_inc_ref(v_machine_6462_);
v_extensions_6463_ = lean_ctor_get(v_connection_6455_, 2);
lean_inc(v_extensions_6463_);
lean_dec_ref(v_connection_6455_);
v___f_6464_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_6465_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_6466_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
v___f_6467_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_6467_, 0, v_responseBodyInstance_6460_);
v___f_6468_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__29___boxed), 15, 13);
lean_closure_set(v___f_6468_, 0, v_config_6456_);
lean_closure_set(v___f_6468_, 1, v_machine_6462_);
lean_closure_set(v___f_6468_, 2, v_h_6454_);
lean_closure_set(v___f_6468_, 3, v_handler_6458_);
lean_closure_set(v___f_6468_, 4, v_responseBodyInstance_6460_);
lean_closure_set(v___f_6468_, 5, v___f_6465_);
lean_closure_set(v___f_6468_, 6, v_inst_6453_);
lean_closure_set(v___f_6468_, 7, v_socket_6461_);
lean_closure_set(v___f_6468_, 8, v_connectionContext_6457_);
lean_closure_set(v___f_6468_, 9, v_extensions_6463_);
lean_closure_set(v___f_6468_, 10, v___f_6464_);
lean_closure_set(v___f_6468_, 11, v___f_6467_);
lean_closure_set(v___f_6468_, 12, v___f_6466_);
v___x_6469_ = lean_unsigned_to_nat(0u);
v___x_6470_ = 0;
v___x_6471_ = l_Std_Http_Body_mkStream();
v___x_6472_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6469_, v___x_6470_, v___x_6471_, v___f_6468_);
return v___x_6472_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_6473_, lean_object* v_h_6474_, lean_object* v_connection_6475_, lean_object* v_config_6476_, lean_object* v_connectionContext_6477_, lean_object* v_handler_6478_, lean_object* v_a_6479_){
_start:
{
lean_object* v_res_6480_; 
v_res_6480_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_6473_, v_h_6474_, v_connection_6475_, v_config_6476_, v_connectionContext_6477_, v_handler_6478_);
return v_res_6480_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_6481_, lean_object* v_00_u03c3_6482_, lean_object* v_inst_6483_, lean_object* v_h_6484_, lean_object* v_connection_6485_, lean_object* v_config_6486_, lean_object* v_connectionContext_6487_, lean_object* v_handler_6488_){
_start:
{
lean_object* v___x_6490_; 
v___x_6490_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_6483_, v_h_6484_, v_connection_6485_, v_config_6486_, v_connectionContext_6487_, v_handler_6488_);
return v___x_6490_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_6491_, lean_object* v_00_u03c3_6492_, lean_object* v_inst_6493_, lean_object* v_h_6494_, lean_object* v_connection_6495_, lean_object* v_config_6496_, lean_object* v_connectionContext_6497_, lean_object* v_handler_6498_, lean_object* v_a_6499_){
_start:
{
lean_object* v_res_6500_; 
v_res_6500_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_6491_, v_00_u03c3_6492_, v_inst_6493_, v_h_6494_, v_connection_6495_, v_config_6496_, v_connectionContext_6497_, v_handler_6498_);
return v_res_6500_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_6501_; lean_object* v___x_6502_; 
v___x_6501_ = 0;
v___x_6502_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_6501_);
return v___x_6502_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6503_; lean_object* v___x_6504_; 
v___x_6503_ = lean_unsigned_to_nat(4096u);
v___x_6504_ = lean_mk_empty_byte_array(v___x_6503_);
return v___x_6504_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_6505_; lean_object* v___x_6506_; 
v___x_6505_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_6506_ = l_ByteArray_mkIterator(v___x_6505_);
return v___x_6506_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_6507_; lean_object* v___x_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; lean_object* v___x_6512_; 
v___x_6507_ = 0;
v___x_6508_ = lean_unsigned_to_nat(0u);
v___x_6509_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_6510_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_6511_ = lean_box(0);
v___x_6512_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_6512_, 0, v___x_6511_);
lean_ctor_set(v___x_6512_, 1, v___x_6510_);
lean_ctor_set(v___x_6512_, 2, v___x_6509_);
lean_ctor_set(v___x_6512_, 3, v___x_6508_);
lean_ctor_set(v___x_6512_, 4, v___x_6508_);
lean_ctor_set(v___x_6512_, 5, v___x_6508_);
lean_ctor_set_uint8(v___x_6512_, sizeof(void*)*6, v___x_6507_);
lean_ctor_set_uint8(v___x_6512_, sizeof(void*)*6 + 1, v___x_6507_);
return v___x_6512_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_6520_; lean_object* v___x_6521_; 
v___x_6520_ = 1;
v___x_6521_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_6520_);
return v___x_6521_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_6522_; uint8_t v___x_6523_; lean_object* v___x_6524_; lean_object* v___x_6525_; lean_object* v___x_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; 
v___x_6522_ = lean_unsigned_to_nat(0u);
v___x_6523_ = 0;
v___x_6524_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_6525_ = lean_box(0);
v___x_6526_ = lean_box(0);
v___x_6527_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_6528_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_6529_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_6529_, 0, v___x_6528_);
lean_ctor_set(v___x_6529_, 1, v___x_6527_);
lean_ctor_set(v___x_6529_, 2, v___x_6526_);
lean_ctor_set(v___x_6529_, 3, v___x_6525_);
lean_ctor_set(v___x_6529_, 4, v___x_6524_);
lean_ctor_set(v___x_6529_, 5, v___x_6522_);
lean_ctor_set_uint8(v___x_6529_, sizeof(void*)*6, v___x_6523_);
lean_ctor_set_uint8(v___x_6529_, sizeof(void*)*6 + 1, v___x_6523_);
return v___x_6529_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_6530_, lean_object* v_client_6531_, lean_object* v_extensions_6532_, lean_object* v_inst_6533_, lean_object* v_inst_6534_, lean_object* v_handler_6535_, lean_object* v_x_6536_){
_start:
{
if (lean_obj_tag(v_x_6536_) == 0)
{
lean_object* v_a_6538_; lean_object* v___x_6540_; uint8_t v_isShared_6541_; uint8_t v_isSharedCheck_6546_; 
lean_dec(v_handler_6535_);
lean_dec_ref(v_inst_6534_);
lean_dec_ref(v_inst_6533_);
lean_dec(v_extensions_6532_);
lean_dec(v_client_6531_);
lean_dec_ref(v_config_6530_);
v_a_6538_ = lean_ctor_get(v_x_6536_, 0);
v_isSharedCheck_6546_ = !lean_is_exclusive(v_x_6536_);
if (v_isSharedCheck_6546_ == 0)
{
v___x_6540_ = v_x_6536_;
v_isShared_6541_ = v_isSharedCheck_6546_;
goto v_resetjp_6539_;
}
else
{
lean_inc(v_a_6538_);
lean_dec(v_x_6536_);
v___x_6540_ = lean_box(0);
v_isShared_6541_ = v_isSharedCheck_6546_;
goto v_resetjp_6539_;
}
v_resetjp_6539_:
{
lean_object* v___x_6543_; 
if (v_isShared_6541_ == 0)
{
v___x_6543_ = v___x_6540_;
goto v_reusejp_6542_;
}
else
{
lean_object* v_reuseFailAlloc_6545_; 
v_reuseFailAlloc_6545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6545_, 0, v_a_6538_);
v___x_6543_ = v_reuseFailAlloc_6545_;
goto v_reusejp_6542_;
}
v_reusejp_6542_:
{
lean_object* v___x_6544_; 
v___x_6544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6544_, 0, v___x_6543_);
return v___x_6544_;
}
}
}
else
{
lean_object* v_a_6547_; uint8_t v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; lean_object* v___x_6553_; uint8_t v_enableKeepAlive_6554_; lean_object* v___x_6555_; lean_object* v___x_6556_; lean_object* v___x_6557_; 
v_a_6547_ = lean_ctor_get(v_x_6536_, 0);
lean_inc(v_a_6547_);
lean_dec_ref_known(v_x_6536_, 1);
v___x_6548_ = 0;
v___x_6549_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_6550_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_6551_ = lean_box(0);
v___x_6552_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_6553_ = l_Std_Http_Config_toH1Config(v_config_6530_);
v_enableKeepAlive_6554_ = lean_ctor_get_uint8(v___x_6553_, sizeof(void*)*19);
v___x_6555_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_6555_, 0, v___x_6549_);
lean_ctor_set(v___x_6555_, 1, v___x_6552_);
lean_ctor_set(v___x_6555_, 2, v___x_6553_);
lean_ctor_set(v___x_6555_, 3, v___x_6550_);
lean_ctor_set(v___x_6555_, 4, v___x_6551_);
lean_ctor_set(v___x_6555_, 5, v___x_6551_);
lean_ctor_set_uint8(v___x_6555_, sizeof(void*)*6, v_enableKeepAlive_6554_);
lean_ctor_set_uint8(v___x_6555_, sizeof(void*)*6 + 1, v___x_6548_);
v___x_6556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6556_, 0, v_client_6531_);
lean_ctor_set(v___x_6556_, 1, v___x_6555_);
lean_ctor_set(v___x_6556_, 2, v_extensions_6532_);
v___x_6557_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_6533_, v_inst_6534_, v___x_6556_, v_config_6530_, v_a_6547_, v_handler_6535_);
return v___x_6557_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_6558_, lean_object* v_client_6559_, lean_object* v_extensions_6560_, lean_object* v_inst_6561_, lean_object* v_inst_6562_, lean_object* v_handler_6563_, lean_object* v_x_6564_, lean_object* v___y_6565_){
_start:
{
lean_object* v_res_6566_; 
v_res_6566_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_6558_, v_client_6559_, v_extensions_6560_, v_inst_6561_, v_inst_6562_, v_handler_6563_, v_x_6564_);
return v_res_6566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_6567_, lean_object* v_inst_6568_, lean_object* v_client_6569_, lean_object* v_handler_6570_, lean_object* v_config_6571_, lean_object* v_extensions_6572_, lean_object* v_a_6573_){
_start:
{
lean_object* v___f_6575_; lean_object* v___x_6576_; uint8_t v___x_6577_; lean_object* v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6580_; 
v___f_6575_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_6575_, 0, v_config_6571_);
lean_closure_set(v___f_6575_, 1, v_client_6569_);
lean_closure_set(v___f_6575_, 2, v_extensions_6572_);
lean_closure_set(v___f_6575_, 3, v_inst_6567_);
lean_closure_set(v___f_6575_, 4, v_inst_6568_);
lean_closure_set(v___f_6575_, 5, v_handler_6570_);
v___x_6576_ = lean_unsigned_to_nat(0u);
v___x_6577_ = 0;
lean_inc_ref(v_a_6573_);
v___x_6578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6578_, 0, v_a_6573_);
v___x_6579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6579_, 0, v___x_6578_);
v___x_6580_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6576_, v___x_6577_, v___x_6579_, v___f_6575_);
return v___x_6580_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_6581_, lean_object* v_inst_6582_, lean_object* v_client_6583_, lean_object* v_handler_6584_, lean_object* v_config_6585_, lean_object* v_extensions_6586_, lean_object* v_a_6587_, lean_object* v_a_6588_){
_start:
{
lean_object* v_res_6589_; 
v_res_6589_ = l_Std_Http_Server_serveConnection___redArg(v_inst_6581_, v_inst_6582_, v_client_6583_, v_handler_6584_, v_config_6585_, v_extensions_6586_, v_a_6587_);
lean_dec_ref(v_a_6587_);
return v_res_6589_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_6590_, lean_object* v_00_u03c3_6591_, lean_object* v_inst_6592_, lean_object* v_inst_6593_, lean_object* v_client_6594_, lean_object* v_handler_6595_, lean_object* v_config_6596_, lean_object* v_extensions_6597_, lean_object* v_a_6598_){
_start:
{
lean_object* v___x_6600_; 
v___x_6600_ = l_Std_Http_Server_serveConnection___redArg(v_inst_6592_, v_inst_6593_, v_client_6594_, v_handler_6595_, v_config_6596_, v_extensions_6597_, v_a_6598_);
return v___x_6600_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_6601_, lean_object* v_00_u03c3_6602_, lean_object* v_inst_6603_, lean_object* v_inst_6604_, lean_object* v_client_6605_, lean_object* v_handler_6606_, lean_object* v_config_6607_, lean_object* v_extensions_6608_, lean_object* v_a_6609_, lean_object* v_a_6610_){
_start:
{
lean_object* v_res_6611_; 
v_res_6611_ = l_Std_Http_Server_serveConnection(v_t_6601_, v_00_u03c3_6602_, v_inst_6603_, v_inst_6604_, v_client_6605_, v_handler_6606_, v_config_6607_, v_extensions_6608_, v_a_6609_);
lean_dec_ref(v_a_6609_);
return v_res_6611_;
}
}
lean_object* runtime_initialize_Std_Async_TCP(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_ContextAsync(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Transport(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Transport_Outbox(uint8_t builtin);
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
res = runtime_initialize_Std_Http_Transport_Outbox(builtin);
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
lean_object* initialize_Std_Http_Transport_Outbox(uint8_t builtin);
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
res = initialize_Std_Http_Transport_Outbox(builtin);
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
