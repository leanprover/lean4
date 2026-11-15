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
extern lean_object* l_instInhabitedError;
lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_get_current_time();
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ByteArray_mkIterator(lean_object*);
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
lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Http_Internal_Outbox_idleFor_x3f___redArg(lean_object*);
lean_object* l_Std_Http_Body_Stream_hasInterest(lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_Functor_discard(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Channel_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Machine_step(uint8_t, lean_object*);
lean_object* l_Std_Http_Internal_Outbox_takeError_x3f___redArg(lean_object*);
lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg(lean_object*);
lean_object* l_Std_Http_Internal_Outbox_push___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_Internal_Outbox_failed___redArg(lean_object*);
lean_object* l_Std_Async_Async_ofTask___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Http_Config_toH1Config(lean_object*);
uint8_t l_Std_Http_Method_isSafe(uint8_t);
lean_object* l_Std_Http_Internal_Outbox_new___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_keepAliveTimeout_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_keepAliveTimeout_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_shutdown_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_close_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "request header timeout"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__3_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__1_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__2_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__2_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__2_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__5;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__22(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__21(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "the connection closed before the request body was complete"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__26(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__27(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__27___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__28___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0(lean_object* v_x_151_){
_start:
{
if (lean_obj_tag(v_x_151_) == 0)
{
lean_object* v___x_153_; 
lean_dec_ref_known(v_x_151_, 1);
v___x_153_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_153_;
}
else
{
lean_object* v___x_154_; 
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v_x_151_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___boxed(lean_object* v_x_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0(v_x_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(lean_object* v_inst_159_, lean_object* v_handler_160_, lean_object* v_error_161_){
_start:
{
lean_object* v_onFailure_163_; lean_object* v___f_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_onFailure_163_ = lean_ctor_get(v_inst_159_, 2);
lean_inc_ref(v_onFailure_163_);
lean_dec_ref(v_inst_159_);
v___f_164_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___closed__0));
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = 0;
v___x_167_ = lean_apply_3(v_onFailure_163_, v_handler_160_, v_error_161_, lean_box(0));
v___x_168_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_165_, v___x_166_, v___x_167_, v___f_164_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___boxed(lean_object* v_inst_169_, lean_object* v_handler_170_, lean_object* v_error_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_169_, v_handler_170_, v_error_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure(lean_object* v_00_u03c3_174_, lean_object* v_inst_175_, lean_object* v_handler_176_, lean_object* v_error_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_175_, v_handler_176_, v_error_177_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___boxed(lean_object* v_00_u03c3_180_, lean_object* v_inst_181_, lean_object* v_handler_182_, lean_object* v_error_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure(v_00_u03c3_180_, v_inst_181_, v_handler_182_, v_error_183_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(lean_object* v_x_186_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v_x_186_);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed(lean_object* v_x_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(v_x_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_198_) == 0)
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_208_; 
v_a_200_ = lean_ctor_get(v_x_198_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_198_);
if (v_isSharedCheck_208_ == 0)
{
v___x_202_ = v_x_198_;
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v_x_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_208_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_207_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
}
else
{
lean_object* v___x_209_; 
lean_dec_ref_known(v_x_198_, 1);
v___x_209_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1));
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed(lean_object* v_x_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(v_x_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(lean_object* v_inst_213_, lean_object* v_handler_214_, lean_object* v___f_215_, lean_object* v_x_216_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_a_218_ = lean_ctor_get(v_x_216_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v_x_216_, 1);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = 0;
v___x_221_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_213_, v_handler_214_, v_a_218_);
v___x_222_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_219_, v___x_220_, v___x_221_, v___f_215_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; 
lean_dec_ref(v___f_215_);
lean_dec(v_handler_214_);
lean_dec_ref(v_inst_213_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v_x_216_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed(lean_object* v_inst_224_, lean_object* v_handler_225_, lean_object* v___f_226_, lean_object* v_x_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(v_inst_224_, v_handler_225_, v___f_226_, v_x_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(lean_object* v_x_230_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_232_, 0, v_x_230_);
v___x_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed(lean_object* v_x_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(v_x_235_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(uint8_t v_x_238_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_240_, 0, v_x_238_);
v___x_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed(lean_object* v_x_243_, lean_object* v___y_244_){
_start:
{
uint8_t v_x_3515__boxed_245_; lean_object* v_res_246_; 
v_x_3515__boxed_245_ = lean_unbox(v_x_243_);
v_res_246_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(v_x_3515__boxed_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(lean_object* v_x_247_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_249_, 0, v_x_247_);
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed(lean_object* v_x_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(v_x_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object* v_x_259_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__1));
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object* v_x_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(v_x_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object* v_x_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___closed__1));
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object* v_x_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v_x_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object* v_x_279_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_291_; 
v_a_283_ = lean_ctor_get(v_x_279_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_279_);
if (v_isSharedCheck_291_ == 0)
{
v___x_285_ = v_x_279_;
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v_x_279_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_290_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
}
else
{
lean_object* v_a_292_; 
v_a_292_ = lean_ctor_get(v_x_279_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v_x_279_, 1);
if (lean_obj_tag(v_a_292_) == 1)
{
lean_object* v_val_293_; 
v_val_293_ = lean_ctor_get(v_a_292_, 0);
lean_inc(v_val_293_);
lean_dec_ref_known(v_a_292_, 1);
if (lean_obj_tag(v_val_293_) == 0)
{
lean_object* v___x_294_; 
v___x_294_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___closed__1));
return v___x_294_;
}
else
{
lean_dec(v_val_293_);
goto v___jp_281_;
}
}
else
{
lean_dec(v_a_292_);
goto v___jp_281_;
}
}
v___jp_281_:
{
lean_object* v___x_282_; 
v___x_282_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___closed__1));
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object* v_x_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(v_x_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object* v___f_298_, lean_object* v_response_299_, lean_object* v___x_300_, lean_object* v___f_301_, lean_object* v_requestBody_302_, lean_object* v___f_303_, lean_object* v_responseBody_304_, lean_object* v_inst_305_, lean_object* v___f_306_, lean_object* v_____r_307_, lean_object* v_selectables_308_){
_start:
{
lean_object* v_selectables_311_; lean_object* v_selectables_317_; lean_object* v_selectables_323_; 
if (lean_obj_tag(v_responseBody_304_) == 1)
{
lean_object* v_val_328_; lean_object* v_recvSelector_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_selectables_332_; 
v_val_328_ = lean_ctor_get(v_responseBody_304_, 0);
lean_inc(v_val_328_);
lean_dec_ref_known(v_responseBody_304_, 1);
v_recvSelector_329_ = lean_ctor_get(v_inst_305_, 3);
lean_inc_ref(v_recvSelector_329_);
lean_dec_ref(v_inst_305_);
v___x_330_ = lean_apply_1(v_recvSelector_329_, v_val_328_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___f_306_);
v_selectables_332_ = lean_array_push(v_selectables_308_, v___x_331_);
v_selectables_323_ = v_selectables_332_;
goto v___jp_322_;
}
else
{
lean_dec_ref(v___f_306_);
lean_dec_ref(v_inst_305_);
lean_dec(v_responseBody_304_);
v_selectables_323_ = v_selectables_308_;
goto v___jp_322_;
}
v___jp_310_:
{
lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = 0;
v___x_314_ = l_Std_Async_Selectable_one___redArg(v_selectables_311_);
v___x_315_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_312_, v___x_313_, v___x_314_, v___f_298_);
return v___x_315_;
}
v___jp_316_:
{
if (lean_obj_tag(v_response_299_) == 1)
{
lean_object* v_val_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_selectables_321_; 
v_val_318_ = lean_ctor_get(v_response_299_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v_response_299_, 1);
v___x_319_ = l_Std_Channel_recvSelector___redArg(v___x_300_, v_val_318_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___f_301_);
v_selectables_321_ = lean_array_push(v_selectables_317_, v___x_320_);
v_selectables_311_ = v_selectables_321_;
goto v___jp_310_;
}
else
{
lean_dec_ref(v___f_301_);
lean_dec_ref(v___x_300_);
lean_dec(v_response_299_);
v_selectables_311_ = v_selectables_317_;
goto v___jp_310_;
}
}
v___jp_322_:
{
if (lean_obj_tag(v_requestBody_302_) == 1)
{
lean_object* v_val_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_selectables_327_; 
v_val_324_ = lean_ctor_get(v_requestBody_302_, 0);
lean_inc(v_val_324_);
lean_dec_ref_known(v_requestBody_302_, 1);
v___x_325_ = l_Std_Http_Body_Stream_interestSelector(v_val_324_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___f_303_);
v_selectables_327_ = lean_array_push(v_selectables_323_, v___x_326_);
v_selectables_317_ = v_selectables_327_;
goto v___jp_316_;
}
else
{
lean_dec_ref(v___f_303_);
lean_dec(v_requestBody_302_);
v_selectables_317_ = v_selectables_323_;
goto v___jp_316_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object* v___f_333_, lean_object* v_response_334_, lean_object* v___x_335_, lean_object* v___f_336_, lean_object* v_requestBody_337_, lean_object* v___f_338_, lean_object* v_responseBody_339_, lean_object* v_inst_340_, lean_object* v___f_341_, lean_object* v_____r_342_, lean_object* v_selectables_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v___f_333_, v_response_334_, v___x_335_, v___f_336_, v_requestBody_337_, v___f_338_, v_responseBody_339_, v_inst_340_, v___f_341_, v_____r_342_, v_selectables_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object* v___f_346_, lean_object* v_selectables_347_, lean_object* v___f_348_, lean_object* v_x_349_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref(v___f_348_);
lean_dec_ref(v_selectables_347_);
lean_dec_ref(v___f_346_);
v_a_351_ = lean_ctor_get(v_x_349_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v_x_349_);
if (v_isSharedCheck_359_ == 0)
{
v___x_353_ = v_x_349_;
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v_x_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_358_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_a_360_ = lean_ctor_get(v_x_349_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v_x_349_, 1);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_a_360_);
lean_ctor_set(v___x_361_, 1, v___f_346_);
v___x_362_ = lean_array_push(v_selectables_347_, v___x_361_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_apply_3(v___f_348_, v___x_363_, v___x_362_, lean_box(0));
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object* v___f_365_, lean_object* v_selectables_366_, lean_object* v___f_367_, lean_object* v_x_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(v___f_365_, v_selectables_366_, v___f_367_, v_x_368_);
return v_res_370_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_unsigned_to_nat(1000000000u);
v___x_372_ = lean_nat_to_int(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_unsigned_to_nat(1000u);
v___x_374_ = lean_nat_to_int(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_unsigned_to_nat(1000000u);
v___x_376_ = lean_nat_to_int(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(lean_object* v_val_377_, lean_object* v___f_378_, lean_object* v_x_379_){
_start:
{
if (lean_obj_tag(v_x_379_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_389_; 
lean_dec_ref(v___f_378_);
v_a_381_ = lean_ctor_get(v_x_379_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v_x_379_);
if (v_isSharedCheck_389_ == 0)
{
v___x_383_ = v_x_379_;
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v_x_379_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_389_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_388_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; 
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
}
else
{
lean_object* v_a_390_; lean_object* v_second_391_; lean_object* v_nano_392_; lean_object* v_second_393_; lean_object* v_nano_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v_nanos_399_; lean_object* v___x_400_; lean_object* v_nanos_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_second_404_; lean_object* v_nano_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_millis_410_; lean_object* v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_a_390_ = lean_ctor_get(v_x_379_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v_x_379_, 1);
v_second_391_ = lean_ctor_get(v_a_390_, 0);
lean_inc(v_second_391_);
v_nano_392_ = lean_ctor_get(v_a_390_, 1);
lean_inc(v_nano_392_);
lean_dec(v_a_390_);
v_second_393_ = lean_ctor_get(v_val_377_, 0);
v_nano_394_ = lean_ctor_get(v_val_377_, 1);
v___x_395_ = lean_int_neg(v_second_391_);
lean_dec(v_second_391_);
v___x_396_ = lean_int_neg(v_nano_392_);
lean_dec(v_nano_392_);
v___x_397_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_398_ = lean_int_mul(v_second_393_, v___x_397_);
v_nanos_399_ = lean_int_add(v___x_398_, v_nano_394_);
lean_dec(v___x_398_);
v___x_400_ = lean_int_mul(v___x_395_, v___x_397_);
lean_dec(v___x_395_);
v_nanos_401_ = lean_int_add(v___x_400_, v___x_396_);
lean_dec(v___x_396_);
lean_dec(v___x_400_);
v___x_402_ = lean_int_add(v_nanos_399_, v_nanos_401_);
lean_dec(v_nanos_401_);
lean_dec(v_nanos_399_);
v___x_403_ = l_Std_Time_Duration_ofNanoseconds(v___x_402_);
lean_dec(v___x_402_);
v_second_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_second_404_);
v_nano_405_ = lean_ctor_get(v___x_403_, 1);
lean_inc(v_nano_405_);
lean_dec_ref(v___x_403_);
v___x_406_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__1);
v___x_407_ = lean_int_mul(v_second_404_, v___x_406_);
lean_dec(v_second_404_);
v___x_408_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_409_ = lean_int_ediv(v_nano_405_, v___x_408_);
lean_dec(v_nano_405_);
v_millis_410_ = lean_int_add(v___x_407_, v___x_409_);
lean_dec(v___x_409_);
lean_dec(v___x_407_);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = 0;
v___x_413_ = l_Std_Async_Selector_sleep(v_millis_410_);
lean_dec(v_millis_410_);
v___x_414_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_411_, v___x_412_, v___x_413_, v___f_378_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed(lean_object* v_val_415_, lean_object* v___f_416_, lean_object* v_x_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11(v_val_415_, v___f_416_, v_x_417_);
lean_dec_ref(v_val_415_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__14(lean_object* v_token_420_, lean_object* v___f_421_, lean_object* v_x_422_){
_start:
{
lean_object* v___x_424_; uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = 0;
v___x_426_ = l_Std_CancellationToken_getCancellationReason(v_token_420_);
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
v___x_429_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_424_, v___x_425_, v___x_428_, v___f_421_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__14___boxed(lean_object* v_token_430_, lean_object* v___f_431_, lean_object* v_x_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__14(v_token_430_, v___f_431_, v_x_432_);
return v_res_434_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = l_instInhabitedError;
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_config_448_, lean_object* v_handler_449_, lean_object* v_sources_450_){
_start:
{
uint8_t v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v_val_456_; lean_object* v_socket_459_; uint8_t v_timer_460_; lean_object* v_expect_461_; lean_object* v_response_462_; lean_object* v_responseBody_463_; lean_object* v_requestBody_464_; lean_object* v_timeout_465_; lean_object* v_keepAliveTimeout_466_; lean_object* v_headerTimeout_467_; lean_object* v_connectionContext_468_; lean_object* v___f_469_; lean_object* v___f_470_; lean_object* v___f_471_; lean_object* v___f_472_; lean_object* v___f_473_; lean_object* v___f_474_; lean_object* v___f_475_; lean_object* v___f_476_; lean_object* v___f_477_; lean_object* v___x_478_; lean_object* v___f_479_; lean_object* v_selectables_481_; lean_object* v___y_517_; lean_object* v___y_533_; 
v_socket_459_ = lean_ctor_get(v_sources_450_, 0);
lean_inc(v_socket_459_);
v_timer_460_ = lean_ctor_get_uint8(v_sources_450_, sizeof(void*)*9);
v_expect_461_ = lean_ctor_get(v_sources_450_, 1);
lean_inc(v_expect_461_);
v_response_462_ = lean_ctor_get(v_sources_450_, 2);
lean_inc_n(v_response_462_, 2);
v_responseBody_463_ = lean_ctor_get(v_sources_450_, 3);
lean_inc_n(v_responseBody_463_, 2);
v_requestBody_464_ = lean_ctor_get(v_sources_450_, 4);
lean_inc_n(v_requestBody_464_, 2);
v_timeout_465_ = lean_ctor_get(v_sources_450_, 5);
lean_inc(v_timeout_465_);
v_keepAliveTimeout_466_ = lean_ctor_get(v_sources_450_, 6);
lean_inc(v_keepAliveTimeout_466_);
v_headerTimeout_467_ = lean_ctor_get(v_sources_450_, 7);
lean_inc(v_headerTimeout_467_);
v_connectionContext_468_ = lean_ctor_get(v_sources_450_, 8);
lean_inc_ref(v_connectionContext_468_);
lean_dec_ref(v_sources_450_);
v___f_469_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0));
v___f_470_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1));
v___f_471_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_471_, 0, v_inst_446_);
lean_closure_set(v___f_471_, 1, v_handler_449_);
lean_closure_set(v___f_471_, 2, v___f_470_);
v___f_472_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2));
v___f_473_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3));
v___f_474_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4));
v___f_475_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5));
v___f_476_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6));
v___f_477_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__7));
v___x_478_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__8);
lean_inc_ref(v_inst_447_);
lean_inc_ref(v___f_471_);
v___f_479_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed), 12, 9);
lean_closure_set(v___f_479_, 0, v___f_471_);
lean_closure_set(v___f_479_, 1, v_response_462_);
lean_closure_set(v___f_479_, 2, v___x_478_);
lean_closure_set(v___f_479_, 3, v___f_472_);
lean_closure_set(v___f_479_, 4, v_requestBody_464_);
lean_closure_set(v___f_479_, 5, v___f_473_);
lean_closure_set(v___f_479_, 6, v_responseBody_463_);
lean_closure_set(v___f_479_, 7, v_inst_447_);
lean_closure_set(v___f_479_, 8, v___f_474_);
if (lean_obj_tag(v_expect_461_) == 0)
{
lean_object* v_defaultPayloadBytes_536_; 
v_defaultPayloadBytes_536_ = lean_ctor_get(v_config_448_, 9);
lean_inc(v_defaultPayloadBytes_536_);
v___y_533_ = v_defaultPayloadBytes_536_;
goto v___jp_532_;
}
else
{
lean_object* v_val_537_; 
v_val_537_ = lean_ctor_get(v_expect_461_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v_expect_461_, 1);
v___y_533_ = v_val_537_;
goto v___jp_532_;
}
v___jp_452_:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_val_456_);
v___x_458_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_454_, v___y_453_, v___x_457_, v___y_455_);
return v___x_458_;
}
v___jp_480_:
{
if (v_timer_460_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec_ref(v___f_479_);
lean_dec(v_headerTimeout_467_);
lean_dec(v_keepAliveTimeout_466_);
lean_dec(v_timeout_465_);
v___x_482_ = lean_box(0);
v___x_483_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v___f_471_, v_response_462_, v___x_478_, v___f_472_, v_requestBody_464_, v___f_473_, v_responseBody_463_, v_inst_447_, v___f_474_, v___x_482_, v_selectables_481_);
return v___x_483_;
}
else
{
lean_dec_ref(v___f_471_);
lean_dec(v_requestBody_464_);
lean_dec(v_responseBody_463_);
lean_dec(v_response_462_);
lean_dec_ref(v_inst_447_);
if (lean_obj_tag(v_keepAliveTimeout_466_) == 0)
{
if (lean_obj_tag(v_headerTimeout_467_) == 1)
{
lean_object* v_val_484_; lean_object* v___f_485_; lean_object* v___f_486_; lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; 
lean_dec(v_timeout_465_);
v_val_484_ = lean_ctor_get(v_headerTimeout_467_, 0);
lean_inc(v_val_484_);
lean_dec_ref_known(v_headerTimeout_467_, 1);
v___f_485_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_485_, 0, v___f_475_);
lean_closure_set(v___f_485_, 1, v_selectables_481_);
lean_closure_set(v___f_485_, 2, v___f_479_);
v___f_486_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___boxed), 4, 2);
lean_closure_set(v___f_486_, 0, v_val_484_);
lean_closure_set(v___f_486_, 1, v___f_485_);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = 0;
v___x_489_ = lean_get_current_time();
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set_tag(v___x_492_, 1);
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
v___y_453_ = v___x_488_;
v___y_454_ = v___x_487_;
v___y_455_ = v___f_486_;
v_val_456_ = v___x_495_;
goto v___jp_452_;
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_a_498_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_489_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_489_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 0);
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
v___y_453_ = v___x_488_;
v___y_454_ = v___x_487_;
v___y_455_ = v___f_486_;
v_val_456_ = v___x_503_;
goto v___jp_452_;
}
}
}
}
else
{
lean_object* v___f_506_; lean_object* v___x_507_; uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v_headerTimeout_467_);
v___f_506_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_506_, 0, v___f_475_);
lean_closure_set(v___f_506_, 1, v_selectables_481_);
lean_closure_set(v___f_506_, 2, v___f_479_);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = 0;
v___x_509_ = l_Std_Async_Selector_sleep(v_timeout_465_);
lean_dec(v_timeout_465_);
v___x_510_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_507_, v___x_508_, v___x_509_, v___f_506_);
return v___x_510_;
}
}
else
{
lean_object* v___f_511_; uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec_ref_known(v_keepAliveTimeout_466_, 1);
lean_dec(v_headerTimeout_467_);
v___f_511_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_511_, 0, v___f_476_);
lean_closure_set(v___f_511_, 1, v_selectables_481_);
lean_closure_set(v___f_511_, 2, v___f_479_);
v___x_512_ = 0;
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = l_Std_Async_Selector_sleep(v_timeout_465_);
lean_dec(v_timeout_465_);
v___x_515_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_513_, v___x_512_, v___x_514_, v___f_511_);
return v___x_515_;
}
}
}
v___jp_516_:
{
lean_object* v_token_518_; lean_object* v___f_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v_selectables_524_; 
v_token_518_ = lean_ctor_get(v_connectionContext_468_, 1);
lean_inc_ref_n(v_token_518_, 2);
lean_dec_ref(v_connectionContext_468_);
v___f_519_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__14___boxed), 4, 2);
lean_closure_set(v___f_519_, 0, v_token_518_);
lean_closure_set(v___f_519_, 1, v___f_477_);
v___x_520_ = l_Std_CancellationToken_selector(v_token_518_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___f_519_);
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_mk_empty_array_with_capacity(v___x_522_);
v_selectables_524_ = lean_array_push(v___x_523_, v___x_521_);
if (lean_obj_tag(v_socket_459_) == 1)
{
lean_object* v_val_525_; lean_object* v_recvSelector_526_; uint64_t v_expectedBytes_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_selectables_531_; 
v_val_525_ = lean_ctor_get(v_socket_459_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v_socket_459_, 1);
v_recvSelector_526_ = lean_ctor_get(v_inst_445_, 2);
lean_inc_ref(v_recvSelector_526_);
lean_dec_ref(v_inst_445_);
v_expectedBytes_527_ = lean_uint64_of_nat(v___y_517_);
lean_dec(v___y_517_);
v___x_528_ = lean_box_uint64(v_expectedBytes_527_);
v___x_529_ = lean_apply_2(v_recvSelector_526_, v_val_525_, v___x_528_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___f_469_);
v_selectables_531_ = lean_array_push(v_selectables_524_, v___x_530_);
v_selectables_481_ = v_selectables_531_;
goto v___jp_480_;
}
else
{
lean_dec(v___y_517_);
lean_dec(v_socket_459_);
lean_dec_ref(v_inst_445_);
v_selectables_481_ = v_selectables_524_;
goto v___jp_480_;
}
}
v___jp_532_:
{
lean_object* v_maximumRecvSize_534_; uint8_t v___x_535_; 
v_maximumRecvSize_534_ = lean_ctor_get(v_config_448_, 8);
lean_inc(v_maximumRecvSize_534_);
lean_dec_ref(v_config_448_);
v___x_535_ = lean_nat_dec_le(v___y_533_, v_maximumRecvSize_534_);
if (v___x_535_ == 0)
{
lean_dec(v___y_533_);
v___y_517_ = v_maximumRecvSize_534_;
goto v___jp_516_;
}
else
{
lean_dec(v_maximumRecvSize_534_);
v___y_517_ = v___y_533_;
goto v___jp_516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_config_541_, lean_object* v_handler_542_, lean_object* v_sources_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_538_, v_inst_539_, v_inst_540_, v_config_541_, v_handler_542_, v_sources_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object* v_00_u03b1_546_, lean_object* v_00_u03c3_547_, lean_object* v_00_u03b2_548_, lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_config_552_, lean_object* v_handler_553_, lean_object* v_sources_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_549_, v_inst_550_, v_inst_551_, v_config_552_, v_handler_553_, v_sources_554_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object* v_00_u03b1_557_, lean_object* v_00_u03c3_558_, lean_object* v_00_u03b2_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_config_563_, lean_object* v_handler_564_, lean_object* v_sources_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(v_00_u03b1_557_, v_00_u03c3_558_, v_00_u03b2_559_, v_inst_560_, v_inst_561_, v_inst_562_, v_config_563_, v_handler_564_, v_sources_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(lean_object* v_machine_568_, lean_object* v_x_569_){
_start:
{
lean_object* v___y_572_; uint8_t v___y_573_; 
if (lean_obj_tag(v_x_569_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v_machine_568_);
v_a_578_ = lean_ctor_get(v_x_569_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v_x_569_);
if (v_isSharedCheck_586_ == 0)
{
v___x_580_ = v_x_569_;
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v_x_569_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_585_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; 
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___y_589_; uint8_t v___x_595_; 
v_a_587_ = lean_ctor_get(v_x_569_, 0);
lean_inc(v_a_587_);
lean_dec_ref_known(v_x_569_, 1);
v___x_595_ = lean_unbox(v_a_587_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_box(40);
v___y_589_ = v___x_596_;
goto v___jp_588_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_box(0);
v___y_589_ = v___x_597_;
goto v___jp_588_;
}
v___jp_588_:
{
uint8_t v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_590_ = 0;
lean_inc(v___y_589_);
v___x_591_ = l_Std_Http_Protocol_H1_Machine_canContinue(v___x_590_, v_machine_568_, v___y_589_);
v___x_592_ = lean_unbox(v_a_587_);
lean_dec(v_a_587_);
if (v___x_592_ == 0)
{
uint8_t v___x_593_; 
v___x_593_ = 1;
v___y_572_ = v___x_591_;
v___y_573_ = v___x_593_;
goto v___jp_571_;
}
else
{
uint8_t v___x_594_; 
v___x_594_ = 0;
v___y_572_ = v___x_591_;
v___y_573_ = v___x_594_;
goto v___jp_571_;
}
}
}
v___jp_571_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_574_ = lean_box(v___y_573_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___y_572_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object* v_machine_598_, lean_object* v_x_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(v_machine_598_, v_x_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t v___y_602_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_box(v___y_602_);
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
uint8_t v___y_1377__boxed_609_; lean_object* v_res_610_; 
v___y_1377__boxed_609_ = lean_unbox(v___y_607_);
v_res_610_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_1377__boxed_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object* v_x_611_){
_start:
{
if (lean_obj_tag(v_x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_613_; 
v_a_612_ = lean_ctor_get(v_x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v_x_611_, 1);
v___x_613_ = lean_task_pure(v_a_612_);
return v___x_613_;
}
else
{
lean_object* v_a_614_; 
v_a_614_ = lean_ctor_get(v_x_611_, 0);
lean_inc_ref(v_a_614_);
lean_dec_ref_known(v_x_611_, 1);
return v_a_614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object* v_a_615_, lean_object* v_x_616_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec_ref_known(v_x_616_, 1);
v___x_618_ = 0;
v___x_619_ = lean_box(0);
v___x_620_ = lean_box(v___x_618_);
v___x_621_ = l_Std_Channel_send___redArg(v_a_615_, v___x_620_);
lean_dec_ref(v___x_621_);
return v___x_619_;
}
else
{
lean_object* v_a_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_a_622_ = lean_ctor_get(v_x_616_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v_x_616_, 1);
v___x_623_ = lean_box(0);
v___x_624_ = l_Std_Channel_send___redArg(v_a_615_, v_a_622_);
lean_dec_ref(v___x_624_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object* v_a_625_, lean_object* v_x_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(v_a_625_, v_x_626_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t v___x_629_, lean_object* v_x_630_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_box(v___x_629_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object* v___x_635_, lean_object* v_x_636_, lean_object* v___y_637_){
_start:
{
uint8_t v___x_1421__boxed_638_; lean_object* v_res_639_; 
v___x_1421__boxed_638_ = lean_unbox(v___x_635_);
v_res_639_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_1421__boxed_638_, v_x_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object* v_connectionContext_640_, uint8_t v___x_641_, lean_object* v_a_642_, lean_object* v___f_643_, lean_object* v___f_644_, lean_object* v___x_645_, uint8_t v___x_646_, lean_object* v___f_647_, lean_object* v_x_648_){
_start:
{
if (lean_obj_tag(v_x_648_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v___f_647_);
lean_dec(v___x_645_);
lean_dec_ref(v___f_644_);
lean_dec_ref(v___f_643_);
lean_dec_ref(v_a_642_);
lean_dec_ref(v_connectionContext_640_);
v_a_650_ = lean_ctor_get(v_x_648_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_648_);
if (v_isSharedCheck_658_ == 0)
{
v___x_652_ = v_x_648_;
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v_x_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_657_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
}
else
{
lean_object* v_a_659_; lean_object* v_token_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_a_659_ = lean_ctor_get(v_x_648_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v_x_648_, 1);
v_token_660_ = lean_ctor_get(v_connectionContext_640_, 1);
lean_inc_ref(v_token_660_);
lean_dec_ref(v_connectionContext_640_);
v___x_661_ = lean_box(v___x_641_);
v___x_662_ = l_Std_Channel_recvSelector___redArg(v___x_661_, v_a_642_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v___f_643_);
v___x_664_ = l_Std_CancellationToken_selector(v_token_660_);
lean_inc_ref(v___f_644_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___f_644_);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_a_659_);
lean_ctor_set(v___x_666_, 1, v___f_644_);
v___x_667_ = lean_unsigned_to_nat(3u);
v___x_668_ = lean_mk_empty_array_with_capacity(v___x_667_);
v___x_669_ = lean_array_push(v___x_668_, v___x_663_);
v___x_670_ = lean_array_push(v___x_669_, v___x_665_);
v___x_671_ = lean_array_push(v___x_670_, v___x_666_);
v___x_672_ = l_Std_Async_Selectable_one___redArg(v___x_671_);
v___x_673_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_645_, v___x_646_, v___x_672_, v___f_647_);
return v___x_673_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object* v_connectionContext_674_, lean_object* v___x_675_, lean_object* v_a_676_, lean_object* v___f_677_, lean_object* v___f_678_, lean_object* v___x_679_, lean_object* v___x_680_, lean_object* v___f_681_, lean_object* v_x_682_, lean_object* v___y_683_){
_start:
{
uint8_t v___x_1436__boxed_684_; uint8_t v___x_1441__boxed_685_; lean_object* v_res_686_; 
v___x_1436__boxed_684_ = lean_unbox(v___x_675_);
v___x_1441__boxed_685_ = lean_unbox(v___x_680_);
v_res_686_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_674_, v___x_1436__boxed_684_, v_a_676_, v___f_677_, v___f_678_, v___x_679_, v___x_1441__boxed_685_, v___f_681_, v_x_682_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object* v_config_687_, lean_object* v___x_688_, uint8_t v___x_689_, lean_object* v___f_690_, lean_object* v_x_691_){
_start:
{
if (lean_obj_tag(v_x_691_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref(v___f_690_);
lean_dec(v___x_688_);
v_a_693_ = lean_ctor_get(v_x_691_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_691_);
if (v_isSharedCheck_701_ == 0)
{
v___x_695_ = v_x_691_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v_x_691_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_700_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
}
else
{
lean_object* v_lingeringTimeout_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec_ref_known(v_x_691_, 1);
v_lingeringTimeout_702_ = lean_ctor_get(v_config_687_, 4);
v___x_703_ = l_Std_Async_Selector_sleep(v_lingeringTimeout_702_);
v___x_704_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_688_, v___x_689_, v___x_703_, v___f_690_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object* v_config_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v___f_708_, lean_object* v_x_709_, lean_object* v___y_710_){
_start:
{
uint8_t v___x_1510__boxed_711_; lean_object* v_res_712_; 
v___x_1510__boxed_711_ = lean_unbox(v___x_707_);
v_res_712_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_705_, v___x_706_, v___x_1510__boxed_711_, v___f_708_, v_x_709_);
lean_dec_ref(v_config_705_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object* v_connectionContext_716_, uint8_t v___x_717_, lean_object* v_a_718_, lean_object* v___f_719_, lean_object* v___x_720_, lean_object* v___f_721_, lean_object* v_config_722_, lean_object* v___f_723_, lean_object* v_x_724_){
_start:
{
if (lean_obj_tag(v_x_724_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v___f_723_);
lean_dec_ref(v_config_722_);
lean_dec_ref(v___f_721_);
lean_dec(v___x_720_);
lean_dec_ref(v___f_719_);
lean_dec_ref(v_a_718_);
lean_dec_ref(v_connectionContext_716_);
v_a_726_ = lean_ctor_get(v_x_724_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v_x_724_);
if (v_isSharedCheck_734_ == 0)
{
v___x_728_ = v_x_724_;
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v_x_724_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_733_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_732_; 
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_752_; 
v_a_735_ = lean_ctor_get(v_x_724_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v_x_724_);
if (v_isSharedCheck_752_ == 0)
{
v___x_737_ = v_x_724_;
v_isShared_738_ = v_isSharedCheck_752_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v_x_724_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_752_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
uint8_t v___x_739_; lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_739_ = 0;
v___f_740_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0));
v___x_741_ = lean_box(v___x_717_);
v___x_742_ = lean_box(v___x_739_);
lean_inc_n(v___x_720_, 3);
v___f_743_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed), 10, 8);
lean_closure_set(v___f_743_, 0, v_connectionContext_716_);
lean_closure_set(v___f_743_, 1, v___x_741_);
lean_closure_set(v___f_743_, 2, v_a_718_);
lean_closure_set(v___f_743_, 3, v___f_719_);
lean_closure_set(v___f_743_, 4, v___f_740_);
lean_closure_set(v___f_743_, 5, v___x_720_);
lean_closure_set(v___f_743_, 6, v___x_742_);
lean_closure_set(v___f_743_, 7, v___f_721_);
v___x_744_ = lean_box(v___x_739_);
v___f_745_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_745_, 0, v_config_722_);
lean_closure_set(v___f_745_, 1, v___x_720_);
lean_closure_set(v___f_745_, 2, v___x_744_);
lean_closure_set(v___f_745_, 3, v___f_743_);
v___x_746_ = l_BaseIO_chainTask___redArg(v_a_735_, v___f_723_, v___x_720_, v___x_739_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_746_);
v___x_748_ = v___x_737_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_751_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
v___x_750_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_720_, v___x_739_, v___x_749_, v___f_745_);
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object* v_connectionContext_753_, lean_object* v___x_754_, lean_object* v_a_755_, lean_object* v___f_756_, lean_object* v___x_757_, lean_object* v___f_758_, lean_object* v_config_759_, lean_object* v___f_760_, lean_object* v_x_761_, lean_object* v___y_762_){
_start:
{
uint8_t v___x_1550__boxed_763_; lean_object* v_res_764_; 
v___x_1550__boxed_763_ = lean_unbox(v___x_754_);
v_res_764_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v_connectionContext_753_, v___x_1550__boxed_763_, v_a_755_, v___f_756_, v___x_757_, v___f_758_, v_config_759_, v___f_760_, v_x_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object* v_inst_765_, lean_object* v_handler_766_, lean_object* v_head_767_, lean_object* v_connectionContext_768_, uint8_t v___x_769_, lean_object* v___f_770_, lean_object* v___f_771_, lean_object* v_config_772_, lean_object* v___f_773_, lean_object* v_x_774_){
_start:
{
if (lean_obj_tag(v_x_774_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v___f_773_);
lean_dec_ref(v_config_772_);
lean_dec_ref(v___f_771_);
lean_dec_ref(v___f_770_);
lean_dec_ref(v_connectionContext_768_);
lean_dec_ref(v_head_767_);
lean_dec(v_handler_766_);
lean_dec_ref(v_inst_765_);
v_a_776_ = lean_ctor_get(v_x_774_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v_x_774_);
if (v_isSharedCheck_784_ == 0)
{
v___x_778_ = v_x_774_;
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v_x_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_783_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; 
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_805_; 
v_a_785_ = lean_ctor_get(v_x_774_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_x_774_);
if (v_isSharedCheck_805_ == 0)
{
v___x_787_ = v_x_774_;
v_isShared_788_ = v_isSharedCheck_805_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v_x_774_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_805_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_onContinue_789_; lean_object* v___f_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___f_794_; uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_801_; 
v_onContinue_789_ = lean_ctor_get(v_inst_765_, 3);
lean_inc_ref(v_onContinue_789_);
lean_dec_ref(v_inst_765_);
lean_inc(v_a_785_);
v___f_790_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_790_, 0, v_a_785_);
v___x_791_ = lean_apply_2(v_onContinue_789_, v_handler_766_, v_head_767_);
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_box(v___x_769_);
v___f_794_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_794_, 0, v_connectionContext_768_);
lean_closure_set(v___f_794_, 1, v___x_793_);
lean_closure_set(v___f_794_, 2, v_a_785_);
lean_closure_set(v___f_794_, 3, v___f_770_);
lean_closure_set(v___f_794_, 4, v___x_792_);
lean_closure_set(v___f_794_, 5, v___f_771_);
lean_closure_set(v___f_794_, 6, v_config_772_);
lean_closure_set(v___f_794_, 7, v___f_790_);
v___x_795_ = 0;
v___x_796_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_796_, 0, lean_box(0));
lean_closure_set(v___x_796_, 1, v___x_791_);
v___x_797_ = lean_io_as_task(v___x_796_, v___x_792_);
v___x_798_ = 1;
v___x_799_ = lean_task_bind(v___x_797_, v___f_773_, v___x_792_, v___x_798_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_799_);
v___x_801_ = v___x_787_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_804_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
v___x_803_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_792_, v___x_795_, v___x_802_, v___f_794_);
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object* v_inst_806_, lean_object* v_handler_807_, lean_object* v_head_808_, lean_object* v_connectionContext_809_, lean_object* v___x_810_, lean_object* v___f_811_, lean_object* v___f_812_, lean_object* v_config_813_, lean_object* v___f_814_, lean_object* v_x_815_, lean_object* v___y_816_){
_start:
{
uint8_t v___x_1633__boxed_817_; lean_object* v_res_818_; 
v___x_1633__boxed_817_ = lean_unbox(v___x_810_);
v_res_818_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_806_, v_handler_807_, v_head_808_, v_connectionContext_809_, v___x_1633__boxed_817_, v___f_811_, v___f_812_, v_config_813_, v___f_814_, v_x_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object* v_inst_821_, lean_object* v_handler_822_, lean_object* v_machine_823_, lean_object* v_head_824_, lean_object* v_config_825_, lean_object* v_connectionContext_826_){
_start:
{
lean_object* v___f_828_; lean_object* v___f_829_; lean_object* v___f_830_; uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___f_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___f_828_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_828_, 0, v_machine_823_);
v___f_829_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0));
v___f_830_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1));
v___x_831_ = 0;
v___x_832_ = lean_box(v___x_831_);
v___f_833_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_833_, 0, v_inst_821_);
lean_closure_set(v___f_833_, 1, v_handler_822_);
lean_closure_set(v___f_833_, 2, v_head_824_);
lean_closure_set(v___f_833_, 3, v_connectionContext_826_);
lean_closure_set(v___f_833_, 4, v___x_832_);
lean_closure_set(v___f_833_, 5, v___f_829_);
lean_closure_set(v___f_833_, 6, v___f_828_);
lean_closure_set(v___f_833_, 7, v_config_825_);
lean_closure_set(v___f_833_, 8, v___f_830_);
v___x_834_ = lean_box(0);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = l_Std_CloseableChannel_new___redArg(v___x_834_);
v___x_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
v___x_839_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_835_, v___x_831_, v___x_838_, v___f_833_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object* v_inst_840_, lean_object* v_handler_841_, lean_object* v_machine_842_, lean_object* v_head_843_, lean_object* v_config_844_, lean_object* v_connectionContext_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_840_, v_handler_841_, v_machine_842_, v_head_843_, v_config_844_, v_connectionContext_845_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object* v_00_u03c3_848_, lean_object* v_inst_849_, lean_object* v_handler_850_, lean_object* v_machine_851_, lean_object* v_head_852_, lean_object* v_config_853_, lean_object* v_connectionContext_854_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_849_, v_handler_850_, v_machine_851_, v_head_852_, v_config_853_, v_connectionContext_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object* v_00_u03c3_857_, lean_object* v_inst_858_, lean_object* v_handler_859_, lean_object* v_machine_860_, lean_object* v_head_861_, lean_object* v_config_862_, lean_object* v_connectionContext_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(v_00_u03c3_857_, v_inst_858_, v_handler_859_, v_machine_860_, v_head_861_, v_config_862_, v_connectionContext_863_);
return v_res_865_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v_x_866_){
_start:
{
lean_object* v_fst_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_fst_867_ = lean_ctor_get(v_x_866_, 0);
v___x_868_ = l_Std_Http_Header_Name_contentLength;
v___x_869_ = lean_string_dec_eq(v_fst_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_870_ = l_Std_Http_Header_Name_transferEncoding;
v___x_871_ = lean_string_dec_eq(v_fst_867_, v___x_870_);
return v___x_871_;
}
else
{
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v_x_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v_x_872_);
lean_dec_ref(v_x_872_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___y_875_, lean_object* v_____r_876_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_878_ = lean_box(0);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___y_875_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___y_882_, lean_object* v_____r_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___y_882_, v_____r_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v___f_886_, lean_object* v_x_887_){
_start:
{
if (lean_obj_tag(v_x_887_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v___f_886_);
v_a_889_ = lean_ctor_get(v_x_887_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_x_887_);
if (v_isSharedCheck_897_ == 0)
{
v___x_891_ = v_x_887_;
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v_x_887_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_896_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; 
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_898_ = lean_ctor_get(v_x_887_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v_x_887_, 1);
v___x_899_ = lean_apply_2(v___f_886_, v_a_898_, lean_box(0));
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v___f_900_, lean_object* v_x_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v___f_900_, v_x_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_close_904_, lean_object* v_body_905_, lean_object* v___f_906_, lean_object* v___f_907_, lean_object* v_x_908_){
_start:
{
if (lean_obj_tag(v_x_908_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v___f_907_);
lean_dec_ref(v___f_906_);
lean_dec(v_body_905_);
lean_dec_ref(v_close_904_);
v_a_910_ = lean_ctor_get(v_x_908_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_x_908_);
if (v_isSharedCheck_918_ == 0)
{
v___x_912_ = v_x_908_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v_x_908_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_917_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
else
{
lean_object* v_a_919_; uint8_t v___x_920_; 
v_a_919_ = lean_ctor_get(v_x_908_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v_x_908_, 1);
v___x_920_ = lean_unbox(v_a_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; lean_object* v___x_924_; 
lean_dec_ref(v___f_907_);
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = lean_apply_2(v_close_904_, v_body_905_, lean_box(0));
v___x_923_ = lean_unbox(v_a_919_);
lean_dec(v_a_919_);
v___x_924_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_921_, v___x_923_, v___x_922_, v___f_906_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v_a_919_);
lean_dec_ref(v___f_906_);
lean_dec(v_body_905_);
lean_dec_ref(v_close_904_);
v___x_925_ = lean_box(0);
v___x_926_ = lean_apply_2(v___f_907_, v___x_925_, lean_box(0));
return v___x_926_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_close_927_, lean_object* v_body_928_, lean_object* v___f_929_, lean_object* v___f_930_, lean_object* v_x_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_close_927_, v_body_928_, v___f_929_, v___f_930_, v_x_931_);
return v_res_933_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_934_, lean_object* v_x_935_){
_start:
{
lean_object* v_fst_936_; uint8_t v___x_937_; 
v_fst_936_ = lean_ctor_get(v_x_935_, 0);
v___x_937_ = lean_string_dec_eq(v_fst_936_, v___x_934_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_938_, lean_object* v_x_939_){
_start:
{
uint8_t v_res_940_; lean_object* v_r_941_; 
v_res_940_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_938_, v_x_939_);
lean_dec_ref(v_x_939_);
lean_dec_ref(v___x_938_);
v_r_941_ = lean_box(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object* v___x_942_, lean_object* v_x1_943_, lean_object* v_x2_944_){
_start:
{
lean_object* v_fst_945_; uint8_t v___x_946_; 
v_fst_945_ = lean_ctor_get(v_x2_944_, 0);
v___x_946_ = lean_string_dec_eq(v_fst_945_, v___x_942_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
v___x_947_ = lean_array_push(v_x1_943_, v_x2_944_);
return v___x_947_;
}
else
{
lean_dec_ref(v_x2_944_);
return v_x1_943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed(lean_object* v___x_948_, lean_object* v_x1_949_, lean_object* v_x2_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(v___x_948_, v_x1_949_, v_x2_950_);
lean_dec_ref(v___x_948_);
return v_res_951_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10(void){
_start:
{
lean_object* v___x_971_; lean_object* v___f_972_; 
v___x_971_ = l_Std_Http_Header_Name_transferEncoding;
v___f_972_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_972_, 0, v___x_971_);
return v___f_972_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11(void){
_start:
{
lean_object* v___x_973_; lean_object* v___f_974_; 
v___x_973_ = l_Std_Http_Header_Name_transferEncoding;
v___f_974_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_974_, 0, v___x_973_);
return v___f_974_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13(void){
_start:
{
lean_object* v___x_977_; lean_object* v___f_978_; 
v___x_977_ = l_Std_Http_Header_Name_contentLength;
v___f_978_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_978_, 0, v___x_977_);
return v___f_978_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14(void){
_start:
{
lean_object* v___x_979_; lean_object* v___f_980_; 
v___x_979_ = l_Std_Http_Header_Name_contentLength;
v___f_980_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_980_, 0, v___x_979_);
return v___f_980_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object* v_body_981_, lean_object* v_close_982_, lean_object* v_isClosed_983_, lean_object* v_line_984_, lean_object* v___f_985_, lean_object* v_machine_986_, lean_object* v_x_987_){
_start:
{
lean_object* v___y_990_; uint8_t v_omitBody_991_; lean_object* v___y_1004_; lean_object* v_reader_1008_; lean_object* v_writer_1009_; lean_object* v_config_1010_; lean_object* v_events_1011_; lean_object* v_error_1012_; lean_object* v_date_1013_; uint8_t v_keepAlive_1014_; uint8_t v_pullBodyStalled_1015_; uint8_t v___y_1016_; uint8_t v___y_1017_; uint8_t v___y_1018_; uint8_t v___y_1019_; lean_object* v_reader_1087_; uint8_t v_method_1088_; lean_object* v_writer_1089_; lean_object* v_config_1090_; lean_object* v_events_1091_; lean_object* v_error_1092_; lean_object* v_date_1093_; uint8_t v_keepAlive_1094_; uint8_t v_pullBodyStalled_1095_; uint8_t v___y_1096_; uint8_t v___y_1097_; uint8_t v___y_1098_; lean_object* v___y_1108_; uint8_t v___y_1109_; uint8_t v___y_1110_; uint8_t v___y_1111_; lean_object* v___y_1123_; uint8_t v___y_1124_; lean_object* v___y_1127_; uint16_t v___y_1128_; uint8_t v___y_1129_; uint8_t v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; uint8_t v___y_1133_; uint8_t v___y_1159_; uint8_t v___y_1160_; uint8_t v___y_1161_; lean_object* v_val_1162_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; uint8_t v___y_1178_; lean_object* v___y_1179_; uint8_t v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; uint8_t v___y_1185_; uint8_t v___y_1186_; uint8_t v___y_1187_; uint8_t v___y_1188_; lean_object* v___y_1189_; uint8_t v___y_1190_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; uint8_t v___y_1198_; lean_object* v___y_1199_; uint8_t v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; uint8_t v___y_1205_; uint8_t v___y_1206_; lean_object* v___y_1207_; uint8_t v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1213_; lean_object* v___y_1214_; uint8_t v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; uint8_t v___y_1219_; lean_object* v___y_1220_; uint8_t v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; uint8_t v___y_1226_; uint8_t v___y_1227_; lean_object* v___y_1228_; uint8_t v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1249_; lean_object* v___y_1250_; uint8_t v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; uint8_t v___y_1255_; lean_object* v___y_1256_; uint8_t v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; uint8_t v___y_1261_; lean_object* v___y_1262_; uint8_t v___y_1263_; lean_object* v___y_1264_; uint8_t v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1280_; lean_object* v___y_1281_; uint8_t v___y_1282_; uint8_t v___y_1283_; uint8_t v___y_1284_; uint8_t v___y_1285_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; uint8_t v___y_1296_; lean_object* v___y_1297_; uint8_t v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; uint8_t v___y_1303_; lean_object* v___y_1304_; uint8_t v___y_1305_; uint8_t v___y_1306_; uint16_t v___y_1307_; uint8_t v___y_1308_; lean_object* v___y_1309_; uint8_t v___y_1310_; lean_object* v___y_1311_; uint8_t v___y_1312_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; uint8_t v___y_1335_; lean_object* v___y_1336_; uint8_t v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; uint8_t v___y_1341_; lean_object* v___y_1342_; uint8_t v___y_1343_; uint8_t v___y_1344_; uint8_t v___y_1345_; lean_object* v___y_1346_; uint8_t v___y_1347_; uint8_t v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; uint8_t v___y_1363_; lean_object* v___y_1364_; uint8_t v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; uint8_t v___y_1369_; lean_object* v___y_1370_; uint8_t v___y_1371_; uint8_t v___y_1372_; uint8_t v___y_1373_; lean_object* v___y_1374_; uint8_t v___y_1375_; uint8_t v___y_1376_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; uint8_t v___y_1384_; uint8_t v___y_1385_; lean_object* v___y_1386_; uint8_t v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; uint8_t v___y_1392_; uint8_t v___y_1393_; uint8_t v___y_1394_; uint8_t v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1397_; lean_object* v___y_1412_; lean_object* v_reader_1413_; lean_object* v_userData_1414_; lean_object* v_outputData_1415_; lean_object* v_state_1416_; lean_object* v_knownSize_1417_; lean_object* v_messageHead_1418_; uint8_t v_sentMessage_1419_; uint8_t v_userClosedBody_1420_; uint8_t v_omitBody_1421_; lean_object* v_userDataBytes_1422_; lean_object* v_config_1423_; lean_object* v_events_1424_; lean_object* v_error_1425_; lean_object* v_date_1426_; uint8_t v_keepAlive_1427_; uint8_t v_pullBodyStalled_1428_; 
if (lean_obj_tag(v_x_987_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v_machine_986_);
lean_dec_ref(v___f_985_);
lean_dec_ref(v_line_984_);
lean_dec_ref(v_isClosed_983_);
lean_dec_ref(v_close_982_);
lean_dec(v_body_981_);
v_a_1456_ = lean_ctor_get(v_x_987_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_x_987_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1458_ = v_x_987_;
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v_x_987_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
}
}
else
{
lean_object* v_a_1465_; 
v_a_1465_ = lean_ctor_get(v_x_987_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v_x_987_, 1);
if (lean_obj_tag(v_a_1465_) == 1)
{
lean_object* v_writer_1466_; lean_object* v_reader_1467_; lean_object* v_config_1468_; lean_object* v_events_1469_; lean_object* v_error_1470_; lean_object* v_date_1471_; uint8_t v_keepAlive_1472_; uint8_t v_pullBodyStalled_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1496_; 
v_writer_1466_ = lean_ctor_get(v_machine_986_, 1);
v_reader_1467_ = lean_ctor_get(v_machine_986_, 0);
v_config_1468_ = lean_ctor_get(v_machine_986_, 2);
v_events_1469_ = lean_ctor_get(v_machine_986_, 3);
v_error_1470_ = lean_ctor_get(v_machine_986_, 4);
v_date_1471_ = lean_ctor_get(v_machine_986_, 5);
v_keepAlive_1472_ = lean_ctor_get_uint8(v_machine_986_, sizeof(void*)*6);
v_pullBodyStalled_1473_ = lean_ctor_get_uint8(v_machine_986_, sizeof(void*)*6 + 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_machine_986_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1475_ = v_machine_986_;
v_isShared_1476_ = v_isSharedCheck_1496_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_date_1471_);
lean_inc(v_error_1470_);
lean_inc(v_events_1469_);
lean_inc(v_config_1468_);
lean_inc(v_writer_1466_);
lean_inc(v_reader_1467_);
lean_dec(v_machine_986_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1496_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_userData_1477_; lean_object* v_outputData_1478_; lean_object* v_state_1479_; lean_object* v_messageHead_1480_; uint8_t v_sentMessage_1481_; uint8_t v_userClosedBody_1482_; uint8_t v_omitBody_1483_; lean_object* v_userDataBytes_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1494_; 
v_userData_1477_ = lean_ctor_get(v_writer_1466_, 0);
v_outputData_1478_ = lean_ctor_get(v_writer_1466_, 1);
v_state_1479_ = lean_ctor_get(v_writer_1466_, 2);
v_messageHead_1480_ = lean_ctor_get(v_writer_1466_, 4);
v_sentMessage_1481_ = lean_ctor_get_uint8(v_writer_1466_, sizeof(void*)*6);
v_userClosedBody_1482_ = lean_ctor_get_uint8(v_writer_1466_, sizeof(void*)*6 + 1);
v_omitBody_1483_ = lean_ctor_get_uint8(v_writer_1466_, sizeof(void*)*6 + 2);
v_userDataBytes_1484_ = lean_ctor_get(v_writer_1466_, 5);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_writer_1466_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v_writer_1466_, 3);
lean_dec(v_unused_1495_);
v___x_1486_ = v_writer_1466_;
v_isShared_1487_ = v_isSharedCheck_1494_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_userDataBytes_1484_);
lean_inc(v_messageHead_1480_);
lean_inc(v_state_1479_);
lean_inc(v_outputData_1478_);
lean_inc(v_userData_1477_);
lean_dec(v_writer_1466_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1494_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
lean_inc(v_userDataBytes_1484_);
lean_inc(v_messageHead_1480_);
lean_inc_ref(v_a_1465_);
lean_inc(v_state_1479_);
lean_inc_ref(v_outputData_1478_);
lean_inc_ref(v_userData_1477_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 3, v_a_1465_);
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_userData_1477_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_outputData_1478_);
lean_ctor_set(v_reuseFailAlloc_1493_, 2, v_state_1479_);
lean_ctor_set(v_reuseFailAlloc_1493_, 3, v_a_1465_);
lean_ctor_set(v_reuseFailAlloc_1493_, 4, v_messageHead_1480_);
lean_ctor_set(v_reuseFailAlloc_1493_, 5, v_userDataBytes_1484_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*6, v_sentMessage_1481_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*6 + 1, v_userClosedBody_1482_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, sizeof(void*)*6 + 2, v_omitBody_1483_);
v___x_1489_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; 
lean_inc(v_date_1471_);
lean_inc(v_error_1470_);
lean_inc_ref(v_events_1469_);
lean_inc_ref(v_config_1468_);
lean_inc_ref(v_reader_1467_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1489_);
v___x_1491_ = v___x_1475_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_reader_1467_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_config_1468_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_events_1469_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v_error_1470_);
lean_ctor_set(v_reuseFailAlloc_1492_, 5, v_date_1471_);
lean_ctor_set_uint8(v_reuseFailAlloc_1492_, sizeof(void*)*6, v_keepAlive_1472_);
lean_ctor_set_uint8(v_reuseFailAlloc_1492_, sizeof(void*)*6 + 1, v_pullBodyStalled_1473_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
v___y_1412_ = v___x_1491_;
v_reader_1413_ = v_reader_1467_;
v_userData_1414_ = v_userData_1477_;
v_outputData_1415_ = v_outputData_1478_;
v_state_1416_ = v_state_1479_;
v_knownSize_1417_ = v_a_1465_;
v_messageHead_1418_ = v_messageHead_1480_;
v_sentMessage_1419_ = v_sentMessage_1481_;
v_userClosedBody_1420_ = v_userClosedBody_1482_;
v_omitBody_1421_ = v_omitBody_1483_;
v_userDataBytes_1422_ = v_userDataBytes_1484_;
v_config_1423_ = v_config_1468_;
v_events_1424_ = v_events_1469_;
v_error_1425_ = v_error_1470_;
v_date_1426_ = v_date_1471_;
v_keepAlive_1427_ = v_keepAlive_1472_;
v_pullBodyStalled_1428_ = v_pullBodyStalled_1473_;
goto v___jp_1411_;
}
}
}
}
}
else
{
lean_object* v_writer_1497_; lean_object* v_reader_1498_; lean_object* v_config_1499_; lean_object* v_events_1500_; lean_object* v_error_1501_; lean_object* v_date_1502_; uint8_t v_keepAlive_1503_; uint8_t v_pullBodyStalled_1504_; lean_object* v_userData_1505_; lean_object* v_outputData_1506_; lean_object* v_state_1507_; lean_object* v_knownSize_1508_; lean_object* v_messageHead_1509_; uint8_t v_sentMessage_1510_; uint8_t v_userClosedBody_1511_; uint8_t v_omitBody_1512_; lean_object* v_userDataBytes_1513_; 
lean_dec(v_a_1465_);
v_writer_1497_ = lean_ctor_get(v_machine_986_, 1);
v_reader_1498_ = lean_ctor_get(v_machine_986_, 0);
lean_inc_ref(v_reader_1498_);
v_config_1499_ = lean_ctor_get(v_machine_986_, 2);
lean_inc_ref(v_config_1499_);
v_events_1500_ = lean_ctor_get(v_machine_986_, 3);
lean_inc_ref(v_events_1500_);
v_error_1501_ = lean_ctor_get(v_machine_986_, 4);
lean_inc(v_error_1501_);
v_date_1502_ = lean_ctor_get(v_machine_986_, 5);
lean_inc(v_date_1502_);
v_keepAlive_1503_ = lean_ctor_get_uint8(v_machine_986_, sizeof(void*)*6);
v_pullBodyStalled_1504_ = lean_ctor_get_uint8(v_machine_986_, sizeof(void*)*6 + 1);
v_userData_1505_ = lean_ctor_get(v_writer_1497_, 0);
lean_inc_ref(v_userData_1505_);
v_outputData_1506_ = lean_ctor_get(v_writer_1497_, 1);
lean_inc_ref(v_outputData_1506_);
v_state_1507_ = lean_ctor_get(v_writer_1497_, 2);
lean_inc(v_state_1507_);
v_knownSize_1508_ = lean_ctor_get(v_writer_1497_, 3);
lean_inc(v_knownSize_1508_);
v_messageHead_1509_ = lean_ctor_get(v_writer_1497_, 4);
lean_inc(v_messageHead_1509_);
v_sentMessage_1510_ = lean_ctor_get_uint8(v_writer_1497_, sizeof(void*)*6);
v_userClosedBody_1511_ = lean_ctor_get_uint8(v_writer_1497_, sizeof(void*)*6 + 1);
v_omitBody_1512_ = lean_ctor_get_uint8(v_writer_1497_, sizeof(void*)*6 + 2);
v_userDataBytes_1513_ = lean_ctor_get(v_writer_1497_, 5);
lean_inc(v_userDataBytes_1513_);
v___y_1412_ = v_machine_986_;
v_reader_1413_ = v_reader_1498_;
v_userData_1414_ = v_userData_1505_;
v_outputData_1415_ = v_outputData_1506_;
v_state_1416_ = v_state_1507_;
v_knownSize_1417_ = v_knownSize_1508_;
v_messageHead_1418_ = v_messageHead_1509_;
v_sentMessage_1419_ = v_sentMessage_1510_;
v_userClosedBody_1420_ = v_userClosedBody_1511_;
v_omitBody_1421_ = v_omitBody_1512_;
v_userDataBytes_1422_ = v_userDataBytes_1513_;
v_config_1423_ = v_config_1499_;
v_events_1424_ = v_events_1500_;
v_error_1425_ = v_error_1501_;
v_date_1426_ = v_date_1502_;
v_keepAlive_1427_ = v_keepAlive_1503_;
v_pullBodyStalled_1428_ = v_pullBodyStalled_1504_;
goto v___jp_1411_;
}
}
v___jp_989_:
{
if (v_omitBody_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
lean_dec_ref(v_isClosed_983_);
lean_dec_ref(v_close_982_);
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v_body_981_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___y_990_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
else
{
lean_object* v___f_996_; lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___f_996_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_996_, 0, v___y_990_);
lean_inc_ref(v___f_996_);
v___f_997_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_997_, 0, v___f_996_);
lean_inc(v_body_981_);
v___f_998_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_998_, 0, v_close_982_);
lean_closure_set(v___f_998_, 1, v_body_981_);
lean_closure_set(v___f_998_, 2, v___f_997_);
lean_closure_set(v___f_998_, 3, v___f_996_);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = 0;
v___x_1001_ = lean_apply_2(v_isClosed_983_, v_body_981_, lean_box(0));
v___x_1002_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_999_, v___x_1000_, v___x_1001_, v___f_998_);
return v___x_1002_;
}
}
v___jp_1003_:
{
lean_object* v_writer_1005_; uint8_t v_omitBody_1006_; 
v_writer_1005_ = lean_ctor_get(v___y_1004_, 1);
v_omitBody_1006_ = lean_ctor_get_uint8(v_writer_1005_, sizeof(void*)*6 + 2);
v___y_990_ = v___y_1004_;
v_omitBody_991_ = v_omitBody_1006_;
goto v___jp_989_;
}
v___jp_1007_:
{
lean_object* v_userData_1020_; lean_object* v_outputData_1021_; lean_object* v_state_1022_; lean_object* v_knownSize_1023_; uint8_t v_userClosedBody_1024_; uint8_t v_omitBody_1025_; lean_object* v_userDataBytes_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1084_; 
v_userData_1020_ = lean_ctor_get(v_writer_1009_, 0);
v_outputData_1021_ = lean_ctor_get(v_writer_1009_, 1);
v_state_1022_ = lean_ctor_get(v_writer_1009_, 2);
v_knownSize_1023_ = lean_ctor_get(v_writer_1009_, 3);
v_userClosedBody_1024_ = lean_ctor_get_uint8(v_writer_1009_, sizeof(void*)*6 + 1);
v_omitBody_1025_ = lean_ctor_get_uint8(v_writer_1009_, sizeof(void*)*6 + 2);
v_userDataBytes_1026_ = lean_ctor_get(v_writer_1009_, 5);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_writer_1009_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v_writer_1009_, 4);
lean_dec(v_unused_1085_);
v___x_1028_ = v_writer_1009_;
v_isShared_1029_ = v_isSharedCheck_1084_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_userDataBytes_1026_);
lean_inc(v_knownSize_1023_);
lean_inc(v_state_1022_);
lean_inc(v_outputData_1021_);
lean_inc(v_userData_1020_);
lean_dec(v_writer_1009_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1084_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
lean_inc_ref(v_line_984_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 4, v_line_984_);
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_userData_1020_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_outputData_1021_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_state_1022_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_knownSize_1023_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v_line_984_);
lean_ctor_set(v_reuseFailAlloc_1083_, 5, v_userDataBytes_1026_);
lean_ctor_set_uint8(v_reuseFailAlloc_1083_, sizeof(void*)*6 + 1, v_userClosedBody_1024_);
lean_ctor_set_uint8(v_reuseFailAlloc_1083_, sizeof(void*)*6 + 2, v_omitBody_1025_);
v___x_1031_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v_machine_1032_; lean_object* v_machine_1033_; lean_object* v_writer_1034_; lean_object* v_reader_1035_; lean_object* v_config_1036_; lean_object* v_events_1037_; lean_object* v_error_1038_; lean_object* v_date_1039_; uint8_t v_keepAlive_1040_; uint8_t v_pullBodyStalled_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1082_; 
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*6, v___y_1017_);
v_machine_1032_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_machine_1032_, 0, v_reader_1008_);
lean_ctor_set(v_machine_1032_, 1, v___x_1031_);
lean_ctor_set(v_machine_1032_, 2, v_config_1010_);
lean_ctor_set(v_machine_1032_, 3, v_events_1011_);
lean_ctor_set(v_machine_1032_, 4, v_error_1012_);
lean_ctor_set(v_machine_1032_, 5, v_date_1013_);
lean_ctor_set_uint8(v_machine_1032_, sizeof(void*)*6, v_keepAlive_1014_);
lean_ctor_set_uint8(v_machine_1032_, sizeof(void*)*6 + 1, v_pullBodyStalled_1015_);
v_machine_1033_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___y_1016_, v_machine_1032_, v_line_984_);
lean_dec_ref(v_line_984_);
v_writer_1034_ = lean_ctor_get(v_machine_1033_, 1);
v_reader_1035_ = lean_ctor_get(v_machine_1033_, 0);
v_config_1036_ = lean_ctor_get(v_machine_1033_, 2);
v_events_1037_ = lean_ctor_get(v_machine_1033_, 3);
v_error_1038_ = lean_ctor_get(v_machine_1033_, 4);
v_date_1039_ = lean_ctor_get(v_machine_1033_, 5);
v_keepAlive_1040_ = lean_ctor_get_uint8(v_machine_1033_, sizeof(void*)*6);
v_pullBodyStalled_1041_ = lean_ctor_get_uint8(v_machine_1033_, sizeof(void*)*6 + 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_machine_1033_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1043_ = v_machine_1033_;
v_isShared_1044_ = v_isSharedCheck_1082_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_date_1039_);
lean_inc(v_error_1038_);
lean_inc(v_events_1037_);
lean_inc(v_config_1036_);
lean_inc(v_writer_1034_);
lean_inc(v_reader_1035_);
lean_dec(v_machine_1033_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1082_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_userData_1045_; lean_object* v_outputData_1046_; lean_object* v_knownSize_1047_; lean_object* v_messageHead_1048_; uint8_t v_sentMessage_1049_; uint8_t v_userClosedBody_1050_; uint8_t v_omitBody_1051_; lean_object* v_userDataBytes_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1080_; 
v_userData_1045_ = lean_ctor_get(v_writer_1034_, 0);
v_outputData_1046_ = lean_ctor_get(v_writer_1034_, 1);
v_knownSize_1047_ = lean_ctor_get(v_writer_1034_, 3);
v_messageHead_1048_ = lean_ctor_get(v_writer_1034_, 4);
v_sentMessage_1049_ = lean_ctor_get_uint8(v_writer_1034_, sizeof(void*)*6);
v_userClosedBody_1050_ = lean_ctor_get_uint8(v_writer_1034_, sizeof(void*)*6 + 1);
v_omitBody_1051_ = lean_ctor_get_uint8(v_writer_1034_, sizeof(void*)*6 + 2);
v_userDataBytes_1052_ = lean_ctor_get(v_writer_1034_, 5);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_writer_1034_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v_writer_1034_, 2);
lean_dec(v_unused_1081_);
v___x_1054_ = v_writer_1034_;
v_isShared_1055_ = v_isSharedCheck_1080_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_userDataBytes_1052_);
lean_inc(v_messageHead_1048_);
lean_inc(v_knownSize_1047_);
lean_inc(v_outputData_1046_);
lean_inc(v_userData_1045_);
lean_dec(v_writer_1034_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1080_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1056_ = lean_box(2);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 2, v___x_1056_);
v___x_1058_ = v___x_1054_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_userData_1045_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_outputData_1046_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_knownSize_1047_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_messageHead_1048_);
lean_ctor_set(v_reuseFailAlloc_1079_, 5, v_userDataBytes_1052_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*6, v_sentMessage_1049_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*6 + 1, v_userClosedBody_1050_);
lean_ctor_set_uint8(v_reuseFailAlloc_1079_, sizeof(void*)*6 + 2, v_omitBody_1051_);
v___x_1058_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
if (v___y_1019_ == 0)
{
lean_object* v_machine_1060_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 1, v___x_1058_);
v_machine_1060_ = v___x_1043_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_reader_1035_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v_config_1036_);
lean_ctor_set(v_reuseFailAlloc_1061_, 3, v_events_1037_);
lean_ctor_set(v_reuseFailAlloc_1061_, 4, v_error_1038_);
lean_ctor_set(v_reuseFailAlloc_1061_, 5, v_date_1039_);
lean_ctor_set_uint8(v_reuseFailAlloc_1061_, sizeof(void*)*6, v_keepAlive_1040_);
lean_ctor_set_uint8(v_reuseFailAlloc_1061_, sizeof(void*)*6 + 1, v_pullBodyStalled_1041_);
v_machine_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
v___y_990_ = v_machine_1060_;
v_omitBody_991_ = v_omitBody_1051_;
goto v___jp_989_;
}
}
else
{
lean_object* v_input_1062_; lean_object* v_messageHead_1063_; lean_object* v_messageCount_1064_; lean_object* v_bodyBytesRead_1065_; lean_object* v_headerBytesRead_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1077_; 
v_input_1062_ = lean_ctor_get(v_reader_1035_, 1);
v_messageHead_1063_ = lean_ctor_get(v_reader_1035_, 2);
v_messageCount_1064_ = lean_ctor_get(v_reader_1035_, 3);
v_bodyBytesRead_1065_ = lean_ctor_get(v_reader_1035_, 4);
v_headerBytesRead_1066_ = lean_ctor_get(v_reader_1035_, 5);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_reader_1035_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v_reader_1035_, 0);
lean_dec(v_unused_1078_);
v___x_1068_ = v_reader_1035_;
v_isShared_1069_ = v_isSharedCheck_1077_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_headerBytesRead_1066_);
lean_inc(v_bodyBytesRead_1065_);
lean_inc(v_messageCount_1064_);
lean_inc(v_messageHead_1063_);
lean_inc(v_input_1062_);
lean_dec(v_reader_1035_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1077_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = lean_box(6);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 0, v___x_1070_);
v___x_1072_ = v___x_1068_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_input_1062_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_messageHead_1063_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_messageCount_1064_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v_bodyBytesRead_1065_);
lean_ctor_set(v_reuseFailAlloc_1076_, 5, v_headerBytesRead_1066_);
v___x_1072_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1074_; 
lean_ctor_set_uint8(v___x_1072_, sizeof(void*)*6, v___y_1019_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 1, v___x_1058_);
lean_ctor_set(v___x_1043_, 0, v___x_1072_);
v___x_1074_ = v___x_1043_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_config_1036_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v_events_1037_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v_error_1038_);
lean_ctor_set(v_reuseFailAlloc_1075_, 5, v_date_1039_);
lean_ctor_set_uint8(v_reuseFailAlloc_1075_, sizeof(void*)*6 + 1, v_pullBodyStalled_1041_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*6, v___y_1018_);
v___y_990_ = v___x_1074_;
v_omitBody_991_ = v_omitBody_1051_;
goto v___jp_989_;
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
v___jp_1086_:
{
uint8_t v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = 5;
v___x_1100_ = l_Std_Http_instBEqMethod_beq(v_method_1088_, v___x_1099_);
if (v___x_1100_ == 0)
{
v_reader_1008_ = v_reader_1087_;
v_writer_1009_ = v_writer_1089_;
v_config_1010_ = v_config_1090_;
v_events_1011_ = v_events_1091_;
v_error_1012_ = v_error_1092_;
v_date_1013_ = v_date_1093_;
v_keepAlive_1014_ = v_keepAlive_1094_;
v_pullBodyStalled_1015_ = v_pullBodyStalled_1095_;
v___y_1016_ = v___y_1097_;
v___y_1017_ = v___y_1096_;
v___y_1018_ = v___y_1098_;
v___y_1019_ = v___x_1100_;
goto v___jp_1007_;
}
else
{
lean_object* v_status_1101_; uint16_t v___x_1102_; uint16_t v___x_1103_; uint8_t v___x_1104_; 
v_status_1101_ = lean_ctor_get(v_line_984_, 0);
v___x_1102_ = 200;
v___x_1103_ = l_Std_Http_Status_toCode(v_status_1101_);
v___x_1104_ = lean_uint16_dec_le(v___x_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
v_reader_1008_ = v_reader_1087_;
v_writer_1009_ = v_writer_1089_;
v_config_1010_ = v_config_1090_;
v_events_1011_ = v_events_1091_;
v_error_1012_ = v_error_1092_;
v_date_1013_ = v_date_1093_;
v_keepAlive_1014_ = v_keepAlive_1094_;
v_pullBodyStalled_1015_ = v_pullBodyStalled_1095_;
v___y_1016_ = v___y_1097_;
v___y_1017_ = v___y_1096_;
v___y_1018_ = v___y_1098_;
v___y_1019_ = v___x_1104_;
goto v___jp_1007_;
}
else
{
uint16_t v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = 300;
v___x_1106_ = lean_uint16_dec_lt(v___x_1103_, v___x_1105_);
v_reader_1008_ = v_reader_1087_;
v_writer_1009_ = v_writer_1089_;
v_config_1010_ = v_config_1090_;
v_events_1011_ = v_events_1091_;
v_error_1012_ = v_error_1092_;
v_date_1013_ = v_date_1093_;
v_keepAlive_1014_ = v_keepAlive_1094_;
v_pullBodyStalled_1015_ = v_pullBodyStalled_1095_;
v___y_1016_ = v___y_1097_;
v___y_1017_ = v___y_1096_;
v___y_1018_ = v___y_1098_;
v___y_1019_ = v___x_1106_;
goto v___jp_1007_;
}
}
}
v___jp_1107_:
{
lean_object* v_reader_1112_; lean_object* v_messageHead_1113_; lean_object* v_writer_1114_; lean_object* v_config_1115_; lean_object* v_events_1116_; lean_object* v_error_1117_; lean_object* v_date_1118_; uint8_t v_keepAlive_1119_; uint8_t v_pullBodyStalled_1120_; uint8_t v_method_1121_; 
v_reader_1112_ = lean_ctor_get(v___y_1108_, 0);
lean_inc_ref(v_reader_1112_);
v_messageHead_1113_ = lean_ctor_get(v_reader_1112_, 2);
v_writer_1114_ = lean_ctor_get(v___y_1108_, 1);
lean_inc_ref(v_writer_1114_);
v_config_1115_ = lean_ctor_get(v___y_1108_, 2);
lean_inc_ref(v_config_1115_);
v_events_1116_ = lean_ctor_get(v___y_1108_, 3);
lean_inc_ref(v_events_1116_);
v_error_1117_ = lean_ctor_get(v___y_1108_, 4);
lean_inc(v_error_1117_);
v_date_1118_ = lean_ctor_get(v___y_1108_, 5);
lean_inc(v_date_1118_);
v_keepAlive_1119_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*6);
v_pullBodyStalled_1120_ = lean_ctor_get_uint8(v___y_1108_, sizeof(void*)*6 + 1);
lean_dec_ref(v___y_1108_);
v_method_1121_ = lean_ctor_get_uint8(v_messageHead_1113_, sizeof(void*)*2);
v_reader_1087_ = v_reader_1112_;
v_method_1088_ = v_method_1121_;
v_writer_1089_ = v_writer_1114_;
v_config_1090_ = v_config_1115_;
v_events_1091_ = v_events_1116_;
v_error_1092_ = v_error_1117_;
v_date_1093_ = v_date_1118_;
v_keepAlive_1094_ = v_keepAlive_1119_;
v_pullBodyStalled_1095_ = v_pullBodyStalled_1120_;
v___y_1096_ = v___y_1109_;
v___y_1097_ = v___y_1110_;
v___y_1098_ = v___y_1111_;
goto v___jp_1086_;
}
v___jp_1122_:
{
lean_object* v___x_1125_; 
v___x_1125_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_rejectOutgoingFraming(v___y_1124_, v___y_1123_);
v___y_1004_ = v___x_1125_;
goto v___jp_1003_;
}
v___jp_1126_:
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_unsigned_to_nat(204u);
v___x_1135_ = lean_nat_dec_eq(v___y_1132_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(304u);
v___x_1137_ = lean_nat_dec_eq(v___y_1132_, v___x_1136_);
lean_dec(v___y_1132_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_box(9);
v___x_1139_ = l_Std_Http_instBEqStatus_beq(v___y_1131_, v___x_1138_);
lean_dec(v___y_1131_);
if (v___x_1139_ == 0)
{
lean_object* v_reader_1140_; lean_object* v_messageHead_1141_; lean_object* v_writer_1142_; lean_object* v_config_1143_; lean_object* v_events_1144_; lean_object* v_error_1145_; lean_object* v_date_1146_; uint8_t v_keepAlive_1147_; uint8_t v_pullBodyStalled_1148_; uint8_t v_method_1149_; uint8_t v___x_1150_; uint8_t v___x_1151_; 
v_reader_1140_ = lean_ctor_get(v___y_1127_, 0);
v_messageHead_1141_ = lean_ctor_get(v_reader_1140_, 2);
v_writer_1142_ = lean_ctor_get(v___y_1127_, 1);
v_config_1143_ = lean_ctor_get(v___y_1127_, 2);
v_events_1144_ = lean_ctor_get(v___y_1127_, 3);
v_error_1145_ = lean_ctor_get(v___y_1127_, 4);
v_date_1146_ = lean_ctor_get(v___y_1127_, 5);
v_keepAlive_1147_ = lean_ctor_get_uint8(v___y_1127_, sizeof(void*)*6);
v_pullBodyStalled_1148_ = lean_ctor_get_uint8(v___y_1127_, sizeof(void*)*6 + 1);
v_method_1149_ = lean_ctor_get_uint8(v_messageHead_1141_, sizeof(void*)*2);
v___x_1150_ = 9;
v___x_1151_ = l_Std_Http_instBEqMethod_beq(v_method_1149_, v___x_1150_);
if (v___x_1151_ == 0)
{
uint8_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = 5;
v___x_1153_ = l_Std_Http_instBEqMethod_beq(v_method_1149_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_dec_ref(v_line_984_);
v___y_1123_ = v___y_1127_;
v___y_1124_ = v___y_1130_;
goto v___jp_1122_;
}
else
{
uint16_t v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = 200;
v___x_1155_ = lean_uint16_dec_le(v___x_1154_, v___y_1128_);
if (v___x_1155_ == 0)
{
lean_dec_ref(v_line_984_);
v___y_1123_ = v___y_1127_;
v___y_1124_ = v___y_1130_;
goto v___jp_1122_;
}
else
{
uint16_t v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = 300;
v___x_1157_ = lean_uint16_dec_lt(v___y_1128_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_dec_ref(v_line_984_);
v___y_1123_ = v___y_1127_;
v___y_1124_ = v___y_1130_;
goto v___jp_1122_;
}
else
{
lean_inc(v_date_1146_);
lean_inc(v_error_1145_);
lean_inc_ref(v_events_1144_);
lean_inc_ref(v_config_1143_);
lean_inc_ref(v_writer_1142_);
lean_inc_ref(v_reader_1140_);
lean_dec_ref(v___y_1127_);
v_reader_1087_ = v_reader_1140_;
v_method_1088_ = v_method_1149_;
v_writer_1089_ = v_writer_1142_;
v_config_1090_ = v_config_1143_;
v_events_1091_ = v_events_1144_;
v_error_1092_ = v_error_1145_;
v_date_1093_ = v_date_1146_;
v_keepAlive_1094_ = v_keepAlive_1147_;
v_pullBodyStalled_1095_ = v_pullBodyStalled_1148_;
v___y_1096_ = v___y_1129_;
v___y_1097_ = v___y_1130_;
v___y_1098_ = v___y_1133_;
goto v___jp_1086_;
}
}
}
}
else
{
lean_inc(v_date_1146_);
lean_inc(v_error_1145_);
lean_inc_ref(v_events_1144_);
lean_inc_ref(v_config_1143_);
lean_inc_ref(v_writer_1142_);
lean_inc_ref(v_reader_1140_);
lean_dec_ref(v___y_1127_);
v_reader_1087_ = v_reader_1140_;
v_method_1088_ = v_method_1149_;
v_writer_1089_ = v_writer_1142_;
v_config_1090_ = v_config_1143_;
v_events_1091_ = v_events_1144_;
v_error_1092_ = v_error_1145_;
v_date_1093_ = v_date_1146_;
v_keepAlive_1094_ = v_keepAlive_1147_;
v_pullBodyStalled_1095_ = v_pullBodyStalled_1148_;
v___y_1096_ = v___y_1129_;
v___y_1097_ = v___y_1130_;
v___y_1098_ = v___y_1133_;
goto v___jp_1086_;
}
}
else
{
v___y_1108_ = v___y_1127_;
v___y_1109_ = v___y_1129_;
v___y_1110_ = v___y_1130_;
v___y_1111_ = v___y_1133_;
goto v___jp_1107_;
}
}
else
{
lean_dec(v___y_1131_);
v___y_1108_ = v___y_1127_;
v___y_1109_ = v___y_1129_;
v___y_1110_ = v___y_1130_;
v___y_1111_ = v___y_1133_;
goto v___jp_1107_;
}
}
else
{
lean_dec(v___y_1132_);
lean_dec(v___y_1131_);
v___y_1108_ = v___y_1127_;
v___y_1109_ = v___y_1129_;
v___y_1110_ = v___y_1130_;
v___y_1111_ = v___y_1133_;
goto v___jp_1107_;
}
}
v___jp_1158_:
{
uint8_t v___x_1163_; 
v___x_1163_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_unframeableForHttp10(v___y_1159_, v_val_1162_, v_line_984_);
if (v___x_1163_ == 0)
{
v___y_1108_ = v_val_1162_;
v___y_1109_ = v___y_1160_;
v___y_1110_ = v___y_1159_;
v___y_1111_ = v___y_1161_;
goto v___jp_1107_;
}
else
{
lean_object* v_status_1164_; uint16_t v___x_1165_; lean_object* v_code_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v_status_1164_ = lean_ctor_get(v_line_984_, 0);
v___x_1165_ = l_Std_Http_Status_toCode(v_status_1164_);
v_code_1166_ = lean_uint16_to_nat(v___x_1165_);
v___x_1167_ = lean_unsigned_to_nat(100u);
v___x_1168_ = lean_nat_dec_le(v___x_1167_, v_code_1166_);
if (v___x_1168_ == 0)
{
lean_inc(v_status_1164_);
v___y_1127_ = v_val_1162_;
v___y_1128_ = v___x_1165_;
v___y_1129_ = v___y_1160_;
v___y_1130_ = v___y_1159_;
v___y_1131_ = v_status_1164_;
v___y_1132_ = v_code_1166_;
v___y_1133_ = v___y_1161_;
goto v___jp_1126_;
}
else
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_unsigned_to_nat(200u);
v___x_1170_ = lean_nat_dec_lt(v_code_1166_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_inc(v_status_1164_);
v___y_1127_ = v_val_1162_;
v___y_1128_ = v___x_1165_;
v___y_1129_ = v___y_1160_;
v___y_1130_ = v___y_1159_;
v___y_1131_ = v_status_1164_;
v___y_1132_ = v_code_1166_;
v___y_1133_ = v___y_1161_;
goto v___jp_1126_;
}
else
{
v___y_1108_ = v_val_1162_;
v___y_1109_ = v___y_1160_;
v___y_1110_ = v___y_1159_;
v___y_1111_ = v___y_1161_;
goto v___jp_1107_;
}
}
}
}
v___jp_1171_:
{
if (lean_obj_tag(v___y_1174_) == 0)
{
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec(v___y_1179_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec_ref(v___y_1173_);
v___y_1159_ = v___y_1186_;
v___y_1160_ = v___y_1187_;
v___y_1161_ = v___y_1178_;
v_val_1162_ = v___y_1172_;
goto v___jp_1158_;
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
lean_dec_ref(v___y_1172_);
v___x_1191_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1191_, 0, v___y_1175_);
lean_ctor_set(v___x_1191_, 1, v___y_1176_);
lean_ctor_set(v___x_1191_, 2, v___y_1184_);
lean_ctor_set(v___x_1191_, 3, v___y_1174_);
lean_ctor_set(v___x_1191_, 4, v___y_1177_);
lean_ctor_set(v___x_1191_, 5, v___y_1183_);
lean_ctor_set_uint8(v___x_1191_, sizeof(void*)*6, v___y_1178_);
lean_ctor_set_uint8(v___x_1191_, sizeof(void*)*6 + 1, v___y_1185_);
lean_ctor_set_uint8(v___x_1191_, sizeof(void*)*6 + 2, v___y_1188_);
v___x_1192_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1192_, 0, v___y_1189_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
lean_ctor_set(v___x_1192_, 2, v___y_1173_);
lean_ctor_set(v___x_1192_, 3, v___y_1182_);
lean_ctor_set(v___x_1192_, 4, v___y_1181_);
lean_ctor_set(v___x_1192_, 5, v___y_1179_);
lean_ctor_set_uint8(v___x_1192_, sizeof(void*)*6, v___y_1180_);
lean_ctor_set_uint8(v___x_1192_, sizeof(void*)*6 + 1, v___y_1190_);
v___y_1159_ = v___y_1186_;
v___y_1160_ = v___y_1187_;
v___y_1161_ = v___y_1178_;
v_val_1162_ = v___x_1192_;
goto v___jp_1158_;
}
}
v___jp_1193_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1210_, 0, v___y_1196_);
lean_ctor_set(v___x_1210_, 1, v___y_1209_);
lean_ctor_set(v___x_1210_, 2, v___y_1204_);
lean_ctor_set(v___x_1210_, 3, v___y_1194_);
lean_ctor_set(v___x_1210_, 4, v___y_1197_);
lean_ctor_set(v___x_1210_, 5, v___y_1202_);
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*6, v___y_1198_);
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*6 + 1, v___y_1205_);
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*6 + 2, v___y_1206_);
v___x_1211_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1211_, 0, v___y_1207_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
lean_ctor_set(v___x_1211_, 2, v___y_1195_);
lean_ctor_set(v___x_1211_, 3, v___y_1203_);
lean_ctor_set(v___x_1211_, 4, v___y_1201_);
lean_ctor_set(v___x_1211_, 5, v___y_1199_);
lean_ctor_set_uint8(v___x_1211_, sizeof(void*)*6, v___y_1200_);
lean_ctor_set_uint8(v___x_1211_, sizeof(void*)*6 + 1, v___y_1208_);
v___y_990_ = v___x_1211_;
v_omitBody_991_ = v___y_1206_;
goto v___jp_989_;
}
v___jp_1212_:
{
lean_object* v_message_1231_; lean_object* v___x_1232_; lean_object* v___x_2973__overap_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v_message_1231_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1215_, v_line_984_, v___y_1230_);
v___x_1232_ = l_ByteArray_empty;
v___x_2973__overap_1233_ = l_Std_Http_Protocol_H1_instEncodeV11Head(v___y_1215_);
v___x_1234_ = lean_apply_2(v___x_2973__overap_1233_, v___x_1232_, v_message_1231_);
v___x_1235_ = l_ByteArray_isEmpty(v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v_data_1236_; lean_object* v_size_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1247_; 
v_data_1236_ = lean_ctor_get(v___y_1216_, 0);
v_size_1237_ = lean_ctor_get(v___y_1216_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___y_1216_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1239_ = v___y_1216_;
v_isShared_1240_ = v_isSharedCheck_1247_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_size_1237_);
lean_inc(v_data_1236_);
lean_dec(v___y_1216_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1247_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
lean_inc_ref(v___x_1234_);
v___x_1241_ = lean_array_push(v_data_1236_, v___x_1234_);
v___x_1242_ = lean_byte_array_size(v___x_1234_);
lean_dec_ref(v___x_1234_);
v___x_1243_ = lean_nat_add(v_size_1237_, v___x_1242_);
lean_dec(v_size_1237_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v___x_1243_);
lean_ctor_set(v___x_1239_, 0, v___x_1241_);
v___x_1245_ = v___x_1239_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
v___y_1194_ = v___y_1213_;
v___y_1195_ = v___y_1214_;
v___y_1196_ = v___y_1217_;
v___y_1197_ = v___y_1218_;
v___y_1198_ = v___y_1219_;
v___y_1199_ = v___y_1220_;
v___y_1200_ = v___y_1221_;
v___y_1201_ = v___y_1222_;
v___y_1202_ = v___y_1223_;
v___y_1203_ = v___y_1224_;
v___y_1204_ = v___y_1225_;
v___y_1205_ = v___y_1226_;
v___y_1206_ = v___y_1227_;
v___y_1207_ = v___y_1228_;
v___y_1208_ = v___y_1229_;
v___y_1209_ = v___x_1245_;
goto v___jp_1193_;
}
}
}
else
{
lean_dec_ref(v___x_1234_);
v___y_1194_ = v___y_1213_;
v___y_1195_ = v___y_1214_;
v___y_1196_ = v___y_1217_;
v___y_1197_ = v___y_1218_;
v___y_1198_ = v___y_1219_;
v___y_1199_ = v___y_1220_;
v___y_1200_ = v___y_1221_;
v___y_1201_ = v___y_1222_;
v___y_1202_ = v___y_1223_;
v___y_1203_ = v___y_1224_;
v___y_1204_ = v___y_1225_;
v___y_1205_ = v___y_1226_;
v___y_1206_ = v___y_1227_;
v___y_1207_ = v___y_1228_;
v___y_1208_ = v___y_1229_;
v___y_1209_ = v___y_1216_;
goto v___jp_1193_;
}
}
v___jp_1248_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_array_get_size(v___y_1266_);
v___x_1269_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1270_ = lean_nat_dec_lt(v___x_1267_, v___x_1268_);
if (v___x_1270_ == 0)
{
v___y_1213_ = v___y_1249_;
v___y_1214_ = v___y_1250_;
v___y_1215_ = v___y_1251_;
v___y_1216_ = v___y_1252_;
v___y_1217_ = v___y_1253_;
v___y_1218_ = v___y_1254_;
v___y_1219_ = v___y_1255_;
v___y_1220_ = v___y_1256_;
v___y_1221_ = v___y_1257_;
v___y_1222_ = v___y_1258_;
v___y_1223_ = v___y_1259_;
v___y_1224_ = v___y_1260_;
v___y_1225_ = v___y_1262_;
v___y_1226_ = v___y_1261_;
v___y_1227_ = v___y_1263_;
v___y_1228_ = v___y_1264_;
v___y_1229_ = v___y_1265_;
v___y_1230_ = v___y_1266_;
goto v___jp_1212_;
}
else
{
lean_object* v___f_1271_; size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___f_1271_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10);
v___x_1272_ = ((size_t)0ULL);
v___x_1273_ = lean_usize_of_nat(v___x_1268_);
lean_inc_ref(v___y_1266_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1269_, v___f_1271_, v___y_1266_, v___x_1272_, v___x_1273_);
v___x_1275_ = lean_unbox(v___x_1274_);
lean_dec(v___x_1274_);
if (v___x_1275_ == 0)
{
v___y_1213_ = v___y_1249_;
v___y_1214_ = v___y_1250_;
v___y_1215_ = v___y_1251_;
v___y_1216_ = v___y_1252_;
v___y_1217_ = v___y_1253_;
v___y_1218_ = v___y_1254_;
v___y_1219_ = v___y_1255_;
v___y_1220_ = v___y_1256_;
v___y_1221_ = v___y_1257_;
v___y_1222_ = v___y_1258_;
v___y_1223_ = v___y_1259_;
v___y_1224_ = v___y_1260_;
v___y_1225_ = v___y_1262_;
v___y_1226_ = v___y_1261_;
v___y_1227_ = v___y_1263_;
v___y_1228_ = v___y_1264_;
v___y_1229_ = v___y_1265_;
v___y_1230_ = v___y_1266_;
goto v___jp_1212_;
}
else
{
lean_object* v___f_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___f_1276_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11);
v___x_1277_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1269_, v___f_1276_, v___y_1266_, v___x_1272_, v___x_1273_, v___x_1277_);
v___y_1213_ = v___y_1249_;
v___y_1214_ = v___y_1250_;
v___y_1215_ = v___y_1251_;
v___y_1216_ = v___y_1252_;
v___y_1217_ = v___y_1253_;
v___y_1218_ = v___y_1254_;
v___y_1219_ = v___y_1255_;
v___y_1220_ = v___y_1256_;
v___y_1221_ = v___y_1257_;
v___y_1222_ = v___y_1258_;
v___y_1223_ = v___y_1259_;
v___y_1224_ = v___y_1260_;
v___y_1225_ = v___y_1262_;
v___y_1226_ = v___y_1261_;
v___y_1227_ = v___y_1263_;
v___y_1228_ = v___y_1264_;
v___y_1229_ = v___y_1265_;
v___y_1230_ = v___x_1278_;
goto v___jp_1212_;
}
}
}
v___jp_1279_:
{
lean_object* v___x_1286_; 
lean_inc_ref(v___y_1280_);
v___x_1286_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___y_1283_, v___y_1280_, v___y_1281_, v___y_1285_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v___x_1287_; 
lean_dec_ref(v_line_984_);
v___x_1287_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_rejectOutgoingFraming(v___y_1283_, v___y_1280_);
v___y_1004_ = v___x_1287_;
goto v___jp_1003_;
}
else
{
lean_object* v_val_1288_; 
lean_dec_ref(v___y_1280_);
v_val_1288_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_val_1288_);
lean_dec_ref_known(v___x_1286_, 1);
v___y_1159_ = v___y_1283_;
v___y_1160_ = v___y_1282_;
v___y_1161_ = v___y_1284_;
v_val_1162_ = v_val_1288_;
goto v___jp_1158_;
}
}
v___jp_1289_:
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = lean_unsigned_to_nat(204u);
v___x_1314_ = lean_nat_dec_eq(v___y_1300_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = lean_unsigned_to_nat(304u);
v___x_1316_ = lean_nat_dec_eq(v___y_1300_, v___x_1315_);
lean_dec(v___y_1300_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = lean_box(9);
v___x_1318_ = l_Std_Http_instBEqStatus_beq(v___y_1311_, v___x_1317_);
lean_dec(v___y_1311_);
if (v___x_1318_ == 0)
{
lean_object* v_messageHead_1319_; uint8_t v_method_1320_; uint8_t v___x_1321_; uint8_t v___x_1322_; 
v_messageHead_1319_ = lean_ctor_get(v___y_1309_, 2);
v_method_1320_ = lean_ctor_get_uint8(v_messageHead_1319_, sizeof(void*)*2);
v___x_1321_ = 9;
v___x_1322_ = l_Std_Http_instBEqMethod_beq(v_method_1320_, v___x_1321_);
if (v___x_1322_ == 0)
{
uint8_t v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = 5;
v___x_1324_ = l_Std_Http_instBEqMethod_beq(v_method_1320_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec(v___y_1299_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
v___y_1280_ = v___y_1290_;
v___y_1281_ = v___y_1291_;
v___y_1282_ = v___y_1305_;
v___y_1283_ = v___y_1306_;
v___y_1284_ = v___y_1296_;
v___y_1285_ = v___y_1310_;
goto v___jp_1279_;
}
else
{
uint16_t v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = 200;
v___x_1326_ = lean_uint16_dec_le(v___x_1325_, v___y_1307_);
if (v___x_1326_ == 0)
{
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec(v___y_1299_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
v___y_1280_ = v___y_1290_;
v___y_1281_ = v___y_1291_;
v___y_1282_ = v___y_1305_;
v___y_1283_ = v___y_1306_;
v___y_1284_ = v___y_1296_;
v___y_1285_ = v___y_1310_;
goto v___jp_1279_;
}
else
{
uint16_t v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = 300;
v___x_1328_ = lean_uint16_dec_lt(v___y_1307_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec(v___y_1299_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
v___y_1280_ = v___y_1290_;
v___y_1281_ = v___y_1291_;
v___y_1282_ = v___y_1305_;
v___y_1283_ = v___y_1306_;
v___y_1284_ = v___y_1296_;
v___y_1285_ = v___y_1310_;
goto v___jp_1279_;
}
else
{
v___y_1172_ = v___y_1290_;
v___y_1173_ = v___y_1292_;
v___y_1174_ = v___y_1291_;
v___y_1175_ = v___y_1294_;
v___y_1176_ = v___y_1295_;
v___y_1177_ = v___y_1293_;
v___y_1178_ = v___y_1296_;
v___y_1179_ = v___y_1297_;
v___y_1180_ = v___y_1298_;
v___y_1181_ = v___y_1299_;
v___y_1182_ = v___y_1302_;
v___y_1183_ = v___y_1301_;
v___y_1184_ = v___y_1304_;
v___y_1185_ = v___y_1303_;
v___y_1186_ = v___y_1306_;
v___y_1187_ = v___y_1305_;
v___y_1188_ = v___y_1308_;
v___y_1189_ = v___y_1309_;
v___y_1190_ = v___y_1312_;
goto v___jp_1171_;
}
}
}
}
else
{
v___y_1172_ = v___y_1290_;
v___y_1173_ = v___y_1292_;
v___y_1174_ = v___y_1291_;
v___y_1175_ = v___y_1294_;
v___y_1176_ = v___y_1295_;
v___y_1177_ = v___y_1293_;
v___y_1178_ = v___y_1296_;
v___y_1179_ = v___y_1297_;
v___y_1180_ = v___y_1298_;
v___y_1181_ = v___y_1299_;
v___y_1182_ = v___y_1302_;
v___y_1183_ = v___y_1301_;
v___y_1184_ = v___y_1304_;
v___y_1185_ = v___y_1303_;
v___y_1186_ = v___y_1306_;
v___y_1187_ = v___y_1305_;
v___y_1188_ = v___y_1308_;
v___y_1189_ = v___y_1309_;
v___y_1190_ = v___y_1312_;
goto v___jp_1171_;
}
}
else
{
v___y_1172_ = v___y_1290_;
v___y_1173_ = v___y_1292_;
v___y_1174_ = v___y_1291_;
v___y_1175_ = v___y_1294_;
v___y_1176_ = v___y_1295_;
v___y_1177_ = v___y_1293_;
v___y_1178_ = v___y_1296_;
v___y_1179_ = v___y_1297_;
v___y_1180_ = v___y_1298_;
v___y_1181_ = v___y_1299_;
v___y_1182_ = v___y_1302_;
v___y_1183_ = v___y_1301_;
v___y_1184_ = v___y_1304_;
v___y_1185_ = v___y_1303_;
v___y_1186_ = v___y_1306_;
v___y_1187_ = v___y_1305_;
v___y_1188_ = v___y_1308_;
v___y_1189_ = v___y_1309_;
v___y_1190_ = v___y_1312_;
goto v___jp_1171_;
}
}
else
{
lean_dec(v___y_1311_);
v___y_1172_ = v___y_1290_;
v___y_1173_ = v___y_1292_;
v___y_1174_ = v___y_1291_;
v___y_1175_ = v___y_1294_;
v___y_1176_ = v___y_1295_;
v___y_1177_ = v___y_1293_;
v___y_1178_ = v___y_1296_;
v___y_1179_ = v___y_1297_;
v___y_1180_ = v___y_1298_;
v___y_1181_ = v___y_1299_;
v___y_1182_ = v___y_1302_;
v___y_1183_ = v___y_1301_;
v___y_1184_ = v___y_1304_;
v___y_1185_ = v___y_1303_;
v___y_1186_ = v___y_1306_;
v___y_1187_ = v___y_1305_;
v___y_1188_ = v___y_1308_;
v___y_1189_ = v___y_1309_;
v___y_1190_ = v___y_1312_;
goto v___jp_1171_;
}
}
else
{
lean_dec(v___y_1311_);
lean_dec(v___y_1300_);
v___y_1172_ = v___y_1290_;
v___y_1173_ = v___y_1292_;
v___y_1174_ = v___y_1291_;
v___y_1175_ = v___y_1294_;
v___y_1176_ = v___y_1295_;
v___y_1177_ = v___y_1293_;
v___y_1178_ = v___y_1296_;
v___y_1179_ = v___y_1297_;
v___y_1180_ = v___y_1298_;
v___y_1181_ = v___y_1299_;
v___y_1182_ = v___y_1302_;
v___y_1183_ = v___y_1301_;
v___y_1184_ = v___y_1304_;
v___y_1185_ = v___y_1303_;
v___y_1186_ = v___y_1306_;
v___y_1187_ = v___y_1305_;
v___y_1188_ = v___y_1308_;
v___y_1189_ = v___y_1309_;
v___y_1190_ = v___y_1312_;
goto v___jp_1171_;
}
}
v___jp_1329_:
{
lean_object* v_status_1350_; uint16_t v___x_1351_; lean_object* v_code_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
v_status_1350_ = lean_ctor_get(v_line_984_, 0);
v___x_1351_ = l_Std_Http_Status_toCode(v_status_1350_);
v_code_1352_ = lean_uint16_to_nat(v___x_1351_);
v___x_1353_ = lean_unsigned_to_nat(100u);
v___x_1354_ = lean_nat_dec_le(v___x_1353_, v_code_1352_);
if (v___x_1354_ == 0)
{
lean_inc(v_status_1350_);
v___y_1290_ = v___y_1330_;
v___y_1291_ = v___y_1349_;
v___y_1292_ = v___y_1331_;
v___y_1293_ = v___y_1334_;
v___y_1294_ = v___y_1332_;
v___y_1295_ = v___y_1333_;
v___y_1296_ = v___y_1335_;
v___y_1297_ = v___y_1336_;
v___y_1298_ = v___y_1337_;
v___y_1299_ = v___y_1338_;
v___y_1300_ = v_code_1352_;
v___y_1301_ = v___y_1339_;
v___y_1302_ = v___y_1340_;
v___y_1303_ = v___y_1341_;
v___y_1304_ = v___y_1342_;
v___y_1305_ = v___y_1343_;
v___y_1306_ = v___y_1344_;
v___y_1307_ = v___x_1351_;
v___y_1308_ = v___y_1345_;
v___y_1309_ = v___y_1346_;
v___y_1310_ = v___y_1347_;
v___y_1311_ = v_status_1350_;
v___y_1312_ = v___y_1348_;
goto v___jp_1289_;
}
else
{
lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1355_ = lean_unsigned_to_nat(200u);
v___x_1356_ = lean_nat_dec_lt(v_code_1352_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_inc(v_status_1350_);
v___y_1290_ = v___y_1330_;
v___y_1291_ = v___y_1349_;
v___y_1292_ = v___y_1331_;
v___y_1293_ = v___y_1334_;
v___y_1294_ = v___y_1332_;
v___y_1295_ = v___y_1333_;
v___y_1296_ = v___y_1335_;
v___y_1297_ = v___y_1336_;
v___y_1298_ = v___y_1337_;
v___y_1299_ = v___y_1338_;
v___y_1300_ = v_code_1352_;
v___y_1301_ = v___y_1339_;
v___y_1302_ = v___y_1340_;
v___y_1303_ = v___y_1341_;
v___y_1304_ = v___y_1342_;
v___y_1305_ = v___y_1343_;
v___y_1306_ = v___y_1344_;
v___y_1307_ = v___x_1351_;
v___y_1308_ = v___y_1345_;
v___y_1309_ = v___y_1346_;
v___y_1310_ = v___y_1347_;
v___y_1311_ = v_status_1350_;
v___y_1312_ = v___y_1348_;
goto v___jp_1289_;
}
else
{
v___y_1172_ = v___y_1330_;
v___y_1173_ = v___y_1331_;
v___y_1174_ = v___y_1349_;
v___y_1175_ = v___y_1332_;
v___y_1176_ = v___y_1333_;
v___y_1177_ = v___y_1334_;
v___y_1178_ = v___y_1335_;
v___y_1179_ = v___y_1336_;
v___y_1180_ = v___y_1337_;
v___y_1181_ = v___y_1338_;
v___y_1182_ = v___y_1340_;
v___y_1183_ = v___y_1339_;
v___y_1184_ = v___y_1342_;
v___y_1185_ = v___y_1341_;
v___y_1186_ = v___y_1344_;
v___y_1187_ = v___y_1343_;
v___y_1188_ = v___y_1345_;
v___y_1189_ = v___y_1346_;
v___y_1190_ = v___y_1348_;
goto v___jp_1171_;
}
}
}
v___jp_1357_:
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_box(0);
v___y_1330_ = v___y_1358_;
v___y_1331_ = v___y_1359_;
v___y_1332_ = v___y_1360_;
v___y_1333_ = v___y_1361_;
v___y_1334_ = v___y_1362_;
v___y_1335_ = v___y_1363_;
v___y_1336_ = v___y_1364_;
v___y_1337_ = v___y_1365_;
v___y_1338_ = v___y_1366_;
v___y_1339_ = v___y_1367_;
v___y_1340_ = v___y_1368_;
v___y_1341_ = v___y_1369_;
v___y_1342_ = v___y_1370_;
v___y_1343_ = v___y_1372_;
v___y_1344_ = v___y_1371_;
v___y_1345_ = v___y_1373_;
v___y_1346_ = v___y_1374_;
v___y_1347_ = v___y_1376_;
v___y_1348_ = v___y_1375_;
v___y_1349_ = v___x_1377_;
goto v___jp_1329_;
}
v___jp_1378_:
{
uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1398_ = 1;
v___x_1399_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1398_, v_line_984_);
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = lean_array_get_size(v___x_1399_);
v___x_1402_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1403_ = lean_nat_dec_lt(v___x_1400_, v___x_1401_);
if (v___x_1403_ == 0)
{
lean_dec_ref(v___x_1399_);
lean_dec_ref(v___f_985_);
v___y_1358_ = v___y_1379_;
v___y_1359_ = v___y_1380_;
v___y_1360_ = v___y_1381_;
v___y_1361_ = v___y_1382_;
v___y_1362_ = v___y_1383_;
v___y_1363_ = v___y_1384_;
v___y_1364_ = v___y_1386_;
v___y_1365_ = v___y_1387_;
v___y_1366_ = v___y_1388_;
v___y_1367_ = v___y_1389_;
v___y_1368_ = v___y_1390_;
v___y_1369_ = v___y_1392_;
v___y_1370_ = v___y_1391_;
v___y_1371_ = v___y_1394_;
v___y_1372_ = v___y_1393_;
v___y_1373_ = v___y_1395_;
v___y_1374_ = v___y_1396_;
v___y_1375_ = v___y_1397_;
v___y_1376_ = v___x_1403_;
goto v___jp_1357_;
}
else
{
size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1404_ = ((size_t)0ULL);
v___x_1405_ = lean_usize_of_nat(v___x_1401_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1402_, v___f_985_, v___x_1399_, v___x_1404_, v___x_1405_);
v___x_1407_ = lean_unbox(v___x_1406_);
if (v___x_1407_ == 0)
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_unbox(v___x_1406_);
lean_dec(v___x_1406_);
v___y_1358_ = v___y_1379_;
v___y_1359_ = v___y_1380_;
v___y_1360_ = v___y_1381_;
v___y_1361_ = v___y_1382_;
v___y_1362_ = v___y_1383_;
v___y_1363_ = v___y_1384_;
v___y_1364_ = v___y_1386_;
v___y_1365_ = v___y_1387_;
v___y_1366_ = v___y_1388_;
v___y_1367_ = v___y_1389_;
v___y_1368_ = v___y_1390_;
v___y_1369_ = v___y_1392_;
v___y_1370_ = v___y_1391_;
v___y_1371_ = v___y_1394_;
v___y_1372_ = v___y_1393_;
v___y_1373_ = v___y_1395_;
v___y_1374_ = v___y_1396_;
v___y_1375_ = v___y_1397_;
v___y_1376_ = v___x_1408_;
goto v___jp_1357_;
}
else
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_1398_, v_line_984_, v___y_1385_);
v___x_1410_ = lean_unbox(v___x_1406_);
lean_dec(v___x_1406_);
v___y_1330_ = v___y_1379_;
v___y_1331_ = v___y_1380_;
v___y_1332_ = v___y_1381_;
v___y_1333_ = v___y_1382_;
v___y_1334_ = v___y_1383_;
v___y_1335_ = v___y_1384_;
v___y_1336_ = v___y_1386_;
v___y_1337_ = v___y_1387_;
v___y_1338_ = v___y_1388_;
v___y_1339_ = v___y_1389_;
v___y_1340_ = v___y_1390_;
v___y_1341_ = v___y_1392_;
v___y_1342_ = v___y_1391_;
v___y_1343_ = v___y_1393_;
v___y_1344_ = v___y_1394_;
v___y_1345_ = v___y_1395_;
v___y_1346_ = v___y_1396_;
v___y_1347_ = v___x_1410_;
v___y_1348_ = v___y_1397_;
v___y_1349_ = v___x_1409_;
goto v___jp_1329_;
}
}
}
v___jp_1411_:
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_box(1);
v___x_1430_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1416_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_dec(v_date_1426_);
lean_dec(v_error_1425_);
lean_dec_ref(v_events_1424_);
lean_dec_ref(v_config_1423_);
lean_dec(v_userDataBytes_1422_);
lean_dec(v_messageHead_1418_);
lean_dec(v_knownSize_1417_);
lean_dec(v_state_1416_);
lean_dec_ref(v_outputData_1415_);
lean_dec_ref(v_userData_1414_);
lean_dec_ref(v_reader_1413_);
lean_dec_ref(v___f_985_);
lean_dec_ref(v_line_984_);
v___y_990_ = v___y_1412_;
v_omitBody_991_ = v_omitBody_1421_;
goto v___jp_989_;
}
else
{
if (v_sentMessage_1419_ == 0)
{
lean_object* v_status_1431_; uint8_t v___x_1432_; uint16_t v___x_1433_; uint16_t v___x_1434_; uint8_t v___x_1435_; 
v_status_1431_ = lean_ctor_get(v_line_984_, 0);
v___x_1432_ = 0;
v___x_1433_ = 100;
v___x_1434_ = l_Std_Http_Status_toCode(v_status_1431_);
v___x_1435_ = lean_uint16_dec_le(v___x_1433_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_dec(v_knownSize_1417_);
v___y_1379_ = v___y_1412_;
v___y_1380_ = v_config_1423_;
v___y_1381_ = v_userData_1414_;
v___y_1382_ = v_outputData_1415_;
v___y_1383_ = v_messageHead_1418_;
v___y_1384_ = v_sentMessage_1419_;
v___y_1385_ = v___x_1435_;
v___y_1386_ = v_date_1426_;
v___y_1387_ = v_keepAlive_1427_;
v___y_1388_ = v_error_1425_;
v___y_1389_ = v_userDataBytes_1422_;
v___y_1390_ = v_events_1424_;
v___y_1391_ = v_state_1416_;
v___y_1392_ = v_userClosedBody_1420_;
v___y_1393_ = v___x_1430_;
v___y_1394_ = v___x_1432_;
v___y_1395_ = v_omitBody_1421_;
v___y_1396_ = v_reader_1413_;
v___y_1397_ = v_pullBodyStalled_1428_;
goto v___jp_1378_;
}
else
{
uint16_t v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = 200;
v___x_1437_ = lean_uint16_dec_lt(v___x_1434_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_dec(v_knownSize_1417_);
v___y_1379_ = v___y_1412_;
v___y_1380_ = v_config_1423_;
v___y_1381_ = v_userData_1414_;
v___y_1382_ = v_outputData_1415_;
v___y_1383_ = v_messageHead_1418_;
v___y_1384_ = v_sentMessage_1419_;
v___y_1385_ = v___x_1437_;
v___y_1386_ = v_date_1426_;
v___y_1387_ = v_keepAlive_1427_;
v___y_1388_ = v_error_1425_;
v___y_1389_ = v_userDataBytes_1422_;
v___y_1390_ = v_events_1424_;
v___y_1391_ = v_state_1416_;
v___y_1392_ = v_userClosedBody_1420_;
v___y_1393_ = v___x_1430_;
v___y_1394_ = v___x_1432_;
v___y_1395_ = v_omitBody_1421_;
v___y_1396_ = v_reader_1413_;
v___y_1397_ = v_pullBodyStalled_1428_;
goto v___jp_1378_;
}
else
{
lean_object* v_messageHead_1438_; uint8_t v___x_1439_; uint8_t v___x_1440_; uint8_t v___x_1441_; 
lean_dec_ref(v___f_985_);
v_messageHead_1438_ = lean_ctor_get(v_reader_1413_, 2);
v___x_1439_ = l_Std_Http_Protocol_H1_Message_Head_version(v___x_1432_, v_messageHead_1438_);
v___x_1440_ = 1;
v___x_1441_ = l_Std_Http_instBEqVersion_beq(v___x_1439_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_dec(v_date_1426_);
lean_dec(v_error_1425_);
lean_dec_ref(v_events_1424_);
lean_dec_ref(v_config_1423_);
lean_dec(v_userDataBytes_1422_);
lean_dec(v_messageHead_1418_);
lean_dec(v_knownSize_1417_);
lean_dec(v_state_1416_);
lean_dec_ref(v_outputData_1415_);
lean_dec_ref(v_userData_1414_);
lean_dec_ref(v_reader_1413_);
lean_dec_ref(v_line_984_);
v___y_1004_ = v___y_1412_;
goto v___jp_1003_;
}
else
{
uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
lean_dec_ref(v___y_1412_);
v___x_1442_ = 1;
v___x_1443_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1442_, v_line_984_);
v___x_1444_ = lean_unsigned_to_nat(0u);
v___x_1445_ = lean_array_get_size(v___x_1443_);
v___x_1446_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_1447_ = lean_nat_dec_lt(v___x_1444_, v___x_1445_);
if (v___x_1447_ == 0)
{
v___y_1249_ = v_knownSize_1417_;
v___y_1250_ = v_config_1423_;
v___y_1251_ = v___x_1442_;
v___y_1252_ = v_outputData_1415_;
v___y_1253_ = v_userData_1414_;
v___y_1254_ = v_messageHead_1418_;
v___y_1255_ = v_sentMessage_1419_;
v___y_1256_ = v_date_1426_;
v___y_1257_ = v_keepAlive_1427_;
v___y_1258_ = v_error_1425_;
v___y_1259_ = v_userDataBytes_1422_;
v___y_1260_ = v_events_1424_;
v___y_1261_ = v_userClosedBody_1420_;
v___y_1262_ = v_state_1416_;
v___y_1263_ = v_omitBody_1421_;
v___y_1264_ = v_reader_1413_;
v___y_1265_ = v_pullBodyStalled_1428_;
v___y_1266_ = v___x_1443_;
goto v___jp_1248_;
}
else
{
lean_object* v___f_1448_; size_t v___x_1449_; size_t v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___f_1448_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13);
v___x_1449_ = ((size_t)0ULL);
v___x_1450_ = lean_usize_of_nat(v___x_1445_);
lean_inc_ref(v___x_1443_);
v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1446_, v___f_1448_, v___x_1443_, v___x_1449_, v___x_1450_);
v___x_1452_ = lean_unbox(v___x_1451_);
lean_dec(v___x_1451_);
if (v___x_1452_ == 0)
{
v___y_1249_ = v_knownSize_1417_;
v___y_1250_ = v_config_1423_;
v___y_1251_ = v___x_1442_;
v___y_1252_ = v_outputData_1415_;
v___y_1253_ = v_userData_1414_;
v___y_1254_ = v_messageHead_1418_;
v___y_1255_ = v_sentMessage_1419_;
v___y_1256_ = v_date_1426_;
v___y_1257_ = v_keepAlive_1427_;
v___y_1258_ = v_error_1425_;
v___y_1259_ = v_userDataBytes_1422_;
v___y_1260_ = v_events_1424_;
v___y_1261_ = v_userClosedBody_1420_;
v___y_1262_ = v_state_1416_;
v___y_1263_ = v_omitBody_1421_;
v___y_1264_ = v_reader_1413_;
v___y_1265_ = v_pullBodyStalled_1428_;
v___y_1266_ = v___x_1443_;
goto v___jp_1248_;
}
else
{
lean_object* v___f_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___f_1453_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14);
v___x_1454_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12));
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1446_, v___f_1453_, v___x_1443_, v___x_1449_, v___x_1450_, v___x_1454_);
v___y_1249_ = v_knownSize_1417_;
v___y_1250_ = v_config_1423_;
v___y_1251_ = v___x_1442_;
v___y_1252_ = v_outputData_1415_;
v___y_1253_ = v_userData_1414_;
v___y_1254_ = v_messageHead_1418_;
v___y_1255_ = v_sentMessage_1419_;
v___y_1256_ = v_date_1426_;
v___y_1257_ = v_keepAlive_1427_;
v___y_1258_ = v_error_1425_;
v___y_1259_ = v_userDataBytes_1422_;
v___y_1260_ = v_events_1424_;
v___y_1261_ = v_userClosedBody_1420_;
v___y_1262_ = v_state_1416_;
v___y_1263_ = v_omitBody_1421_;
v___y_1264_ = v_reader_1413_;
v___y_1265_ = v_pullBodyStalled_1428_;
v___y_1266_ = v___x_1455_;
goto v___jp_1248_;
}
}
}
}
}
}
else
{
lean_dec(v_date_1426_);
lean_dec(v_error_1425_);
lean_dec_ref(v_events_1424_);
lean_dec_ref(v_config_1423_);
lean_dec(v_userDataBytes_1422_);
lean_dec(v_messageHead_1418_);
lean_dec(v_knownSize_1417_);
lean_dec(v_state_1416_);
lean_dec_ref(v_outputData_1415_);
lean_dec_ref(v_userData_1414_);
lean_dec_ref(v_reader_1413_);
lean_dec_ref(v___f_985_);
lean_dec_ref(v_line_984_);
v___y_990_ = v___y_1412_;
v_omitBody_991_ = v_omitBody_1421_;
goto v___jp_989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object* v_body_1514_, lean_object* v_close_1515_, lean_object* v_isClosed_1516_, lean_object* v_line_1517_, lean_object* v___f_1518_, lean_object* v_machine_1519_, lean_object* v_x_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(v_body_1514_, v_close_1515_, v_isClosed_1516_, v_line_1517_, v___f_1518_, v_machine_1519_, v_x_1520_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1524_, lean_object* v_machine_1525_, lean_object* v_res_1526_){
_start:
{
lean_object* v_close_1528_; lean_object* v_isClosed_1529_; lean_object* v_getKnownSize_1530_; lean_object* v_line_1531_; lean_object* v_body_1532_; lean_object* v___f_1533_; lean_object* v___f_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_close_1528_ = lean_ctor_get(v_inst_1524_, 1);
lean_inc_ref(v_close_1528_);
v_isClosed_1529_ = lean_ctor_get(v_inst_1524_, 2);
lean_inc_ref(v_isClosed_1529_);
v_getKnownSize_1530_ = lean_ctor_get(v_inst_1524_, 5);
lean_inc_ref(v_getKnownSize_1530_);
lean_dec_ref(v_inst_1524_);
v_line_1531_ = lean_ctor_get(v_res_1526_, 0);
lean_inc_ref(v_line_1531_);
v_body_1532_ = lean_ctor_get(v_res_1526_, 1);
lean_inc_n(v_body_1532_, 2);
lean_dec_ref(v_res_1526_);
v___f_1533_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___closed__0));
v___f_1534_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed), 8, 6);
lean_closure_set(v___f_1534_, 0, v_body_1532_);
lean_closure_set(v___f_1534_, 1, v_close_1528_);
lean_closure_set(v___f_1534_, 2, v_isClosed_1529_);
lean_closure_set(v___f_1534_, 3, v_line_1531_);
lean_closure_set(v___f_1534_, 4, v___f_1533_);
lean_closure_set(v___f_1534_, 5, v_machine_1525_);
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = 0;
v___x_1537_ = lean_apply_2(v_getKnownSize_1530_, v_body_1532_, lean_box(0));
v___x_1538_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1535_, v___x_1536_, v___x_1537_, v___f_1534_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1539_, lean_object* v_machine_1540_, lean_object* v_res_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1539_, v_machine_1540_, v_res_1541_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1544_, lean_object* v_inst_1545_, lean_object* v_machine_1546_, lean_object* v_res_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1545_, v_machine_1546_, v_res_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1550_, lean_object* v_inst_1551_, lean_object* v_machine_1552_, lean_object* v_res_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1550_, v_inst_1551_, v_machine_1552_, v_res_1553_);
return v_res_1555_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0(lean_object* v_x_1556_, lean_object* v_x_1557_){
_start:
{
if (lean_obj_tag(v_x_1556_) == 0)
{
if (lean_obj_tag(v_x_1557_) == 0)
{
uint8_t v___x_1558_; 
v___x_1558_ = 1;
return v___x_1558_;
}
else
{
uint8_t v___x_1559_; 
v___x_1559_ = 0;
return v___x_1559_;
}
}
else
{
if (lean_obj_tag(v_x_1557_) == 0)
{
uint8_t v___x_1560_; 
v___x_1560_ = 0;
return v___x_1560_;
}
else
{
lean_object* v_val_1561_; lean_object* v_val_1562_; uint8_t v___x_1563_; 
v_val_1561_ = lean_ctor_get(v_x_1556_, 0);
v_val_1562_ = lean_ctor_get(v_x_1557_, 0);
v___x_1563_ = lean_int_dec_eq(v_val_1561_, v_val_1562_);
return v___x_1563_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0___boxed(lean_object* v_x_1564_, lean_object* v_x_1565_){
_start:
{
uint8_t v_res_1566_; lean_object* v_r_1567_; 
v_res_1566_ = l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0(v_x_1564_, v_x_1565_);
lean_dec(v_x_1565_);
lean_dec(v_x_1564_);
v_r_1567_ = lean_box(v_res_1566_);
return v_r_1567_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__2(lean_object* v_a_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_nat_to_int(v_a_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__3(lean_object* v_a_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Rat_ofInt(v_a_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0(lean_object* v_tz_1572_, lean_object* v___x_1573_, lean_object* v_second_1574_, lean_object* v_nano_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v_offset_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_nanos_1581_; lean_object* v___x_1582_; lean_object* v_nanos_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_offset_1577_ = lean_ctor_get(v_tz_1572_, 0);
v___x_1578_ = lean_nat_to_int(v___x_1573_);
v___x_1579_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_1580_ = lean_int_mul(v_second_1574_, v___x_1579_);
v_nanos_1581_ = lean_int_add(v___x_1580_, v_nano_1575_);
lean_dec(v___x_1580_);
v___x_1582_ = lean_int_mul(v_offset_1577_, v___x_1579_);
v_nanos_1583_ = lean_int_add(v___x_1582_, v___x_1578_);
lean_dec(v___x_1578_);
lean_dec(v___x_1582_);
v___x_1584_ = lean_int_add(v_nanos_1581_, v_nanos_1583_);
lean_dec(v_nanos_1583_);
lean_dec(v_nanos_1581_);
v___x_1585_ = l_Std_Time_Duration_ofNanoseconds(v___x_1584_);
lean_dec(v___x_1584_);
v___x_1586_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___boxed(lean_object* v_tz_1587_, lean_object* v___x_1588_, lean_object* v_second_1589_, lean_object* v_nano_1590_, lean_object* v_x_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0(v_tz_1587_, v___x_1588_, v_second_1589_, v_nano_1590_, v_x_1591_);
lean_dec(v_nano_1590_);
lean_dec(v_second_1589_);
lean_dec_ref(v_tz_1587_);
return v_res_1592_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = lean_nat_to_int(v___x_1593_);
return v___x_1594_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__2));
v___x_1599_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0);
v___x_1600_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_1599_, v___x_1598_, v___x_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(lean_object* v_config_1601_, lean_object* v_state_1602_){
_start:
{
uint8_t v_generateDate_1604_; 
v_generateDate_1604_ = lean_ctor_get_uint8(v_config_1601_, sizeof(void*)*26 + 1);
if (v_generateDate_1604_ == 0)
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_state_1602_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_get_current_time();
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1679_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1679_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1679_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v_second_1611_; lean_object* v_nano_1612_; lean_object* v_machine_1613_; lean_object* v_requestStream_1614_; lean_object* v_keepAliveTimeout_1615_; lean_object* v_currentTimeout_1616_; lean_object* v_headerTimeout_1617_; lean_object* v_response_1618_; lean_object* v_respStream_1619_; uint8_t v_requiresData_1620_; lean_object* v_expectData_1621_; uint8_t v_handlerDispatched_1622_; lean_object* v_pendingHead_1623_; uint8_t v_requestFinalOffered_1624_; lean_object* v_handlerTask_1625_; lean_object* v_dateSecond_1626_; uint8_t v_peerClosed_1627_; uint8_t v_requestEnded_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v_second_1611_ = lean_ctor_get(v_a_1607_, 0);
v_nano_1612_ = lean_ctor_get(v_a_1607_, 1);
v_machine_1613_ = lean_ctor_get(v_state_1602_, 0);
lean_inc_ref(v_machine_1613_);
v_requestStream_1614_ = lean_ctor_get(v_state_1602_, 1);
v_keepAliveTimeout_1615_ = lean_ctor_get(v_state_1602_, 2);
v_currentTimeout_1616_ = lean_ctor_get(v_state_1602_, 3);
v_headerTimeout_1617_ = lean_ctor_get(v_state_1602_, 4);
v_response_1618_ = lean_ctor_get(v_state_1602_, 5);
v_respStream_1619_ = lean_ctor_get(v_state_1602_, 6);
v_requiresData_1620_ = lean_ctor_get_uint8(v_state_1602_, sizeof(void*)*11);
v_expectData_1621_ = lean_ctor_get(v_state_1602_, 7);
v_handlerDispatched_1622_ = lean_ctor_get_uint8(v_state_1602_, sizeof(void*)*11 + 1);
v_pendingHead_1623_ = lean_ctor_get(v_state_1602_, 8);
v_requestFinalOffered_1624_ = lean_ctor_get_uint8(v_state_1602_, sizeof(void*)*11 + 2);
v_handlerTask_1625_ = lean_ctor_get(v_state_1602_, 9);
v_dateSecond_1626_ = lean_ctor_get(v_state_1602_, 10);
v_peerClosed_1627_ = lean_ctor_get_uint8(v_state_1602_, sizeof(void*)*11 + 3);
v_requestEnded_1628_ = lean_ctor_get_uint8(v_state_1602_, sizeof(void*)*11 + 4);
lean_inc(v_second_1611_);
v___x_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_second_1611_);
v___x_1630_ = l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0(v_dateSecond_1626_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1664_; 
lean_inc(v_handlerTask_1625_);
lean_inc(v_pendingHead_1623_);
lean_inc(v_expectData_1621_);
lean_inc(v_respStream_1619_);
lean_inc_ref(v_response_1618_);
lean_inc(v_headerTimeout_1617_);
lean_inc(v_currentTimeout_1616_);
lean_inc(v_keepAliveTimeout_1615_);
lean_inc_ref(v_requestStream_1614_);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_state_1602_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; lean_object* v_unused_1666_; lean_object* v_unused_1667_; lean_object* v_unused_1668_; lean_object* v_unused_1669_; lean_object* v_unused_1670_; lean_object* v_unused_1671_; lean_object* v_unused_1672_; lean_object* v_unused_1673_; lean_object* v_unused_1674_; lean_object* v_unused_1675_; 
v_unused_1665_ = lean_ctor_get(v_state_1602_, 10);
lean_dec(v_unused_1665_);
v_unused_1666_ = lean_ctor_get(v_state_1602_, 9);
lean_dec(v_unused_1666_);
v_unused_1667_ = lean_ctor_get(v_state_1602_, 8);
lean_dec(v_unused_1667_);
v_unused_1668_ = lean_ctor_get(v_state_1602_, 7);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_state_1602_, 6);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_state_1602_, 5);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_state_1602_, 4);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_state_1602_, 3);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_state_1602_, 2);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_state_1602_, 1);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_state_1602_, 0);
lean_dec(v_unused_1675_);
v___x_1632_ = v_state_1602_;
v_isShared_1633_ = v_isSharedCheck_1664_;
goto v_resetjp_1631_;
}
else
{
lean_dec(v_state_1602_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1664_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v_reader_1636_; lean_object* v_writer_1637_; lean_object* v_config_1638_; lean_object* v_events_1639_; lean_object* v_error_1640_; uint8_t v_keepAlive_1641_; uint8_t v_pullBodyStalled_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1662_; 
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3);
v_reader_1636_ = lean_ctor_get(v_machine_1613_, 0);
v_writer_1637_ = lean_ctor_get(v_machine_1613_, 1);
v_config_1638_ = lean_ctor_get(v_machine_1613_, 2);
v_events_1639_ = lean_ctor_get(v_machine_1613_, 3);
v_error_1640_ = lean_ctor_get(v_machine_1613_, 4);
v_keepAlive_1641_ = lean_ctor_get_uint8(v_machine_1613_, sizeof(void*)*6);
v_pullBodyStalled_1642_ = lean_ctor_get_uint8(v_machine_1613_, sizeof(void*)*6 + 1);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_machine_1613_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v_machine_1613_, 5);
lean_dec(v_unused_1663_);
v___x_1644_ = v_machine_1613_;
v_isShared_1645_ = v_isSharedCheck_1662_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_error_1640_);
lean_inc(v_events_1639_);
lean_inc(v_config_1638_);
lean_inc(v_writer_1637_);
lean_inc(v_reader_1636_);
lean_dec(v_machine_1613_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1662_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_tz_1646_; lean_object* v___f_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
v_tz_1646_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_1635_, v_a_1607_);
lean_inc(v_nano_1612_);
lean_inc(v_second_1611_);
lean_inc_ref(v_tz_1646_);
v___f_1647_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1647_, 0, v_tz_1646_);
lean_closure_set(v___f_1647_, 1, v___x_1634_);
lean_closure_set(v___f_1647_, 2, v_second_1611_);
lean_closure_set(v___f_1647_, 3, v_nano_1612_);
v___x_1648_ = lean_mk_thunk(v___f_1647_);
v___x_1649_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v_a_1607_);
lean_ctor_set(v___x_1649_, 2, v___x_1635_);
lean_ctor_set(v___x_1649_, 3, v_tz_1646_);
v___x_1650_ = l_Std_Time_DateTime_toHTTPDateString(v___x_1649_);
v___x_1651_ = l_Std_Http_Header_Value_ofString_x21(v___x_1650_);
v___x_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 5, v___x_1652_);
v___x_1654_ = v___x_1644_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_reader_1636_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_writer_1637_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_config_1638_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_events_1639_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_error_1640_);
lean_ctor_set(v_reuseFailAlloc_1661_, 5, v___x_1652_);
lean_ctor_set_uint8(v_reuseFailAlloc_1661_, sizeof(void*)*6, v_keepAlive_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1661_, sizeof(void*)*6 + 1, v_pullBodyStalled_1642_);
v___x_1654_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1656_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 10, v___x_1629_);
lean_ctor_set(v___x_1632_, 0, v___x_1654_);
v___x_1656_ = v___x_1632_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_requestStream_1614_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_keepAliveTimeout_1615_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_currentTimeout_1616_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_headerTimeout_1617_);
lean_ctor_set(v_reuseFailAlloc_1660_, 5, v_response_1618_);
lean_ctor_set(v_reuseFailAlloc_1660_, 6, v_respStream_1619_);
lean_ctor_set(v_reuseFailAlloc_1660_, 7, v_expectData_1621_);
lean_ctor_set(v_reuseFailAlloc_1660_, 8, v_pendingHead_1623_);
lean_ctor_set(v_reuseFailAlloc_1660_, 9, v_handlerTask_1625_);
lean_ctor_set(v_reuseFailAlloc_1660_, 10, v___x_1629_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*11, v_requiresData_1620_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*11 + 1, v_handlerDispatched_1622_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*11 + 2, v_requestFinalOffered_1624_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*11 + 3, v_peerClosed_1627_);
lean_ctor_set_uint8(v_reuseFailAlloc_1660_, sizeof(void*)*11 + 4, v_requestEnded_1628_);
v___x_1656_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1658_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1656_);
v___x_1658_ = v___x_1609_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
}
else
{
lean_object* v___x_1677_; 
lean_dec_ref_known(v___x_1629_, 1);
lean_dec_ref(v_machine_1613_);
lean_dec(v_a_1607_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v_state_1602_);
v___x_1677_ = v___x_1609_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_state_1602_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec_ref(v_state_1602_);
v_a_1680_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1606_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1606_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___boxed(lean_object* v_config_1688_, lean_object* v_state_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(v_config_1688_, v_state_1689_);
lean_dec_ref(v_config_1688_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate(lean_object* v_00_u03b2_1692_, lean_object* v_config_1693_, lean_object* v_state_1694_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(v_config_1693_, v_state_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___boxed(lean_object* v_00_u03b2_1697_, lean_object* v_config_1698_, lean_object* v_state_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate(v_00_u03b2_1697_, v_config_1698_, v_state_1699_);
lean_dec_ref(v_config_1698_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__1(lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_nat_to_int(v_a_1702_);
v___x_1704_ = l_Rat_ofInt(v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0(lean_object* v_x_1705_, lean_object* v_x_1706_){
_start:
{
if (lean_obj_tag(v_x_1705_) == 0)
{
if (lean_obj_tag(v_x_1706_) == 0)
{
uint8_t v___x_1707_; 
v___x_1707_ = 1;
return v___x_1707_;
}
else
{
uint8_t v___x_1708_; 
v___x_1708_ = 0;
return v___x_1708_;
}
}
else
{
if (lean_obj_tag(v_x_1706_) == 0)
{
uint8_t v___x_1709_; 
v___x_1709_ = 0;
return v___x_1709_;
}
else
{
lean_object* v_val_1710_; lean_object* v_val_1711_; uint8_t v___x_1712_; 
v_val_1710_ = lean_ctor_get(v_x_1705_, 0);
v_val_1711_ = lean_ctor_get(v_x_1706_, 0);
v___x_1712_ = l_Std_Http_Body_instBEqLength_beq(v_val_1710_, v_val_1711_);
return v___x_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0___boxed(lean_object* v_x_1713_, lean_object* v_x_1714_){
_start:
{
uint8_t v_res_1715_; lean_object* v_r_1716_; 
v_res_1715_ = l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0(v_x_1713_, v_x_1714_);
lean_dec(v_x_1714_);
lean_dec(v_x_1713_);
v_r_1716_ = lean_box(v_res_1715_);
return v_r_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__0(lean_object* v___y_1717_){
_start:
{
if (lean_obj_tag(v___y_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
v_a_1718_ = lean_ctor_get(v___y_1717_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___y_1717_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___y_1717_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___y_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1734_; 
v_a_1726_ = lean_ctor_get(v___y_1717_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___y_1717_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1728_ = v___y_1717_;
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___y_1717_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v_fst_1730_; lean_object* v___x_1732_; 
v_fst_1730_ = lean_ctor_get(v_a_1726_, 0);
lean_inc(v_fst_1730_);
lean_dec(v_a_1726_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v_fst_1730_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_fst_1730_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1(lean_object* v_mutex_1735_, lean_object* v_x_1736_){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_io_basemutex_unlock(v_mutex_1735_);
v___x_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1___boxed(lean_object* v_mutex_1741_, lean_object* v_x_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1(v_mutex_1741_, v_x_1742_);
lean_dec(v_x_1742_);
lean_dec(v_mutex_1741_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2(lean_object* v_k_1745_, lean_object* v_ref_1746_, lean_object* v_x_1747_){
_start:
{
if (lean_obj_tag(v_x_1747_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1757_; 
lean_dec(v_ref_1746_);
lean_dec_ref(v_k_1745_);
v_a_1749_ = lean_ctor_get(v_x_1747_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_x_1747_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1751_ = v_x_1747_;
v_isShared_1752_ = v_isSharedCheck_1757_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v_x_1747_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1757_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
}
else
{
lean_object* v___x_1758_; 
lean_dec_ref_known(v_x_1747_, 1);
v___x_1758_ = lean_apply_2(v_k_1745_, v_ref_1746_, lean_box(0));
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2___boxed(lean_object* v_k_1759_, lean_object* v_ref_1760_, lean_object* v_x_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2(v_k_1759_, v_ref_1760_, v_x_1761_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3(lean_object* v_mutex_1764_, lean_object* v___f_1765_){
_start:
{
lean_object* v___x_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = 0;
v___x_1769_ = lean_io_basemutex_lock(v_mutex_1764_);
v___x_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
v___x_1772_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1767_, v___x_1768_, v___x_1771_, v___f_1765_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3___boxed(lean_object* v_mutex_1773_, lean_object* v___f_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3(v_mutex_1773_, v___f_1774_);
lean_dec(v_mutex_1773_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(lean_object* v_mutex_1778_, lean_object* v_k_1779_){
_start:
{
lean_object* v_ref_1781_; lean_object* v_mutex_1782_; lean_object* v___f_1783_; lean_object* v___f_1784_; lean_object* v___f_1785_; lean_object* v___f_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___y_1791_; 
v_ref_1781_ = lean_ctor_get(v_mutex_1778_, 0);
lean_inc(v_ref_1781_);
v_mutex_1782_ = lean_ctor_get(v_mutex_1778_, 1);
lean_inc_n(v_mutex_1782_, 2);
lean_dec_ref(v_mutex_1778_);
v___f_1783_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___closed__0));
v___f_1784_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1784_, 0, v_mutex_1782_);
v___f_1785_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1785_, 0, v_k_1779_);
lean_closure_set(v___f_1785_, 1, v_ref_1781_);
v___f_1786_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1786_, 0, v_mutex_1782_);
lean_closure_set(v___f_1786_, 1, v___f_1785_);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = 0;
v___x_1789_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1786_, v___f_1784_, v___x_1787_, v___x_1788_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1793_; 
v_a_1793_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1789_, 1);
if (lean_obj_tag(v_a_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
v_a_1794_ = lean_ctor_get(v_a_1793_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_a_1793_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v_a_1793_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v_a_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
v___y_1791_ = v___x_1799_;
goto v___jp_1790_;
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1810_; 
v_a_1802_ = lean_ctor_get(v_a_1793_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_a_1793_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1804_ = v_a_1793_;
v_isShared_1805_ = v_isSharedCheck_1810_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v_a_1793_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1810_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_fst_1806_; lean_object* v___x_1808_; 
v_fst_1806_ = lean_ctor_get(v_a_1802_, 0);
lean_inc(v_fst_1806_);
lean_dec(v_a_1802_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v_fst_1806_);
v___x_1808_ = v___x_1804_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_fst_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
v___y_1791_ = v___x_1808_;
goto v___jp_1790_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1819_; 
v_a_1811_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1813_ = v___x_1789_;
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1789_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_task_map(v___f_1783_, v_a_1811_, v___x_1787_, v___x_1788_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
v___jp_1790_:
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1792_, 0, v___y_1791_);
return v___x_1792_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___boxed(lean_object* v_mutex_1820_, lean_object* v_k_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(v_mutex_1820_, v_k_1821_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1(lean_object* v_00_u03b1_1824_, lean_object* v_00_u03b2_1825_, lean_object* v_mutex_1826_, lean_object* v_k_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(v_mutex_1826_, v_k_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___boxed(lean_object* v_00_u03b1_1830_, lean_object* v_00_u03b2_1831_, lean_object* v_mutex_1832_, lean_object* v_k_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1(v_00_u03b1_1830_, v_00_u03b2_1831_, v_mutex_1832_, v_k_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0(lean_object* v_x_1836_){
_start:
{
if (lean_obj_tag(v_x_1836_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1846_; 
v_a_1838_ = lean_ctor_get(v_x_1836_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_x_1836_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1840_ = v_x_1836_;
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v_x_1836_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1856_; 
v_a_1847_ = lean_ctor_get(v_x_1836_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_x_1836_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1849_ = v_x_1836_;
v_isShared_1850_ = v_isSharedCheck_1856_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v_x_1836_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1856_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_knownSize_1851_; lean_object* v___x_1853_; 
v_knownSize_1851_ = lean_ctor_get(v_a_1847_, 3);
lean_inc(v_knownSize_1851_);
lean_dec(v_a_1847_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v_knownSize_1851_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_knownSize_1851_);
v___x_1853_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
return v___x_1854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0___boxed(lean_object* v_x_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0(v_x_1857_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1(lean_object* v_x_1860_){
_start:
{
if (lean_obj_tag(v_x_1860_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1870_; 
v_a_1862_ = lean_ctor_get(v_x_1860_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_x_1860_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1864_ = v_x_1860_;
v_isShared_1865_ = v_isSharedCheck_1870_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v_x_1860_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1870_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1862_);
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
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1881_; 
v_a_1871_ = lean_ctor_get(v_x_1860_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_x_1860_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1873_ = v_x_1860_;
v_isShared_1874_ = v_isSharedCheck_1881_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v_x_1860_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1881_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
uint8_t v_closed_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v_closed_1875_ = lean_ctor_get_uint8(v_a_1871_, sizeof(void*)*6);
lean_dec(v_a_1871_);
v___x_1876_ = lean_box(v_closed_1875_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1876_);
v___x_1878_ = v___x_1873_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
return v___x_1879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___boxed(lean_object* v_x_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1(v_x_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2(lean_object* v_reason_1889_, lean_object* v_requestStream_1890_, lean_object* v_x_1891_){
_start:
{
if (lean_obj_tag(v_x_1891_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1901_; 
lean_dec_ref(v_requestStream_1890_);
lean_dec_ref(v_reason_1889_);
v_a_1893_ = lean_ctor_get(v_x_1891_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_x_1891_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1895_ = v_x_1891_;
v_isShared_1896_ = v_isSharedCheck_1901_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v_x_1891_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1901_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
return v___x_1899_;
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; 
v_a_1902_ = lean_ctor_get(v_x_1891_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v_x_1891_, 1);
v___x_1903_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___closed__1));
v___x_1904_ = l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0(v_a_1902_, v___x_1903_);
lean_dec(v_a_1902_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_reason_1889_);
v___x_1906_ = l_Std_Http_Body_Stream_closeWithError(v_requestStream_1890_, v___x_1905_);
return v___x_1906_;
}
else
{
lean_object* v___x_1907_; 
lean_dec_ref(v_reason_1889_);
v___x_1907_ = l_Std_Http_Body_Stream_close(v_requestStream_1890_);
return v___x_1907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___boxed(lean_object* v_reason_1908_, lean_object* v_requestStream_1909_, lean_object* v_x_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2(v_reason_1908_, v_requestStream_1909_, v_x_1910_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3(lean_object* v___x_1913_, uint8_t v_a_1914_, lean_object* v___f_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1918_ = lean_st_ref_get(v___y_1916_);
v___x_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
v___x_1921_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1913_, v_a_1914_, v___x_1920_, v___f_1915_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3___boxed(lean_object* v___x_1922_, lean_object* v_a_1923_, lean_object* v___f_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
uint8_t v_a_2111__boxed_1927_; lean_object* v_res_1928_; 
v_a_2111__boxed_1927_ = lean_unbox(v_a_1923_);
v_res_1928_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3(v___x_1922_, v_a_2111__boxed_1927_, v___f_1924_, v___y_1925_);
lean_dec(v___y_1925_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4(uint8_t v_requestFinalOffered_1929_, lean_object* v___f_1930_, lean_object* v_requestStream_1931_, lean_object* v___f_1932_, lean_object* v_x_1933_){
_start:
{
if (lean_obj_tag(v_x_1933_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v___f_1932_);
lean_dec_ref(v_requestStream_1931_);
lean_dec_ref(v___f_1930_);
v_a_1937_ = lean_ctor_get(v_x_1933_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_x_1933_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1939_ = v_x_1933_;
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v_x_1933_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1945_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
}
}
else
{
if (v_requestFinalOffered_1929_ == 0)
{
lean_object* v_a_1946_; uint8_t v___x_1947_; 
v_a_1946_ = lean_ctor_get(v_x_1933_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v_x_1933_, 1);
v___x_1947_ = lean_unbox(v_a_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___f_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; lean_object* v___x_1952_; 
v___x_1948_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_1946_);
v___f_1949_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_1949_, 0, v___x_1948_);
lean_closure_set(v___f_1949_, 1, v_a_1946_);
lean_closure_set(v___f_1949_, 2, v___f_1930_);
v___x_1950_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(v_requestStream_1931_, v___f_1949_);
v___x_1951_ = lean_unbox(v_a_1946_);
lean_dec(v_a_1946_);
v___x_1952_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1948_, v___x_1951_, v___x_1950_, v___f_1932_);
return v___x_1952_;
}
else
{
lean_dec(v_a_1946_);
lean_dec_ref(v___f_1932_);
lean_dec_ref(v_requestStream_1931_);
lean_dec_ref(v___f_1930_);
goto v___jp_1935_;
}
}
else
{
lean_dec_ref_known(v_x_1933_, 1);
lean_dec_ref(v___f_1932_);
lean_dec_ref(v_requestStream_1931_);
lean_dec_ref(v___f_1930_);
goto v___jp_1935_;
}
}
v___jp_1935_:
{
lean_object* v___x_1936_; 
v___x_1936_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_1936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4___boxed(lean_object* v_requestFinalOffered_1953_, lean_object* v___f_1954_, lean_object* v_requestStream_1955_, lean_object* v___f_1956_, lean_object* v_x_1957_, lean_object* v___y_1958_){
_start:
{
uint8_t v_requestFinalOffered_boxed_1959_; lean_object* v_res_1960_; 
v_requestFinalOffered_boxed_1959_ = lean_unbox(v_requestFinalOffered_1953_);
v_res_1960_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4(v_requestFinalOffered_boxed_1959_, v___f_1954_, v_requestStream_1955_, v___f_1956_, v_x_1957_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5(lean_object* v___x_1961_, uint8_t v___x_1962_, lean_object* v___f_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1966_ = lean_st_ref_get(v___y_1964_);
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
v___x_1969_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1961_, v___x_1962_, v___x_1968_, v___f_1963_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5___boxed(lean_object* v___x_1970_, lean_object* v___x_1971_, lean_object* v___f_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
uint8_t v___x_2188__boxed_1975_; lean_object* v_res_1976_; 
v___x_2188__boxed_1975_ = lean_unbox(v___x_1971_);
v_res_1976_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5(v___x_1970_, v___x_2188__boxed_1975_, v___f_1972_, v___y_1973_);
lean_dec(v___y_1973_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(lean_object* v_state_1984_, lean_object* v_reason_1985_){
_start:
{
lean_object* v_requestStream_1987_; uint8_t v_requestFinalOffered_1988_; lean_object* v___f_1989_; lean_object* v___f_1990_; lean_object* v___x_1991_; lean_object* v___f_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; lean_object* v___f_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_requestStream_1987_ = lean_ctor_get(v_state_1984_, 1);
lean_inc_ref_n(v_requestStream_1987_, 3);
v_requestFinalOffered_1988_ = lean_ctor_get_uint8(v_state_1984_, sizeof(void*)*11 + 2);
lean_dec_ref(v_state_1984_);
v___f_1989_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__0));
v___f_1990_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1990_, 0, v_reason_1985_);
lean_closure_set(v___f_1990_, 1, v_requestStream_1987_);
v___x_1991_ = lean_box(v_requestFinalOffered_1988_);
v___f_1992_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_1992_, 0, v___x_1991_);
lean_closure_set(v___f_1992_, 1, v___f_1989_);
lean_closure_set(v___f_1992_, 2, v_requestStream_1987_);
lean_closure_set(v___f_1992_, 3, v___f_1990_);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = 0;
v___f_1995_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__2));
v___x_1996_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(v_requestStream_1987_, v___f_1995_);
v___x_1997_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1993_, v___x_1994_, v___x_1996_, v___f_1992_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___boxed(lean_object* v_state_1998_, lean_object* v_reason_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v_state_1998_, v_reason_1999_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream(lean_object* v_00_u03b2_2002_, lean_object* v_state_2003_, lean_object* v_reason_2004_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v_state_2003_, v_reason_2004_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___boxed(lean_object* v_00_u03b2_2007_, lean_object* v_state_2008_, lean_object* v_reason_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream(v_00_u03b2_2007_, v_state_2008_, v_reason_2009_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v___x_2012_, lean_object* v_x_2013_){
_start:
{
if (lean_obj_tag(v_x_2013_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v___x_2012_);
v_a_2015_ = lean_ctor_get(v_x_2013_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_x_2013_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2017_ = v_x_2013_;
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v_x_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
}
else
{
lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2032_; 
v_isSharedCheck_2032_ = !lean_is_exclusive(v_x_2013_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; 
v_unused_2033_ = lean_ctor_get(v_x_2013_, 0);
lean_dec(v_unused_2033_);
v___x_2025_ = v_x_2013_;
v_isShared_2026_ = v_isSharedCheck_2032_;
goto v_resetjp_2024_;
}
else
{
lean_dec(v_x_2013_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2032_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2012_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2027_);
v___x_2029_ = v___x_2025_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v___x_2034_, lean_object* v_x_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v___x_2034_, v_x_2035_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v___x_2041_; lean_object* v_pendingProducer_2042_; lean_object* v_pendingConsumer_2043_; lean_object* v_interestWaiter_2044_; uint8_t v_closed_2045_; lean_object* v_pendingIncomplete_2046_; lean_object* v_closeError_2047_; uint8_t v_closeAfterProducer_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2057_; 
v___x_2041_ = lean_st_ref_take(v___y_2039_);
v_pendingProducer_2042_ = lean_ctor_get(v___x_2041_, 0);
v_pendingConsumer_2043_ = lean_ctor_get(v___x_2041_, 1);
v_interestWaiter_2044_ = lean_ctor_get(v___x_2041_, 2);
v_closed_2045_ = lean_ctor_get_uint8(v___x_2041_, sizeof(void*)*6);
v_pendingIncomplete_2046_ = lean_ctor_get(v___x_2041_, 4);
v_closeError_2047_ = lean_ctor_get(v___x_2041_, 5);
v_closeAfterProducer_2048_ = lean_ctor_get_uint8(v___x_2041_, sizeof(void*)*6 + 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v___x_2041_, 3);
lean_dec(v_unused_2058_);
v___x_2050_ = v___x_2041_;
v_isShared_2051_ = v_isSharedCheck_2057_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_closeError_2047_);
lean_inc(v_pendingIncomplete_2046_);
lean_inc(v_interestWaiter_2044_);
lean_inc(v_pendingConsumer_2043_);
lean_inc(v_pendingProducer_2042_);
lean_dec(v___x_2041_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2057_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 3, v___x_2038_);
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_pendingProducer_2042_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_pendingConsumer_2043_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_interestWaiter_2044_);
lean_ctor_set(v_reuseFailAlloc_2056_, 3, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2056_, 4, v_pendingIncomplete_2046_);
lean_ctor_set(v_reuseFailAlloc_2056_, 5, v_closeError_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*6, v_closed_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*6 + 1, v_closeAfterProducer_2048_);
v___x_2053_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_st_ref_put(v___y_2039_, v___x_2053_);
v___x_2055_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_2055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_2059_, v___y_2060_);
lean_dec(v___y_2060_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v___y_2063_, lean_object* v_x_2064_){
_start:
{
if (lean_obj_tag(v_x_2064_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2074_; 
lean_dec_ref(v___y_2063_);
v_a_2066_ = lean_ctor_get(v_x_2064_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_x_2064_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2068_ = v_x_2064_;
v_isShared_2069_ = v_isSharedCheck_2074_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v_x_2064_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2074_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
return v___x_2072_;
}
}
}
else
{
lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2107_; 
v_isSharedCheck_2107_ = !lean_is_exclusive(v_x_2064_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v_x_2064_, 0);
lean_dec(v_unused_2108_);
v___x_2076_ = v_x_2064_;
v_isShared_2077_ = v_isSharedCheck_2107_;
goto v_resetjp_2075_;
}
else
{
lean_dec(v_x_2064_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2107_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_machine_2078_; lean_object* v_requestStream_2079_; lean_object* v_keepAliveTimeout_2080_; lean_object* v_currentTimeout_2081_; lean_object* v_headerTimeout_2082_; lean_object* v_response_2083_; lean_object* v_respStream_2084_; lean_object* v_expectData_2085_; uint8_t v_handlerDispatched_2086_; uint8_t v_requestFinalOffered_2087_; lean_object* v_handlerTask_2088_; lean_object* v_dateSecond_2089_; uint8_t v_peerClosed_2090_; uint8_t v_requestEnded_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2105_; 
v_machine_2078_ = lean_ctor_get(v___y_2063_, 0);
v_requestStream_2079_ = lean_ctor_get(v___y_2063_, 1);
v_keepAliveTimeout_2080_ = lean_ctor_get(v___y_2063_, 2);
v_currentTimeout_2081_ = lean_ctor_get(v___y_2063_, 3);
v_headerTimeout_2082_ = lean_ctor_get(v___y_2063_, 4);
v_response_2083_ = lean_ctor_get(v___y_2063_, 5);
v_respStream_2084_ = lean_ctor_get(v___y_2063_, 6);
v_expectData_2085_ = lean_ctor_get(v___y_2063_, 7);
v_handlerDispatched_2086_ = lean_ctor_get_uint8(v___y_2063_, sizeof(void*)*11 + 1);
v_requestFinalOffered_2087_ = lean_ctor_get_uint8(v___y_2063_, sizeof(void*)*11 + 2);
v_handlerTask_2088_ = lean_ctor_get(v___y_2063_, 9);
v_dateSecond_2089_ = lean_ctor_get(v___y_2063_, 10);
v_peerClosed_2090_ = lean_ctor_get_uint8(v___y_2063_, sizeof(void*)*11 + 3);
v_requestEnded_2091_ = lean_ctor_get_uint8(v___y_2063_, sizeof(void*)*11 + 4);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___y_2063_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; 
v_unused_2106_ = lean_ctor_get(v___y_2063_, 8);
lean_dec(v_unused_2106_);
v___x_2093_ = v___y_2063_;
v_isShared_2094_ = v_isSharedCheck_2105_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_dateSecond_2089_);
lean_inc(v_handlerTask_2088_);
lean_inc(v_expectData_2085_);
lean_inc(v_respStream_2084_);
lean_inc(v_response_2083_);
lean_inc(v_headerTimeout_2082_);
lean_inc(v_currentTimeout_2081_);
lean_inc(v_keepAliveTimeout_2080_);
lean_inc(v_requestStream_2079_);
lean_inc(v_machine_2078_);
lean_dec(v___y_2063_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2105_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2095_ = 0;
v___x_2096_ = lean_box(0);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 8, v___x_2096_);
v___x_2098_ = v___x_2093_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_machine_2078_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v_requestStream_2079_);
lean_ctor_set(v_reuseFailAlloc_2104_, 2, v_keepAliveTimeout_2080_);
lean_ctor_set(v_reuseFailAlloc_2104_, 3, v_currentTimeout_2081_);
lean_ctor_set(v_reuseFailAlloc_2104_, 4, v_headerTimeout_2082_);
lean_ctor_set(v_reuseFailAlloc_2104_, 5, v_response_2083_);
lean_ctor_set(v_reuseFailAlloc_2104_, 6, v_respStream_2084_);
lean_ctor_set(v_reuseFailAlloc_2104_, 7, v_expectData_2085_);
lean_ctor_set(v_reuseFailAlloc_2104_, 8, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2104_, 9, v_handlerTask_2088_);
lean_ctor_set(v_reuseFailAlloc_2104_, 10, v_dateSecond_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*11 + 1, v_handlerDispatched_2086_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*11 + 2, v_requestFinalOffered_2087_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*11 + 3, v_peerClosed_2090_);
lean_ctor_set_uint8(v_reuseFailAlloc_2104_, sizeof(void*)*11 + 4, v_requestEnded_2091_);
v___x_2098_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
lean_ctor_set_uint8(v___x_2098_, sizeof(void*)*11, v___x_2095_);
v___x_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2099_);
v___x_2101_ = v___x_2076_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; 
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v___y_2109_, lean_object* v_x_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v___y_2109_, v_x_2110_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___f_2116_, lean_object* v_x_2117_){
_start:
{
if (lean_obj_tag(v_x_2117_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v___f_2116_);
lean_dec_ref(v___y_2115_);
v_a_2119_ = lean_ctor_get(v_x_2117_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_x_2117_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2121_ = v_x_2117_;
v_isShared_2122_ = v_isSharedCheck_2127_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v_x_2117_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2127_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
}
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec_ref_known(v_x_2117_, 1);
v___x_2128_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0));
v___x_2129_ = lean_string_append(v___x_2128_, v___y_2114_);
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = 0;
v___x_2132_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v___y_2115_, v___x_2129_);
v___x_2133_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2130_, v___x_2131_, v___x_2132_, v___f_2116_);
return v___x_2133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___f_2136_, lean_object* v_x_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___y_2134_, v___y_2135_, v___f_2136_, v_x_2137_);
lean_dec_ref(v___y_2134_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___y_2140_, lean_object* v_x_2141_){
_start:
{
if (lean_obj_tag(v_x_2141_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v___y_2140_);
v_a_2143_ = lean_ctor_get(v_x_2141_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_x_2141_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2145_ = v_x_2141_;
v_isShared_2146_ = v_isSharedCheck_2151_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v_x_2141_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2151_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
return v___x_2149_;
}
}
}
else
{
lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2183_; 
v_isSharedCheck_2183_ = !lean_is_exclusive(v_x_2141_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; 
v_unused_2184_ = lean_ctor_get(v_x_2141_, 0);
lean_dec(v_unused_2184_);
v___x_2153_ = v_x_2141_;
v_isShared_2154_ = v_isSharedCheck_2183_;
goto v_resetjp_2152_;
}
else
{
lean_dec(v_x_2141_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2183_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v_machine_2155_; lean_object* v_requestStream_2156_; lean_object* v_keepAliveTimeout_2157_; lean_object* v_currentTimeout_2158_; lean_object* v_headerTimeout_2159_; lean_object* v_response_2160_; lean_object* v_respStream_2161_; uint8_t v_requiresData_2162_; lean_object* v_expectData_2163_; uint8_t v_handlerDispatched_2164_; lean_object* v_pendingHead_2165_; uint8_t v_requestFinalOffered_2166_; lean_object* v_handlerTask_2167_; lean_object* v_dateSecond_2168_; uint8_t v_peerClosed_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2182_; 
v_machine_2155_ = lean_ctor_get(v___y_2140_, 0);
v_requestStream_2156_ = lean_ctor_get(v___y_2140_, 1);
v_keepAliveTimeout_2157_ = lean_ctor_get(v___y_2140_, 2);
v_currentTimeout_2158_ = lean_ctor_get(v___y_2140_, 3);
v_headerTimeout_2159_ = lean_ctor_get(v___y_2140_, 4);
v_response_2160_ = lean_ctor_get(v___y_2140_, 5);
v_respStream_2161_ = lean_ctor_get(v___y_2140_, 6);
v_requiresData_2162_ = lean_ctor_get_uint8(v___y_2140_, sizeof(void*)*11);
v_expectData_2163_ = lean_ctor_get(v___y_2140_, 7);
v_handlerDispatched_2164_ = lean_ctor_get_uint8(v___y_2140_, sizeof(void*)*11 + 1);
v_pendingHead_2165_ = lean_ctor_get(v___y_2140_, 8);
v_requestFinalOffered_2166_ = lean_ctor_get_uint8(v___y_2140_, sizeof(void*)*11 + 2);
v_handlerTask_2167_ = lean_ctor_get(v___y_2140_, 9);
v_dateSecond_2168_ = lean_ctor_get(v___y_2140_, 10);
v_peerClosed_2169_ = lean_ctor_get_uint8(v___y_2140_, sizeof(void*)*11 + 3);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___y_2140_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2171_ = v___y_2140_;
v_isShared_2172_ = v_isSharedCheck_2182_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_dateSecond_2168_);
lean_inc(v_handlerTask_2167_);
lean_inc(v_pendingHead_2165_);
lean_inc(v_expectData_2163_);
lean_inc(v_respStream_2161_);
lean_inc(v_response_2160_);
lean_inc(v_headerTimeout_2159_);
lean_inc(v_currentTimeout_2158_);
lean_inc(v_keepAliveTimeout_2157_);
lean_inc(v_requestStream_2156_);
lean_inc(v_machine_2155_);
lean_dec(v___y_2140_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2182_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
uint8_t v___x_2173_; lean_object* v___x_2175_; 
v___x_2173_ = 1;
if (v_isShared_2172_ == 0)
{
v___x_2175_ = v___x_2171_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_machine_2155_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_requestStream_2156_);
lean_ctor_set(v_reuseFailAlloc_2181_, 2, v_keepAliveTimeout_2157_);
lean_ctor_set(v_reuseFailAlloc_2181_, 3, v_currentTimeout_2158_);
lean_ctor_set(v_reuseFailAlloc_2181_, 4, v_headerTimeout_2159_);
lean_ctor_set(v_reuseFailAlloc_2181_, 5, v_response_2160_);
lean_ctor_set(v_reuseFailAlloc_2181_, 6, v_respStream_2161_);
lean_ctor_set(v_reuseFailAlloc_2181_, 7, v_expectData_2163_);
lean_ctor_set(v_reuseFailAlloc_2181_, 8, v_pendingHead_2165_);
lean_ctor_set(v_reuseFailAlloc_2181_, 9, v_handlerTask_2167_);
lean_ctor_set(v_reuseFailAlloc_2181_, 10, v_dateSecond_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, sizeof(void*)*11, v_requiresData_2162_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, sizeof(void*)*11 + 1, v_handlerDispatched_2164_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, sizeof(void*)*11 + 2, v_requestFinalOffered_2166_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, sizeof(void*)*11 + 3, v_peerClosed_2169_);
v___x_2175_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
lean_ctor_set_uint8(v___x_2175_, sizeof(void*)*11 + 4, v___x_2173_);
v___x_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2176_);
v___x_2178_ = v___x_2153_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
return v___x_2179_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___y_2185_, lean_object* v_x_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___y_2185_, v_x_2186_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v___y_2189_, lean_object* v_config_2190_, lean_object* v_a_2191_, lean_object* v_x_2192_){
_start:
{
if (lean_obj_tag(v_x_2192_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2202_; 
lean_dec_ref(v_a_2191_);
lean_dec_ref(v___y_2189_);
v_a_2194_ = lean_ctor_get(v_x_2192_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_x_2192_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2196_ = v_x_2192_;
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v_x_2192_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; 
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
return v___x_2200_;
}
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2237_; 
v_a_2203_ = lean_ctor_get(v_x_2192_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_x_2192_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2205_ = v_x_2192_;
v_isShared_2206_ = v_isSharedCheck_2237_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v_x_2192_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2237_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v_machine_2207_; uint8_t v_requiresData_2208_; lean_object* v_expectData_2209_; lean_object* v_pendingHead_2210_; lean_object* v_handlerTask_2211_; lean_object* v_dateSecond_2212_; uint8_t v_peerClosed_2213_; uint8_t v_requestEnded_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2230_; 
v_machine_2207_ = lean_ctor_get(v___y_2189_, 0);
v_requiresData_2208_ = lean_ctor_get_uint8(v___y_2189_, sizeof(void*)*11);
v_expectData_2209_ = lean_ctor_get(v___y_2189_, 7);
v_pendingHead_2210_ = lean_ctor_get(v___y_2189_, 8);
v_handlerTask_2211_ = lean_ctor_get(v___y_2189_, 9);
v_dateSecond_2212_ = lean_ctor_get(v___y_2189_, 10);
v_peerClosed_2213_ = lean_ctor_get_uint8(v___y_2189_, sizeof(void*)*11 + 3);
v_requestEnded_2214_ = lean_ctor_get_uint8(v___y_2189_, sizeof(void*)*11 + 4);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___y_2189_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; lean_object* v_unused_2232_; lean_object* v_unused_2233_; lean_object* v_unused_2234_; lean_object* v_unused_2235_; lean_object* v_unused_2236_; 
v_unused_2231_ = lean_ctor_get(v___y_2189_, 6);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v___y_2189_, 5);
lean_dec(v_unused_2232_);
v_unused_2233_ = lean_ctor_get(v___y_2189_, 4);
lean_dec(v_unused_2233_);
v_unused_2234_ = lean_ctor_get(v___y_2189_, 3);
lean_dec(v_unused_2234_);
v_unused_2235_ = lean_ctor_get(v___y_2189_, 2);
lean_dec(v_unused_2235_);
v_unused_2236_ = lean_ctor_get(v___y_2189_, 1);
lean_dec(v_unused_2236_);
v___x_2216_ = v___y_2189_;
v_isShared_2217_ = v_isSharedCheck_2230_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_dateSecond_2212_);
lean_inc(v_handlerTask_2211_);
lean_inc(v_pendingHead_2210_);
lean_inc(v_expectData_2209_);
lean_inc(v_machine_2207_);
lean_dec(v___y_2189_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2230_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v_keepAliveTimeout_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; lean_object* v___x_2223_; 
v_keepAliveTimeout_2218_ = lean_ctor_get(v_config_2190_, 5);
lean_inc_n(v_keepAliveTimeout_2218_, 2);
v___x_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_keepAliveTimeout_2218_);
v___x_2220_ = lean_box(0);
v___x_2221_ = 0;
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 6, v___x_2220_);
lean_ctor_set(v___x_2216_, 5, v_a_2203_);
lean_ctor_set(v___x_2216_, 4, v___x_2220_);
lean_ctor_set(v___x_2216_, 3, v_keepAliveTimeout_2218_);
lean_ctor_set(v___x_2216_, 2, v___x_2219_);
lean_ctor_set(v___x_2216_, 1, v_a_2191_);
v___x_2223_ = v___x_2216_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_machine_2207_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_a_2191_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_keepAliveTimeout_2218_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2229_, 5, v_a_2203_);
lean_ctor_set(v_reuseFailAlloc_2229_, 6, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2229_, 7, v_expectData_2209_);
lean_ctor_set(v_reuseFailAlloc_2229_, 8, v_pendingHead_2210_);
lean_ctor_set(v_reuseFailAlloc_2229_, 9, v_handlerTask_2211_);
lean_ctor_set(v_reuseFailAlloc_2229_, 10, v_dateSecond_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2229_, sizeof(void*)*11, v_requiresData_2208_);
lean_ctor_set_uint8(v_reuseFailAlloc_2229_, sizeof(void*)*11 + 3, v_peerClosed_2213_);
lean_ctor_set_uint8(v_reuseFailAlloc_2229_, sizeof(void*)*11 + 4, v_requestEnded_2214_);
v___x_2223_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
lean_ctor_set_uint8(v___x_2223_, sizeof(void*)*11 + 1, v___x_2221_);
lean_ctor_set_uint8(v___x_2223_, sizeof(void*)*11 + 2, v___x_2221_);
v___x_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2224_);
v___x_2226_ = v___x_2205_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
return v___x_2227_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v___y_2238_, lean_object* v_config_2239_, lean_object* v_a_2240_, lean_object* v_x_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v___y_2238_, v_config_2239_, v_a_2240_, v_x_2241_);
lean_dec_ref(v_config_2239_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v___y_2244_, lean_object* v_config_2245_, lean_object* v_x_2246_){
_start:
{
if (lean_obj_tag(v_x_2246_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2256_; 
lean_dec_ref(v_config_2245_);
lean_dec_ref(v___y_2244_);
v_a_2248_ = lean_ctor_get(v_x_2246_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_x_2246_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2250_ = v_x_2246_;
v_isShared_2251_ = v_isSharedCheck_2256_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v_x_2246_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2256_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
return v___x_2254_;
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2271_; 
v_a_2257_ = lean_ctor_get(v_x_2246_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_x_2246_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2259_ = v_x_2246_;
v_isShared_2260_ = v_isSharedCheck_2271_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v_x_2246_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2271_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___f_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___f_2261_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_2261_, 0, v___y_2244_);
lean_closure_set(v___f_2261_, 1, v_config_2245_);
lean_closure_set(v___f_2261_, 2, v_a_2257_);
v___x_2262_ = lean_box(0);
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = 0;
v___x_2265_ = l_Std_CloseableChannel_new___redArg(v___x_2262_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2265_);
v___x_2267_ = v___x_2259_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
v___x_2269_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2263_, v___x_2264_, v___x_2268_, v___f_2261_);
return v___x_2269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v___y_2272_, lean_object* v_config_2273_, lean_object* v_x_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v___y_2272_, v_config_2273_, v_x_2274_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v___f_2277_, lean_object* v_____r_2278_){
_start:
{
lean_object* v___x_2280_; uint8_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2280_ = lean_unsigned_to_nat(0u);
v___x_2281_ = 0;
v___x_2282_ = l_Std_Http_Body_mkStream();
v___x_2283_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2280_, v___x_2281_, v___x_2282_, v___f_2277_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v___f_2284_, lean_object* v_____r_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v___f_2284_, v_____r_2285_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v___f_2288_, lean_object* v_x_2289_){
_start:
{
if (lean_obj_tag(v_x_2289_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v___f_2288_);
v_a_2291_ = lean_ctor_get(v_x_2289_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v_x_2289_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2293_ = v_x_2289_;
v_isShared_2294_ = v_isSharedCheck_2299_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v_x_2289_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2299_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2301_; 
v_a_2300_ = lean_ctor_get(v_x_2289_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v_x_2289_, 1);
v___x_2301_ = lean_apply_2(v___f_2288_, v_a_2300_, lean_box(0));
return v___x_2301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v___f_2302_, lean_object* v_x_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v___f_2302_, v_x_2303_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v_close_2306_, lean_object* v_val_2307_, lean_object* v___f_2308_, lean_object* v___f_2309_, lean_object* v_x_2310_){
_start:
{
if (lean_obj_tag(v_x_2310_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v___f_2309_);
lean_dec_ref(v___f_2308_);
lean_dec(v_val_2307_);
lean_dec_ref(v_close_2306_);
v_a_2312_ = lean_ctor_get(v_x_2310_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_x_2310_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2314_ = v_x_2310_;
v_isShared_2315_ = v_isSharedCheck_2320_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v_x_2310_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2320_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
return v___x_2318_;
}
}
}
else
{
lean_object* v_a_2321_; uint8_t v___x_2322_; 
v_a_2321_ = lean_ctor_get(v_x_2310_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v_x_2310_, 1);
v___x_2322_ = lean_unbox(v_a_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; 
lean_dec_ref(v___f_2309_);
v___x_2323_ = lean_unsigned_to_nat(0u);
v___x_2324_ = lean_apply_2(v_close_2306_, v_val_2307_, lean_box(0));
v___x_2325_ = lean_unbox(v_a_2321_);
lean_dec(v_a_2321_);
v___x_2326_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2323_, v___x_2325_, v___x_2324_, v___f_2308_);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_dec(v_a_2321_);
lean_dec_ref(v___f_2308_);
lean_dec(v_val_2307_);
lean_dec_ref(v_close_2306_);
v___x_2327_ = lean_box(0);
v___x_2328_ = lean_apply_2(v___f_2309_, v___x_2327_, lean_box(0));
return v___x_2328_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v_close_2329_, lean_object* v_val_2330_, lean_object* v___f_2331_, lean_object* v___f_2332_, lean_object* v_x_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v_close_2329_, v_val_2330_, v___f_2331_, v___f_2332_, v_x_2333_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v___y_2336_, lean_object* v_inst_2337_, lean_object* v___f_2338_, lean_object* v___f_2339_, lean_object* v_x_2340_){
_start:
{
if (lean_obj_tag(v_x_2340_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v___f_2339_);
lean_dec_ref(v___f_2338_);
lean_dec_ref(v_inst_2337_);
lean_dec_ref(v___y_2336_);
v_a_2342_ = lean_ctor_get(v_x_2340_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_x_2340_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2344_ = v_x_2340_;
v_isShared_2345_ = v_isSharedCheck_2350_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v_x_2340_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2350_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2348_; 
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
return v___x_2348_;
}
}
}
else
{
lean_object* v_respStream_2351_; 
lean_dec_ref_known(v_x_2340_, 1);
v_respStream_2351_ = lean_ctor_get(v___y_2336_, 6);
lean_inc(v_respStream_2351_);
lean_dec_ref(v___y_2336_);
if (lean_obj_tag(v_respStream_2351_) == 1)
{
lean_object* v_val_2352_; lean_object* v_close_2353_; lean_object* v_isClosed_2354_; lean_object* v___f_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_val_2352_ = lean_ctor_get(v_respStream_2351_, 0);
lean_inc_n(v_val_2352_, 2);
lean_dec_ref_known(v_respStream_2351_, 1);
v_close_2353_ = lean_ctor_get(v_inst_2337_, 1);
lean_inc_ref(v_close_2353_);
v_isClosed_2354_ = lean_ctor_get(v_inst_2337_, 2);
lean_inc_ref(v_isClosed_2354_);
lean_dec_ref(v_inst_2337_);
v___f_2355_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 6, 4);
lean_closure_set(v___f_2355_, 0, v_close_2353_);
lean_closure_set(v___f_2355_, 1, v_val_2352_);
lean_closure_set(v___f_2355_, 2, v___f_2338_);
lean_closure_set(v___f_2355_, 3, v___f_2339_);
v___x_2356_ = lean_unsigned_to_nat(0u);
v___x_2357_ = 0;
v___x_2358_ = lean_apply_2(v_isClosed_2354_, v_val_2352_, lean_box(0));
v___x_2359_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2356_, v___x_2357_, v___x_2358_, v___f_2355_);
return v___x_2359_;
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_dec(v_respStream_2351_);
lean_dec_ref(v___f_2338_);
lean_dec_ref(v_inst_2337_);
v___x_2360_ = lean_box(0);
v___x_2361_ = lean_apply_2(v___f_2339_, v___x_2360_, lean_box(0));
return v___x_2361_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v___y_2362_, lean_object* v_inst_2363_, lean_object* v___f_2364_, lean_object* v___f_2365_, lean_object* v_x_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v___y_2362_, v_inst_2363_, v___f_2364_, v___f_2365_, v_x_2366_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v_requestStream_2369_, lean_object* v_keepAliveTimeout_2370_, lean_object* v_currentTimeout_2371_, lean_object* v_headerTimeout_2372_, lean_object* v_response_2373_, lean_object* v_respStream_2374_, uint8_t v_requiresData_2375_, lean_object* v_expectData_2376_, uint8_t v_handlerDispatched_2377_, lean_object* v_pendingHead_2378_, uint8_t v_requestFinalOffered_2379_, lean_object* v_handlerTask_2380_, lean_object* v_dateSecond_2381_, uint8_t v_peerClosed_2382_, uint8_t v_requestEnded_2383_, lean_object* v_x_2384_){
_start:
{
if (lean_obj_tag(v_x_2384_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_dateSecond_2381_);
lean_dec(v_handlerTask_2380_);
lean_dec(v_pendingHead_2378_);
lean_dec(v_expectData_2376_);
lean_dec(v_respStream_2374_);
lean_dec_ref(v_response_2373_);
lean_dec(v_headerTimeout_2372_);
lean_dec(v_currentTimeout_2371_);
lean_dec(v_keepAliveTimeout_2370_);
lean_dec_ref(v_requestStream_2369_);
v_a_2386_ = lean_ctor_get(v_x_2384_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_x_2384_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2388_ = v_x_2384_;
v_isShared_2389_ = v_isSharedCheck_2394_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v_x_2384_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2394_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
return v___x_2392_;
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2416_; 
v_a_2395_ = lean_ctor_get(v_x_2384_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_x_2384_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2397_ = v_x_2384_;
v_isShared_2398_ = v_isSharedCheck_2416_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v_x_2384_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2416_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v_snd_2399_; uint8_t v___x_2400_; 
v_snd_2399_ = lean_ctor_get(v_a_2395_, 1);
v___x_2400_ = lean_unbox(v_snd_2399_);
if (v___x_2400_ == 0)
{
lean_object* v_fst_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v_fst_2401_ = lean_ctor_get(v_a_2395_, 0);
lean_inc(v_fst_2401_);
lean_dec(v_a_2395_);
v___x_2402_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v___x_2402_, 0, v_fst_2401_);
lean_ctor_set(v___x_2402_, 1, v_requestStream_2369_);
lean_ctor_set(v___x_2402_, 2, v_keepAliveTimeout_2370_);
lean_ctor_set(v___x_2402_, 3, v_currentTimeout_2371_);
lean_ctor_set(v___x_2402_, 4, v_headerTimeout_2372_);
lean_ctor_set(v___x_2402_, 5, v_response_2373_);
lean_ctor_set(v___x_2402_, 6, v_respStream_2374_);
lean_ctor_set(v___x_2402_, 7, v_expectData_2376_);
lean_ctor_set(v___x_2402_, 8, v_pendingHead_2378_);
lean_ctor_set(v___x_2402_, 9, v_handlerTask_2380_);
lean_ctor_set(v___x_2402_, 10, v_dateSecond_2381_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*11, v_requiresData_2375_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*11 + 1, v_handlerDispatched_2377_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*11 + 2, v_requestFinalOffered_2379_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*11 + 3, v_peerClosed_2382_);
lean_ctor_set_uint8(v___x_2402_, sizeof(void*)*11 + 4, v_requestEnded_2383_);
v___x_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2403_);
v___x_2405_ = v___x_2397_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
return v___x_2406_;
}
}
else
{
lean_object* v_fst_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
lean_dec(v_pendingHead_2378_);
v_fst_2408_ = lean_ctor_get(v_a_2395_, 0);
lean_inc(v_fst_2408_);
lean_dec(v_a_2395_);
v___x_2409_ = lean_box(0);
v___x_2410_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v___x_2410_, 0, v_fst_2408_);
lean_ctor_set(v___x_2410_, 1, v_requestStream_2369_);
lean_ctor_set(v___x_2410_, 2, v_keepAliveTimeout_2370_);
lean_ctor_set(v___x_2410_, 3, v_currentTimeout_2371_);
lean_ctor_set(v___x_2410_, 4, v_headerTimeout_2372_);
lean_ctor_set(v___x_2410_, 5, v_response_2373_);
lean_ctor_set(v___x_2410_, 6, v_respStream_2374_);
lean_ctor_set(v___x_2410_, 7, v_expectData_2376_);
lean_ctor_set(v___x_2410_, 8, v___x_2409_);
lean_ctor_set(v___x_2410_, 9, v_handlerTask_2380_);
lean_ctor_set(v___x_2410_, 10, v_dateSecond_2381_);
lean_ctor_set_uint8(v___x_2410_, sizeof(void*)*11, v_requiresData_2375_);
lean_ctor_set_uint8(v___x_2410_, sizeof(void*)*11 + 1, v_handlerDispatched_2377_);
lean_ctor_set_uint8(v___x_2410_, sizeof(void*)*11 + 2, v_requestFinalOffered_2379_);
lean_ctor_set_uint8(v___x_2410_, sizeof(void*)*11 + 3, v_peerClosed_2382_);
lean_ctor_set_uint8(v___x_2410_, sizeof(void*)*11 + 4, v_requestEnded_2383_);
v___x_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2411_);
v___x_2413_ = v___x_2397_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2414_; 
v___x_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
return v___x_2414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_requestStream_2417_ = _args[0];
lean_object* v_keepAliveTimeout_2418_ = _args[1];
lean_object* v_currentTimeout_2419_ = _args[2];
lean_object* v_headerTimeout_2420_ = _args[3];
lean_object* v_response_2421_ = _args[4];
lean_object* v_respStream_2422_ = _args[5];
lean_object* v_requiresData_2423_ = _args[6];
lean_object* v_expectData_2424_ = _args[7];
lean_object* v_handlerDispatched_2425_ = _args[8];
lean_object* v_pendingHead_2426_ = _args[9];
lean_object* v_requestFinalOffered_2427_ = _args[10];
lean_object* v_handlerTask_2428_ = _args[11];
lean_object* v_dateSecond_2429_ = _args[12];
lean_object* v_peerClosed_2430_ = _args[13];
lean_object* v_requestEnded_2431_ = _args[14];
lean_object* v_x_2432_ = _args[15];
lean_object* v___y_2433_ = _args[16];
_start:
{
uint8_t v_requiresData_boxed_2434_; uint8_t v_handlerDispatched_boxed_2435_; uint8_t v_requestFinalOffered_boxed_2436_; uint8_t v_peerClosed_boxed_2437_; uint8_t v_requestEnded_boxed_2438_; lean_object* v_res_2439_; 
v_requiresData_boxed_2434_ = lean_unbox(v_requiresData_2423_);
v_handlerDispatched_boxed_2435_ = lean_unbox(v_handlerDispatched_2425_);
v_requestFinalOffered_boxed_2436_ = lean_unbox(v_requestFinalOffered_2427_);
v_peerClosed_boxed_2437_ = lean_unbox(v_peerClosed_2430_);
v_requestEnded_boxed_2438_ = lean_unbox(v_requestEnded_2431_);
v_res_2439_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v_requestStream_2417_, v_keepAliveTimeout_2418_, v_currentTimeout_2419_, v_headerTimeout_2420_, v_response_2421_, v_respStream_2422_, v_requiresData_boxed_2434_, v_expectData_2424_, v_handlerDispatched_boxed_2435_, v_pendingHead_2426_, v_requestFinalOffered_boxed_2436_, v_handlerTask_2428_, v_dateSecond_2429_, v_peerClosed_boxed_2437_, v_requestEnded_boxed_2438_, v_x_2432_);
return v_res_2439_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0(void){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_2440_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1(void){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_2441_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___f_2448_; lean_object* v___f_2449_; 
v___x_2447_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1);
v___f_2448_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__4));
v___f_2449_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2449_, 0, v___f_2448_);
lean_closure_set(v___f_2449_, 1, v___x_2447_);
return v___f_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v_config_2466_, lean_object* v_inst_2467_, lean_object* v_handler_2468_, lean_object* v_inst_2469_, lean_object* v_connectionContext_2470_, lean_object* v_a_2471_, lean_object* v_x_2472_, lean_object* v___y_2473_){
_start:
{
switch(lean_obj_tag(v_a_2471_))
{
case 0:
{
lean_object* v_head_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2522_; 
lean_dec_ref(v_connectionContext_2470_);
lean_dec_ref(v_inst_2469_);
lean_dec(v_handler_2468_);
lean_dec_ref(v_inst_2467_);
v_head_2475_ = lean_ctor_get(v_a_2471_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_a_2471_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2477_ = v_a_2471_;
v_isShared_2478_ = v_isSharedCheck_2522_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_head_2475_);
lean_dec(v_a_2471_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2522_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v_machine_2479_; lean_object* v_requestStream_2480_; lean_object* v_response_2481_; lean_object* v_respStream_2482_; uint8_t v_requiresData_2483_; lean_object* v_expectData_2484_; uint8_t v_handlerDispatched_2485_; uint8_t v_requestFinalOffered_2486_; lean_object* v_handlerTask_2487_; lean_object* v_dateSecond_2488_; uint8_t v_peerClosed_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2517_; 
v_machine_2479_ = lean_ctor_get(v___y_2473_, 0);
v_requestStream_2480_ = lean_ctor_get(v___y_2473_, 1);
v_response_2481_ = lean_ctor_get(v___y_2473_, 5);
v_respStream_2482_ = lean_ctor_get(v___y_2473_, 6);
v_requiresData_2483_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11);
v_expectData_2484_ = lean_ctor_get(v___y_2473_, 7);
v_handlerDispatched_2485_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11 + 1);
v_requestFinalOffered_2486_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11 + 2);
v_handlerTask_2487_ = lean_ctor_get(v___y_2473_, 9);
v_dateSecond_2488_ = lean_ctor_get(v___y_2473_, 10);
v_peerClosed_2489_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11 + 3);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___y_2473_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; lean_object* v_unused_2519_; lean_object* v_unused_2520_; lean_object* v_unused_2521_; 
v_unused_2518_ = lean_ctor_get(v___y_2473_, 8);
lean_dec(v_unused_2518_);
v_unused_2519_ = lean_ctor_get(v___y_2473_, 4);
lean_dec(v_unused_2519_);
v_unused_2520_ = lean_ctor_get(v___y_2473_, 3);
lean_dec(v_unused_2520_);
v_unused_2521_ = lean_ctor_get(v___y_2473_, 2);
lean_dec(v_unused_2521_);
v___x_2491_ = v___y_2473_;
v_isShared_2492_ = v_isSharedCheck_2517_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_dateSecond_2488_);
lean_inc(v_handlerTask_2487_);
lean_inc(v_expectData_2484_);
lean_inc(v_respStream_2482_);
lean_inc(v_response_2481_);
lean_inc(v_requestStream_2480_);
lean_inc(v_machine_2479_);
lean_dec(v___y_2473_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2517_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v_lingeringTimeout_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
v_lingeringTimeout_2493_ = lean_ctor_get(v_config_2466_, 4);
lean_inc(v_lingeringTimeout_2493_);
lean_dec_ref(v_config_2466_);
v___x_2494_ = lean_box(0);
lean_inc(v_head_2475_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set_tag(v___x_2477_, 1);
v___x_2496_ = v___x_2477_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_head_2475_);
v___x_2496_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
uint8_t v___x_2497_; lean_object* v___x_2499_; 
v___x_2497_ = 0;
lean_inc_ref(v_requestStream_2480_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 8, v___x_2496_);
lean_ctor_set(v___x_2491_, 4, v___x_2494_);
lean_ctor_set(v___x_2491_, 3, v_lingeringTimeout_2493_);
lean_ctor_set(v___x_2491_, 2, v___x_2494_);
v___x_2499_ = v___x_2491_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_machine_2479_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_requestStream_2480_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_lingeringTimeout_2493_);
lean_ctor_set(v_reuseFailAlloc_2515_, 4, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2515_, 5, v_response_2481_);
lean_ctor_set(v_reuseFailAlloc_2515_, 6, v_respStream_2482_);
lean_ctor_set(v_reuseFailAlloc_2515_, 7, v_expectData_2484_);
lean_ctor_set(v_reuseFailAlloc_2515_, 8, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2515_, 9, v_handlerTask_2487_);
lean_ctor_set(v_reuseFailAlloc_2515_, 10, v_dateSecond_2488_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, sizeof(void*)*11, v_requiresData_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, sizeof(void*)*11 + 1, v_handlerDispatched_2485_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, sizeof(void*)*11 + 2, v_requestFinalOffered_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2515_, sizeof(void*)*11 + 3, v_peerClosed_2489_);
v___x_2499_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
uint8_t v___x_2500_; uint8_t v___x_2501_; lean_object* v___x_2502_; 
lean_ctor_set_uint8(v___x_2499_, sizeof(void*)*11 + 4, v___x_2497_);
v___x_2500_ = 0;
v___x_2501_ = 1;
v___x_2502_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2500_, v_head_2475_, v___x_2501_);
lean_dec(v_head_2475_);
if (lean_obj_tag(v___x_2502_) == 1)
{
lean_object* v___f_2503_; lean_object* v___f_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___f_2507_; lean_object* v___f_2508_; lean_object* v___x_4145__overap_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___f_2503_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2503_, 0, v___x_2499_);
v___f_2504_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2504_, 0, v___x_2502_);
v___x_2505_ = lean_unsigned_to_nat(0u);
v___x_2506_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0);
v___f_2507_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5);
v___f_2508_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__6));
v___x_4145__overap_2509_ = l_Std_Mutex_atomically___redArg(v___x_2506_, v___f_2507_, v___f_2508_, v_requestStream_2480_, v___f_2504_);
v___x_2510_ = lean_apply_1(v___x_4145__overap_2509_, lean_box(0));
v___x_2511_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2505_, v___x_2497_, v___x_2510_, v___f_2503_);
return v___x_2511_;
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_dec(v___x_2502_);
lean_dec_ref(v_requestStream_2480_);
v___x_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2499_);
v___x_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
return v___x_2514_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2555_; 
lean_dec_ref(v_connectionContext_2470_);
lean_dec_ref(v_inst_2469_);
lean_dec(v_handler_2468_);
lean_dec_ref(v_inst_2467_);
lean_dec_ref(v_config_2466_);
v_size_2523_ = lean_ctor_get(v_a_2471_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_a_2471_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2525_ = v_a_2471_;
v_isShared_2526_ = v_isSharedCheck_2555_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_size_2523_);
lean_dec(v_a_2471_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2555_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v_machine_2527_; lean_object* v_requestStream_2528_; lean_object* v_keepAliveTimeout_2529_; lean_object* v_currentTimeout_2530_; lean_object* v_headerTimeout_2531_; lean_object* v_response_2532_; lean_object* v_respStream_2533_; uint8_t v_handlerDispatched_2534_; lean_object* v_pendingHead_2535_; uint8_t v_requestFinalOffered_2536_; lean_object* v_handlerTask_2537_; lean_object* v_dateSecond_2538_; uint8_t v_peerClosed_2539_; uint8_t v_requestEnded_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2553_; 
v_machine_2527_ = lean_ctor_get(v___y_2473_, 0);
v_requestStream_2528_ = lean_ctor_get(v___y_2473_, 1);
v_keepAliveTimeout_2529_ = lean_ctor_get(v___y_2473_, 2);
v_currentTimeout_2530_ = lean_ctor_get(v___y_2473_, 3);
v_headerTimeout_2531_ = lean_ctor_get(v___y_2473_, 4);
v_response_2532_ = lean_ctor_get(v___y_2473_, 5);
v_respStream_2533_ = lean_ctor_get(v___y_2473_, 6);
v_handlerDispatched_2534_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11 + 1);
v_pendingHead_2535_ = lean_ctor_get(v___y_2473_, 8);
v_requestFinalOffered_2536_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11 + 2);
v_handlerTask_2537_ = lean_ctor_get(v___y_2473_, 9);
v_dateSecond_2538_ = lean_ctor_get(v___y_2473_, 10);
v_peerClosed_2539_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11 + 3);
v_requestEnded_2540_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11 + 4);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___y_2473_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; 
v_unused_2554_ = lean_ctor_get(v___y_2473_, 7);
lean_dec(v_unused_2554_);
v___x_2542_ = v___y_2473_;
v_isShared_2543_ = v_isSharedCheck_2553_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_dateSecond_2538_);
lean_inc(v_handlerTask_2537_);
lean_inc(v_pendingHead_2535_);
lean_inc(v_respStream_2533_);
lean_inc(v_response_2532_);
lean_inc(v_headerTimeout_2531_);
lean_inc(v_currentTimeout_2530_);
lean_inc(v_keepAliveTimeout_2529_);
lean_inc(v_requestStream_2528_);
lean_inc(v_machine_2527_);
lean_dec(v___y_2473_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2553_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
uint8_t v___x_2544_; lean_object* v___x_2546_; 
v___x_2544_ = 1;
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 7, v_size_2523_);
v___x_2546_ = v___x_2542_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_machine_2527_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_requestStream_2528_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_keepAliveTimeout_2529_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_currentTimeout_2530_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v_headerTimeout_2531_);
lean_ctor_set(v_reuseFailAlloc_2552_, 5, v_response_2532_);
lean_ctor_set(v_reuseFailAlloc_2552_, 6, v_respStream_2533_);
lean_ctor_set(v_reuseFailAlloc_2552_, 7, v_size_2523_);
lean_ctor_set(v_reuseFailAlloc_2552_, 8, v_pendingHead_2535_);
lean_ctor_set(v_reuseFailAlloc_2552_, 9, v_handlerTask_2537_);
lean_ctor_set(v_reuseFailAlloc_2552_, 10, v_dateSecond_2538_);
lean_ctor_set_uint8(v_reuseFailAlloc_2552_, sizeof(void*)*11 + 1, v_handlerDispatched_2534_);
lean_ctor_set_uint8(v_reuseFailAlloc_2552_, sizeof(void*)*11 + 2, v_requestFinalOffered_2536_);
lean_ctor_set_uint8(v_reuseFailAlloc_2552_, sizeof(void*)*11 + 3, v_peerClosed_2539_);
lean_ctor_set_uint8(v_reuseFailAlloc_2552_, sizeof(void*)*11 + 4, v_requestEnded_2540_);
v___x_2546_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2548_; 
lean_ctor_set_uint8(v___x_2546_, sizeof(void*)*11, v___x_2544_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2546_);
v___x_2548_ = v___x_2525_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
return v___x_2550_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2556_; lean_object* v___f_2557_; lean_object* v___y_2559_; 
lean_dec_ref(v_connectionContext_2470_);
lean_dec_ref(v_inst_2469_);
lean_dec_ref(v_config_2466_);
v_err_2556_ = lean_ctor_get(v_a_2471_, 0);
lean_inc(v_err_2556_);
lean_dec_ref_known(v_a_2471_, 1);
lean_inc_ref(v___y_2473_);
v___f_2557_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2557_, 0, v___y_2473_);
switch(lean_obj_tag(v_err_2556_))
{
case 0:
{
lean_object* v___x_2566_; 
v___x_2566_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__7));
v___y_2559_ = v___x_2566_;
goto v___jp_2558_;
}
case 1:
{
lean_object* v___x_2567_; 
v___x_2567_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__8));
v___y_2559_ = v___x_2567_;
goto v___jp_2558_;
}
case 2:
{
lean_object* v___x_2568_; 
v___x_2568_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__9));
v___y_2559_ = v___x_2568_;
goto v___jp_2558_;
}
case 3:
{
lean_object* v___x_2569_; 
v___x_2569_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__10));
v___y_2559_ = v___x_2569_;
goto v___jp_2558_;
}
case 4:
{
lean_object* v___x_2570_; 
v___x_2570_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__11));
v___y_2559_ = v___x_2570_;
goto v___jp_2558_;
}
case 5:
{
lean_object* v___x_2571_; 
v___x_2571_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__12));
v___y_2559_ = v___x_2571_;
goto v___jp_2558_;
}
case 6:
{
lean_object* v___x_2572_; 
v___x_2572_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__13));
v___y_2559_ = v___x_2572_;
goto v___jp_2558_;
}
case 7:
{
lean_object* v___x_2573_; 
v___x_2573_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__14));
v___y_2559_ = v___x_2573_;
goto v___jp_2558_;
}
case 8:
{
lean_object* v___x_2574_; 
v___x_2574_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__15));
v___y_2559_ = v___x_2574_;
goto v___jp_2558_;
}
case 9:
{
lean_object* v___x_2575_; 
v___x_2575_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__16));
v___y_2559_ = v___x_2575_;
goto v___jp_2558_;
}
case 10:
{
lean_object* v___x_2576_; 
v___x_2576_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__17));
v___y_2559_ = v___x_2576_;
goto v___jp_2558_;
}
case 11:
{
lean_object* v___x_2577_; 
v___x_2577_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__18));
v___y_2559_ = v___x_2577_;
goto v___jp_2558_;
}
case 12:
{
lean_object* v___x_2578_; 
v___x_2578_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__19));
v___y_2559_ = v___x_2578_;
goto v___jp_2558_;
}
default: 
{
lean_object* v_message_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v_message_2579_ = lean_ctor_get(v_err_2556_, 0);
lean_inc_ref(v_message_2579_);
lean_dec_ref_known(v_err_2556_, 1);
v___x_2580_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__20));
v___x_2581_ = lean_string_append(v___x_2580_, v_message_2579_);
lean_dec_ref(v_message_2579_);
v___y_2559_ = v___x_2581_;
goto v___jp_2558_;
}
}
v___jp_2558_:
{
lean_object* v___f_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_inc_ref(v___y_2559_);
v___f_2560_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2560_, 0, v___y_2559_);
lean_closure_set(v___f_2560_, 1, v___y_2473_);
lean_closure_set(v___f_2560_, 2, v___f_2557_);
v___x_2561_ = lean_mk_io_user_error(v___y_2559_);
v___x_2562_ = lean_unsigned_to_nat(0u);
v___x_2563_ = 0;
v___x_2564_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_2467_, v_handler_2468_, v___x_2561_);
v___x_2565_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2562_, v___x_2563_, v___x_2564_, v___f_2560_);
return v___x_2565_;
}
}
case 4:
{
lean_object* v___f_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_dec_ref(v_connectionContext_2470_);
lean_dec_ref(v_inst_2469_);
lean_dec(v_handler_2468_);
lean_dec_ref(v_inst_2467_);
lean_dec_ref(v_config_2466_);
lean_inc_ref(v___y_2473_);
v___f_2582_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2582_, 0, v___y_2473_);
v___x_2583_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__21));
v___x_2584_ = lean_unsigned_to_nat(0u);
v___x_2585_ = 0;
v___x_2586_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v___y_2473_, v___x_2583_);
v___x_2587_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2584_, v___x_2585_, v___x_2586_, v___f_2582_);
return v___x_2587_;
}
case 6:
{
lean_object* v___f_2588_; lean_object* v___f_2589_; lean_object* v___f_2590_; lean_object* v___f_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
lean_dec_ref(v_connectionContext_2470_);
lean_dec(v_handler_2468_);
lean_dec_ref(v_inst_2467_);
lean_inc_ref_n(v___y_2473_, 2);
v___f_2588_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_2588_, 0, v___y_2473_);
lean_closure_set(v___f_2588_, 1, v_config_2466_);
v___f_2589_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_2589_, 0, v___f_2588_);
lean_inc_ref(v___f_2589_);
v___f_2590_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_2590_, 0, v___f_2589_);
v___f_2591_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 6, 4);
lean_closure_set(v___f_2591_, 0, v___y_2473_);
lean_closure_set(v___f_2591_, 1, v_inst_2469_);
lean_closure_set(v___f_2591_, 2, v___f_2590_);
lean_closure_set(v___f_2591_, 3, v___f_2589_);
v___x_2592_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__21));
v___x_2593_ = lean_unsigned_to_nat(0u);
v___x_2594_ = 0;
v___x_2595_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v___y_2473_, v___x_2592_);
v___x_2596_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2593_, v___x_2594_, v___x_2595_, v___f_2591_);
return v___x_2596_;
}
case 7:
{
lean_object* v_pendingHead_2597_; 
lean_dec_ref(v_inst_2469_);
v_pendingHead_2597_ = lean_ctor_get(v___y_2473_, 8);
if (lean_obj_tag(v_pendingHead_2597_) == 1)
{
lean_object* v_machine_2598_; lean_object* v_requestStream_2599_; lean_object* v_keepAliveTimeout_2600_; lean_object* v_currentTimeout_2601_; lean_object* v_headerTimeout_2602_; lean_object* v_response_2603_; lean_object* v_respStream_2604_; uint8_t v_requiresData_2605_; lean_object* v_expectData_2606_; uint8_t v_handlerDispatched_2607_; uint8_t v_requestFinalOffered_2608_; lean_object* v_handlerTask_2609_; lean_object* v_dateSecond_2610_; uint8_t v_peerClosed_2611_; uint8_t v_requestEnded_2612_; lean_object* v_val_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
lean_inc_ref(v_pendingHead_2597_);
v_machine_2598_ = lean_ctor_get(v___y_2473_, 0);
lean_inc_ref(v_machine_2598_);
v_requestStream_2599_ = lean_ctor_get(v___y_2473_, 1);
lean_inc_ref(v_requestStream_2599_);
v_keepAliveTimeout_2600_ = lean_ctor_get(v___y_2473_, 2);
lean_inc(v_keepAliveTimeout_2600_);
v_currentTimeout_2601_ = lean_ctor_get(v___y_2473_, 3);
lean_inc(v_currentTimeout_2601_);
v_headerTimeout_2602_ = lean_ctor_get(v___y_2473_, 4);
lean_inc(v_headerTimeout_2602_);
v_response_2603_ = lean_ctor_get(v___y_2473_, 5);
lean_inc_ref(v_response_2603_);
v_respStream_2604_ = lean_ctor_get(v___y_2473_, 6);
lean_inc(v_respStream_2604_);
v_requiresData_2605_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11);
v_expectData_2606_ = lean_ctor_get(v___y_2473_, 7);
lean_inc(v_expectData_2606_);
v_handlerDispatched_2607_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11 + 1);
v_requestFinalOffered_2608_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11 + 2);
v_handlerTask_2609_ = lean_ctor_get(v___y_2473_, 9);
lean_inc(v_handlerTask_2609_);
v_dateSecond_2610_ = lean_ctor_get(v___y_2473_, 10);
lean_inc(v_dateSecond_2610_);
v_peerClosed_2611_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11 + 3);
v_requestEnded_2612_ = lean_ctor_get_uint8(v___y_2473_, sizeof(void*)*11 + 4);
lean_dec_ref(v___y_2473_);
v_val_2613_ = lean_ctor_get(v_pendingHead_2597_, 0);
lean_inc(v_val_2613_);
v___x_2614_ = lean_box(v_requiresData_2605_);
v___x_2615_ = lean_box(v_handlerDispatched_2607_);
v___x_2616_ = lean_box(v_requestFinalOffered_2608_);
v___x_2617_ = lean_box(v_peerClosed_2611_);
v___x_2618_ = lean_box(v_requestEnded_2612_);
v___f_2619_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 17, 15);
lean_closure_set(v___f_2619_, 0, v_requestStream_2599_);
lean_closure_set(v___f_2619_, 1, v_keepAliveTimeout_2600_);
lean_closure_set(v___f_2619_, 2, v_currentTimeout_2601_);
lean_closure_set(v___f_2619_, 3, v_headerTimeout_2602_);
lean_closure_set(v___f_2619_, 4, v_response_2603_);
lean_closure_set(v___f_2619_, 5, v_respStream_2604_);
lean_closure_set(v___f_2619_, 6, v___x_2614_);
lean_closure_set(v___f_2619_, 7, v_expectData_2606_);
lean_closure_set(v___f_2619_, 8, v___x_2615_);
lean_closure_set(v___f_2619_, 9, v_pendingHead_2597_);
lean_closure_set(v___f_2619_, 10, v___x_2616_);
lean_closure_set(v___f_2619_, 11, v_handlerTask_2609_);
lean_closure_set(v___f_2619_, 12, v_dateSecond_2610_);
lean_closure_set(v___f_2619_, 13, v___x_2617_);
lean_closure_set(v___f_2619_, 14, v___x_2618_);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = 0;
v___x_2622_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2467_, v_handler_2468_, v_machine_2598_, v_val_2613_, v_config_2466_, v_connectionContext_2470_);
v___x_2623_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2620_, v___x_2621_, v___x_2622_, v___f_2619_);
return v___x_2623_;
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec_ref(v_connectionContext_2470_);
lean_dec(v_handler_2468_);
lean_dec_ref(v_inst_2467_);
lean_dec_ref(v_config_2466_);
v___x_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___y_2473_);
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2624_);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
return v___x_2626_;
}
}
default: 
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
lean_dec(v_a_2471_);
lean_dec_ref(v_connectionContext_2470_);
lean_dec_ref(v_inst_2469_);
lean_dec(v_handler_2468_);
lean_dec_ref(v_inst_2467_);
lean_dec_ref(v_config_2466_);
v___x_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___y_2473_);
v___x_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
return v___x_2629_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v_config_2630_, lean_object* v_inst_2631_, lean_object* v_handler_2632_, lean_object* v_inst_2633_, lean_object* v_connectionContext_2634_, lean_object* v_a_2635_, lean_object* v_x_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v_config_2630_, v_inst_2631_, v_handler_2632_, v_inst_2633_, v_connectionContext_2634_, v_a_2635_, v_x_2636_, v___y_2637_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_x_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2642_, 0, v_x_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_x_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_x_2643_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2647_, lean_object* v_inst_2648_, lean_object* v_handler_2649_, lean_object* v_config_2650_, lean_object* v_connectionContext_2651_, lean_object* v_events_2652_, lean_object* v_state_2653_){
_start:
{
lean_object* v___f_2655_; lean_object* v___f_2656_; lean_object* v___x_2657_; size_t v_sz_2658_; size_t v___x_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; lean_object* v___x_3495__overap_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___f_2655_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 9, 5);
lean_closure_set(v___f_2655_, 0, v_config_2650_);
lean_closure_set(v___f_2655_, 1, v_inst_2647_);
lean_closure_set(v___f_2655_, 2, v_handler_2649_);
lean_closure_set(v___f_2655_, 3, v_inst_2648_);
lean_closure_set(v___f_2655_, 4, v_connectionContext_2651_);
v___f_2656_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_2657_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0);
v_sz_2658_ = lean_array_size(v_events_2652_);
v___x_2659_ = ((size_t)0ULL);
v___x_2660_ = lean_unsigned_to_nat(0u);
v___x_2661_ = 0;
v___x_3495__overap_2662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2657_, v_events_2652_, v___f_2655_, v_sz_2658_, v___x_2659_, v_state_2653_);
v___x_2663_ = lean_apply_1(v___x_3495__overap_2662_, lean_box(0));
v___x_2664_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2660_, v___x_2661_, v___x_2663_, v___f_2656_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2665_, lean_object* v_inst_2666_, lean_object* v_handler_2667_, lean_object* v_config_2668_, lean_object* v_connectionContext_2669_, lean_object* v_events_2670_, lean_object* v_state_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2665_, v_inst_2666_, v_handler_2667_, v_config_2668_, v_connectionContext_2669_, v_events_2670_, v_state_2671_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2674_, lean_object* v_00_u03b2_2675_, lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_handler_2678_, lean_object* v_config_2679_, lean_object* v_connectionContext_2680_, lean_object* v_events_2681_, lean_object* v_state_2682_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2676_, v_inst_2677_, v_handler_2678_, v_config_2679_, v_connectionContext_2680_, v_events_2681_, v_state_2682_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2685_, lean_object* v_00_u03b2_2686_, lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_handler_2689_, lean_object* v_config_2690_, lean_object* v_connectionContext_2691_, lean_object* v_events_2692_, lean_object* v_state_2693_, lean_object* v_a_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2685_, v_00_u03b2_2686_, v_inst_2687_, v_inst_2688_, v_handler_2689_, v_config_2690_, v_connectionContext_2691_, v_events_2692_, v_state_2693_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2696_){
_start:
{
if (lean_obj_tag(v_x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2698_; 
v_a_2697_ = lean_ctor_get(v_x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref_known(v_x_2696_, 1);
v___x_2698_ = lean_task_pure(v_a_2697_);
return v___x_2698_;
}
else
{
lean_object* v_a_2699_; 
v_a_2699_ = lean_ctor_get(v_x_2696_, 0);
lean_inc_ref(v_a_2699_);
lean_dec_ref_known(v_x_2696_, 1);
return v_a_2699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_a_2700_, lean_object* v_machine_2701_, lean_object* v_requestStream_2702_, lean_object* v_keepAliveTimeout_2703_, lean_object* v_currentTimeout_2704_, lean_object* v_headerTimeout_2705_, lean_object* v_response_2706_, lean_object* v_respStream_2707_, uint8_t v_requiresData_2708_, lean_object* v_expectData_2709_, uint8_t v_requestFinalOffered_2710_, lean_object* v_dateSecond_2711_, uint8_t v_peerClosed_2712_, uint8_t v_requestEnded_2713_, lean_object* v_x_2714_){
_start:
{
if (lean_obj_tag(v_x_2714_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v_dateSecond_2711_);
lean_dec(v_expectData_2709_);
lean_dec(v_respStream_2707_);
lean_dec_ref(v_response_2706_);
lean_dec(v_headerTimeout_2705_);
lean_dec(v_currentTimeout_2704_);
lean_dec(v_keepAliveTimeout_2703_);
lean_dec_ref(v_requestStream_2702_);
lean_dec_ref(v_machine_2701_);
lean_dec_ref(v_a_2700_);
v_a_2716_ = lean_ctor_get(v_x_2714_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_x_2714_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2718_ = v_x_2714_;
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v_x_2714_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2724_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
}
else
{
lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2736_; 
v_isSharedCheck_2736_ = !lean_is_exclusive(v_x_2714_);
if (v_isSharedCheck_2736_ == 0)
{
lean_object* v_unused_2737_; 
v_unused_2737_ = lean_ctor_get(v_x_2714_, 0);
lean_dec(v_unused_2737_);
v___x_2726_ = v_x_2714_;
v_isShared_2727_ = v_isSharedCheck_2736_;
goto v_resetjp_2725_;
}
else
{
lean_dec(v_x_2714_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2736_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
uint8_t v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2728_ = 1;
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_a_2700_);
v___x_2731_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v___x_2731_, 0, v_machine_2701_);
lean_ctor_set(v___x_2731_, 1, v_requestStream_2702_);
lean_ctor_set(v___x_2731_, 2, v_keepAliveTimeout_2703_);
lean_ctor_set(v___x_2731_, 3, v_currentTimeout_2704_);
lean_ctor_set(v___x_2731_, 4, v_headerTimeout_2705_);
lean_ctor_set(v___x_2731_, 5, v_response_2706_);
lean_ctor_set(v___x_2731_, 6, v_respStream_2707_);
lean_ctor_set(v___x_2731_, 7, v_expectData_2709_);
lean_ctor_set(v___x_2731_, 8, v___x_2729_);
lean_ctor_set(v___x_2731_, 9, v___x_2730_);
lean_ctor_set(v___x_2731_, 10, v_dateSecond_2711_);
lean_ctor_set_uint8(v___x_2731_, sizeof(void*)*11, v_requiresData_2708_);
lean_ctor_set_uint8(v___x_2731_, sizeof(void*)*11 + 1, v___x_2728_);
lean_ctor_set_uint8(v___x_2731_, sizeof(void*)*11 + 2, v_requestFinalOffered_2710_);
lean_ctor_set_uint8(v___x_2731_, sizeof(void*)*11 + 3, v_peerClosed_2712_);
lean_ctor_set_uint8(v___x_2731_, sizeof(void*)*11 + 4, v_requestEnded_2713_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 0, v___x_2731_);
v___x_2733_ = v___x_2726_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
return v___x_2734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_a_2738_, lean_object* v_machine_2739_, lean_object* v_requestStream_2740_, lean_object* v_keepAliveTimeout_2741_, lean_object* v_currentTimeout_2742_, lean_object* v_headerTimeout_2743_, lean_object* v_response_2744_, lean_object* v_respStream_2745_, lean_object* v_requiresData_2746_, lean_object* v_expectData_2747_, lean_object* v_requestFinalOffered_2748_, lean_object* v_dateSecond_2749_, lean_object* v_peerClosed_2750_, lean_object* v_requestEnded_2751_, lean_object* v_x_2752_, lean_object* v___y_2753_){
_start:
{
uint8_t v_requiresData_boxed_2754_; uint8_t v_requestFinalOffered_boxed_2755_; uint8_t v_peerClosed_boxed_2756_; uint8_t v_requestEnded_boxed_2757_; lean_object* v_res_2758_; 
v_requiresData_boxed_2754_ = lean_unbox(v_requiresData_2746_);
v_requestFinalOffered_boxed_2755_ = lean_unbox(v_requestFinalOffered_2748_);
v_peerClosed_boxed_2756_ = lean_unbox(v_peerClosed_2750_);
v_requestEnded_boxed_2757_ = lean_unbox(v_requestEnded_2751_);
v_res_2758_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_a_2738_, v_machine_2739_, v_requestStream_2740_, v_keepAliveTimeout_2741_, v_currentTimeout_2742_, v_headerTimeout_2743_, v_response_2744_, v_respStream_2745_, v_requiresData_boxed_2754_, v_expectData_2747_, v_requestFinalOffered_boxed_2755_, v_dateSecond_2749_, v_peerClosed_boxed_2756_, v_requestEnded_boxed_2757_, v_x_2752_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_machine_2759_, lean_object* v_requestStream_2760_, lean_object* v_keepAliveTimeout_2761_, lean_object* v_currentTimeout_2762_, lean_object* v_headerTimeout_2763_, lean_object* v_response_2764_, lean_object* v_respStream_2765_, uint8_t v_requiresData_2766_, lean_object* v_expectData_2767_, uint8_t v_requestFinalOffered_2768_, lean_object* v_dateSecond_2769_, uint8_t v_peerClosed_2770_, uint8_t v_requestEnded_2771_, lean_object* v_toFunctor_2772_, lean_object* v___x_2773_, lean_object* v_x_2774_){
_start:
{
if (lean_obj_tag(v_x_2774_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v___x_2773_);
lean_dec_ref(v_toFunctor_2772_);
lean_dec(v_dateSecond_2769_);
lean_dec(v_expectData_2767_);
lean_dec(v_respStream_2765_);
lean_dec_ref(v_response_2764_);
lean_dec(v_headerTimeout_2763_);
lean_dec(v_currentTimeout_2762_);
lean_dec(v_keepAliveTimeout_2761_);
lean_dec_ref(v_requestStream_2760_);
lean_dec_ref(v_machine_2759_);
v_a_2776_ = lean_ctor_get(v_x_2774_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_x_2774_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2778_ = v_x_2774_;
v_isShared_2779_ = v_isSharedCheck_2784_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v_x_2774_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2784_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
return v___x_2782_;
}
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2804_; 
v_a_2785_ = lean_ctor_get(v_x_2774_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_x_2774_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2787_ = v_x_2774_;
v_isShared_2788_ = v_isSharedCheck_2804_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v_x_2774_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2804_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___f_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2789_ = lean_box(v_requiresData_2766_);
v___x_2790_ = lean_box(v_requestFinalOffered_2768_);
v___x_2791_ = lean_box(v_peerClosed_2770_);
v___x_2792_ = lean_box(v_requestEnded_2771_);
lean_inc_ref(v_response_2764_);
lean_inc(v_a_2785_);
v___f_2793_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 16, 14);
lean_closure_set(v___f_2793_, 0, v_a_2785_);
lean_closure_set(v___f_2793_, 1, v_machine_2759_);
lean_closure_set(v___f_2793_, 2, v_requestStream_2760_);
lean_closure_set(v___f_2793_, 3, v_keepAliveTimeout_2761_);
lean_closure_set(v___f_2793_, 4, v_currentTimeout_2762_);
lean_closure_set(v___f_2793_, 5, v_headerTimeout_2763_);
lean_closure_set(v___f_2793_, 6, v_response_2764_);
lean_closure_set(v___f_2793_, 7, v_respStream_2765_);
lean_closure_set(v___f_2793_, 8, v___x_2789_);
lean_closure_set(v___f_2793_, 9, v_expectData_2767_);
lean_closure_set(v___f_2793_, 10, v___x_2790_);
lean_closure_set(v___f_2793_, 11, v_dateSecond_2769_);
lean_closure_set(v___f_2793_, 12, v___x_2791_);
lean_closure_set(v___f_2793_, 13, v___x_2792_);
v___x_2794_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_2794_, 0, lean_box(0));
lean_closure_set(v___x_2794_, 1, lean_box(0));
lean_closure_set(v___x_2794_, 2, v_toFunctor_2772_);
v___x_2795_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_2795_, 0, lean_box(0));
lean_closure_set(v___x_2795_, 1, v_response_2764_);
v___x_2796_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_2796_, 0, lean_box(0));
lean_closure_set(v___x_2796_, 1, lean_box(0));
lean_closure_set(v___x_2796_, 2, lean_box(0));
lean_closure_set(v___x_2796_, 3, v___x_2794_);
lean_closure_set(v___x_2796_, 4, v___x_2795_);
v___x_2797_ = 0;
lean_inc(v___x_2773_);
v___x_2798_ = l_BaseIO_chainTask___redArg(v_a_2785_, v___x_2796_, v___x_2773_, v___x_2797_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2798_);
v___x_2800_ = v___x_2787_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
v___x_2802_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2773_, v___x_2797_, v___x_2801_, v___f_2793_);
return v___x_2802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_machine_2805_ = _args[0];
lean_object* v_requestStream_2806_ = _args[1];
lean_object* v_keepAliveTimeout_2807_ = _args[2];
lean_object* v_currentTimeout_2808_ = _args[3];
lean_object* v_headerTimeout_2809_ = _args[4];
lean_object* v_response_2810_ = _args[5];
lean_object* v_respStream_2811_ = _args[6];
lean_object* v_requiresData_2812_ = _args[7];
lean_object* v_expectData_2813_ = _args[8];
lean_object* v_requestFinalOffered_2814_ = _args[9];
lean_object* v_dateSecond_2815_ = _args[10];
lean_object* v_peerClosed_2816_ = _args[11];
lean_object* v_requestEnded_2817_ = _args[12];
lean_object* v_toFunctor_2818_ = _args[13];
lean_object* v___x_2819_ = _args[14];
lean_object* v_x_2820_ = _args[15];
lean_object* v___y_2821_ = _args[16];
_start:
{
uint8_t v_requiresData_boxed_2822_; uint8_t v_requestFinalOffered_boxed_2823_; uint8_t v_peerClosed_boxed_2824_; uint8_t v_requestEnded_boxed_2825_; lean_object* v_res_2826_; 
v_requiresData_boxed_2822_ = lean_unbox(v_requiresData_2812_);
v_requestFinalOffered_boxed_2823_ = lean_unbox(v_requestFinalOffered_2814_);
v_peerClosed_boxed_2824_ = lean_unbox(v_peerClosed_2816_);
v_requestEnded_boxed_2825_ = lean_unbox(v_requestEnded_2817_);
v_res_2826_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_machine_2805_, v_requestStream_2806_, v_keepAliveTimeout_2807_, v_currentTimeout_2808_, v_headerTimeout_2809_, v_response_2810_, v_respStream_2811_, v_requiresData_boxed_2822_, v_expectData_2813_, v_requestFinalOffered_boxed_2823_, v_dateSecond_2815_, v_peerClosed_boxed_2824_, v_requestEnded_boxed_2825_, v_toFunctor_2818_, v___x_2819_, v_x_2820_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_2828_, lean_object* v_handler_2829_, lean_object* v_extensions_2830_, lean_object* v_connectionContext_2831_, lean_object* v_state_2832_){
_start:
{
lean_object* v___x_2834_; lean_object* v_toApplicative_2835_; lean_object* v_pendingHead_2836_; 
v___x_2834_ = l_instMonadBaseIO;
v_toApplicative_2835_ = lean_ctor_get(v___x_2834_, 0);
v_pendingHead_2836_ = lean_ctor_get(v_state_2832_, 8);
lean_inc(v_pendingHead_2836_);
if (lean_obj_tag(v_pendingHead_2836_) == 1)
{
lean_object* v_toFunctor_2837_; lean_object* v_machine_2838_; lean_object* v_requestStream_2839_; lean_object* v_keepAliveTimeout_2840_; lean_object* v_currentTimeout_2841_; lean_object* v_headerTimeout_2842_; lean_object* v_response_2843_; lean_object* v_respStream_2844_; uint8_t v_requiresData_2845_; lean_object* v_expectData_2846_; uint8_t v_requestFinalOffered_2847_; lean_object* v_dateSecond_2848_; uint8_t v_peerClosed_2849_; uint8_t v_requestEnded_2850_; lean_object* v_val_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2875_; 
v_toFunctor_2837_ = lean_ctor_get(v_toApplicative_2835_, 0);
v_machine_2838_ = lean_ctor_get(v_state_2832_, 0);
lean_inc_ref(v_machine_2838_);
v_requestStream_2839_ = lean_ctor_get(v_state_2832_, 1);
lean_inc_ref(v_requestStream_2839_);
v_keepAliveTimeout_2840_ = lean_ctor_get(v_state_2832_, 2);
lean_inc(v_keepAliveTimeout_2840_);
v_currentTimeout_2841_ = lean_ctor_get(v_state_2832_, 3);
lean_inc(v_currentTimeout_2841_);
v_headerTimeout_2842_ = lean_ctor_get(v_state_2832_, 4);
lean_inc(v_headerTimeout_2842_);
v_response_2843_ = lean_ctor_get(v_state_2832_, 5);
lean_inc_ref(v_response_2843_);
v_respStream_2844_ = lean_ctor_get(v_state_2832_, 6);
lean_inc(v_respStream_2844_);
v_requiresData_2845_ = lean_ctor_get_uint8(v_state_2832_, sizeof(void*)*11);
v_expectData_2846_ = lean_ctor_get(v_state_2832_, 7);
lean_inc(v_expectData_2846_);
v_requestFinalOffered_2847_ = lean_ctor_get_uint8(v_state_2832_, sizeof(void*)*11 + 2);
v_dateSecond_2848_ = lean_ctor_get(v_state_2832_, 10);
lean_inc(v_dateSecond_2848_);
v_peerClosed_2849_ = lean_ctor_get_uint8(v_state_2832_, sizeof(void*)*11 + 3);
v_requestEnded_2850_ = lean_ctor_get_uint8(v_state_2832_, sizeof(void*)*11 + 4);
lean_dec_ref(v_state_2832_);
v_val_2851_ = lean_ctor_get(v_pendingHead_2836_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_pendingHead_2836_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2853_ = v_pendingHead_2836_;
v_isShared_2854_ = v_isSharedCheck_2875_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_val_2851_);
lean_dec(v_pendingHead_2836_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2875_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v_onRequest_2855_; lean_object* v___f_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___f_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2871_; 
v_onRequest_2855_ = lean_ctor_get(v_inst_2828_, 1);
lean_inc_ref(v_onRequest_2855_);
lean_dec_ref(v_inst_2828_);
v___f_2856_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
lean_inc_ref(v_requestStream_2839_);
v___x_2857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2857_, 0, v_val_2851_);
lean_ctor_set(v___x_2857_, 1, v_requestStream_2839_);
lean_ctor_set(v___x_2857_, 2, v_extensions_2830_);
v___x_2858_ = lean_apply_3(v_onRequest_2855_, v_handler_2829_, v___x_2857_, v_connectionContext_2831_);
v___x_2859_ = lean_unsigned_to_nat(0u);
v___x_2860_ = lean_box(v_requiresData_2845_);
v___x_2861_ = lean_box(v_requestFinalOffered_2847_);
v___x_2862_ = lean_box(v_peerClosed_2849_);
v___x_2863_ = lean_box(v_requestEnded_2850_);
lean_inc_ref(v_toFunctor_2837_);
v___f_2864_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 17, 15);
lean_closure_set(v___f_2864_, 0, v_machine_2838_);
lean_closure_set(v___f_2864_, 1, v_requestStream_2839_);
lean_closure_set(v___f_2864_, 2, v_keepAliveTimeout_2840_);
lean_closure_set(v___f_2864_, 3, v_currentTimeout_2841_);
lean_closure_set(v___f_2864_, 4, v_headerTimeout_2842_);
lean_closure_set(v___f_2864_, 5, v_response_2843_);
lean_closure_set(v___f_2864_, 6, v_respStream_2844_);
lean_closure_set(v___f_2864_, 7, v___x_2860_);
lean_closure_set(v___f_2864_, 8, v_expectData_2846_);
lean_closure_set(v___f_2864_, 9, v___x_2861_);
lean_closure_set(v___f_2864_, 10, v_dateSecond_2848_);
lean_closure_set(v___f_2864_, 11, v___x_2862_);
lean_closure_set(v___f_2864_, 12, v___x_2863_);
lean_closure_set(v___f_2864_, 13, v_toFunctor_2837_);
lean_closure_set(v___f_2864_, 14, v___x_2859_);
v___x_2865_ = 0;
v___x_2866_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_2866_, 0, lean_box(0));
lean_closure_set(v___x_2866_, 1, v___x_2858_);
v___x_2867_ = lean_io_as_task(v___x_2866_, v___x_2859_);
v___x_2868_ = 1;
v___x_2869_ = lean_task_bind(v___x_2867_, v___f_2856_, v___x_2859_, v___x_2868_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2869_);
v___x_2871_ = v___x_2853_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
v___x_2873_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2859_, v___x_2865_, v___x_2872_, v___f_2864_);
return v___x_2873_;
}
}
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec(v_pendingHead_2836_);
lean_dec_ref(v_connectionContext_2831_);
lean_dec(v_extensions_2830_);
lean_dec(v_handler_2829_);
lean_dec_ref(v_inst_2828_);
v___x_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2876_, 0, v_state_2832_);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_2878_, lean_object* v_handler_2879_, lean_object* v_extensions_2880_, lean_object* v_connectionContext_2881_, lean_object* v_state_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2878_, v_handler_2879_, v_extensions_2880_, v_connectionContext_2881_, v_state_2882_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_2885_, lean_object* v_inst_2886_, lean_object* v_handler_2887_, lean_object* v_extensions_2888_, lean_object* v_connectionContext_2889_, lean_object* v_state_2890_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_2886_, v_handler_2887_, v_extensions_2888_, v_connectionContext_2889_, v_state_2890_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_2893_, lean_object* v_inst_2894_, lean_object* v_handler_2895_, lean_object* v_extensions_2896_, lean_object* v_connectionContext_2897_, lean_object* v_state_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_2893_, v_inst_2894_, v_handler_2895_, v_extensions_2896_, v_connectionContext_2897_, v_state_2898_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_2901_, lean_object* v_____r_2902_){
_start:
{
lean_object* v_writer_2904_; lean_object* v_reader_2905_; lean_object* v_config_2906_; lean_object* v_events_2907_; lean_object* v_error_2908_; lean_object* v_date_2909_; uint8_t v_keepAlive_2910_; uint8_t v_pullBodyStalled_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2938_; 
v_writer_2904_ = lean_ctor_get(v_machine_2901_, 1);
v_reader_2905_ = lean_ctor_get(v_machine_2901_, 0);
v_config_2906_ = lean_ctor_get(v_machine_2901_, 2);
v_events_2907_ = lean_ctor_get(v_machine_2901_, 3);
v_error_2908_ = lean_ctor_get(v_machine_2901_, 4);
v_date_2909_ = lean_ctor_get(v_machine_2901_, 5);
v_keepAlive_2910_ = lean_ctor_get_uint8(v_machine_2901_, sizeof(void*)*6);
v_pullBodyStalled_2911_ = lean_ctor_get_uint8(v_machine_2901_, sizeof(void*)*6 + 1);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_machine_2901_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2913_ = v_machine_2901_;
v_isShared_2914_ = v_isSharedCheck_2938_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_date_2909_);
lean_inc(v_error_2908_);
lean_inc(v_events_2907_);
lean_inc(v_config_2906_);
lean_inc(v_writer_2904_);
lean_inc(v_reader_2905_);
lean_dec(v_machine_2901_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2938_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v_userData_2915_; lean_object* v_outputData_2916_; lean_object* v_state_2917_; lean_object* v_knownSize_2918_; lean_object* v_messageHead_2919_; uint8_t v_sentMessage_2920_; uint8_t v_omitBody_2921_; lean_object* v_userDataBytes_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2937_; 
v_userData_2915_ = lean_ctor_get(v_writer_2904_, 0);
v_outputData_2916_ = lean_ctor_get(v_writer_2904_, 1);
v_state_2917_ = lean_ctor_get(v_writer_2904_, 2);
v_knownSize_2918_ = lean_ctor_get(v_writer_2904_, 3);
v_messageHead_2919_ = lean_ctor_get(v_writer_2904_, 4);
v_sentMessage_2920_ = lean_ctor_get_uint8(v_writer_2904_, sizeof(void*)*6);
v_omitBody_2921_ = lean_ctor_get_uint8(v_writer_2904_, sizeof(void*)*6 + 2);
v_userDataBytes_2922_ = lean_ctor_get(v_writer_2904_, 5);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_writer_2904_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2924_ = v_writer_2904_;
v_isShared_2925_ = v_isSharedCheck_2937_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_userDataBytes_2922_);
lean_inc(v_messageHead_2919_);
lean_inc(v_knownSize_2918_);
lean_inc(v_state_2917_);
lean_inc(v_outputData_2916_);
lean_inc(v_userData_2915_);
lean_dec(v_writer_2904_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2937_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
uint8_t v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = 1;
if (v_isShared_2925_ == 0)
{
v___x_2928_ = v___x_2924_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_userData_2915_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_outputData_2916_);
lean_ctor_set(v_reuseFailAlloc_2936_, 2, v_state_2917_);
lean_ctor_set(v_reuseFailAlloc_2936_, 3, v_knownSize_2918_);
lean_ctor_set(v_reuseFailAlloc_2936_, 4, v_messageHead_2919_);
lean_ctor_set(v_reuseFailAlloc_2936_, 5, v_userDataBytes_2922_);
lean_ctor_set_uint8(v_reuseFailAlloc_2936_, sizeof(void*)*6, v_sentMessage_2920_);
lean_ctor_set_uint8(v_reuseFailAlloc_2936_, sizeof(void*)*6 + 2, v_omitBody_2921_);
v___x_2928_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2930_; 
lean_ctor_set_uint8(v___x_2928_, sizeof(void*)*6 + 1, v___x_2926_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v___x_2928_);
v___x_2930_ = v___x_2913_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_reader_2905_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v___x_2928_);
lean_ctor_set(v_reuseFailAlloc_2935_, 2, v_config_2906_);
lean_ctor_set(v_reuseFailAlloc_2935_, 3, v_events_2907_);
lean_ctor_set(v_reuseFailAlloc_2935_, 4, v_error_2908_);
lean_ctor_set(v_reuseFailAlloc_2935_, 5, v_date_2909_);
lean_ctor_set_uint8(v_reuseFailAlloc_2935_, sizeof(void*)*6, v_keepAlive_2910_);
lean_ctor_set_uint8(v_reuseFailAlloc_2935_, sizeof(void*)*6 + 1, v_pullBodyStalled_2911_);
v___x_2930_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2931_ = lean_box(0);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2930_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
v___x_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
return v___x_2934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_2939_, lean_object* v_____r_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_2939_, v_____r_2940_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_2943_, lean_object* v_x2_2944_){
_start:
{
lean_object* v_data_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_data_2945_ = lean_ctor_get(v_x2_2944_, 0);
v___x_2946_ = lean_byte_array_size(v_data_2945_);
v___x_2947_ = lean_nat_add(v_x1_2943_, v___x_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_2948_, lean_object* v_x2_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_2948_, v_x2_2949_);
lean_dec_ref(v_x2_2949_);
lean_dec(v_x1_2948_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_2951_, lean_object* v_machine_2952_, lean_object* v_isClosed_2953_, lean_object* v___f_2954_, lean_object* v___f_2955_, lean_object* v_x_2956_){
_start:
{
lean_object* v___y_2959_; 
if (lean_obj_tag(v_x_2956_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2972_; 
lean_dec_ref(v___f_2955_);
lean_dec_ref(v___f_2954_);
lean_dec_ref(v_isClosed_2953_);
lean_dec_ref(v_machine_2952_);
lean_dec(v_body_2951_);
v_a_2964_ = lean_ctor_get(v_x_2956_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v_x_2956_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2966_ = v_x_2956_;
v_isShared_2967_ = v_isSharedCheck_2972_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v_x_2956_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2972_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2970_; 
v___x_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
return v___x_2970_;
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3035_; 
v_a_2973_ = lean_ctor_get(v_x_2956_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_x_2956_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_2975_ = v_x_2956_;
v_isShared_2976_ = v_isSharedCheck_3035_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v_x_2956_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3035_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
if (lean_obj_tag(v_a_2973_) == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2980_; 
lean_dec_ref(v___f_2955_);
lean_dec_ref(v___f_2954_);
lean_dec_ref(v_isClosed_2953_);
v___x_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2977_, 0, v_body_2951_);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v_machine_2952_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_2978_);
v___x_2980_ = v___x_2975_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
return v___x_2981_;
}
}
else
{
lean_object* v_val_2983_; 
lean_del_object(v___x_2975_);
v_val_2983_ = lean_ctor_get(v_a_2973_, 0);
lean_inc(v_val_2983_);
lean_dec_ref_known(v_a_2973_, 1);
if (lean_obj_tag(v_val_2983_) == 0)
{
lean_object* v___x_2984_; uint8_t v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec_ref(v___f_2955_);
lean_dec_ref(v_machine_2952_);
v___x_2984_ = lean_unsigned_to_nat(0u);
v___x_2985_ = 0;
v___x_2986_ = lean_apply_2(v_isClosed_2953_, v_body_2951_, lean_box(0));
v___x_2987_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2984_, v___x_2985_, v___x_2986_, v___f_2954_);
return v___x_2987_;
}
else
{
lean_object* v_val_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
lean_dec_ref(v___f_2954_);
lean_dec_ref(v_isClosed_2953_);
v_val_2988_ = lean_ctor_get(v_val_2983_, 0);
lean_inc(v_val_2988_);
lean_dec_ref_known(v_val_2983_, 1);
v___x_2989_ = lean_unsigned_to_nat(1u);
v___x_2990_ = lean_mk_empty_array_with_capacity(v___x_2989_);
v___x_2991_ = lean_array_push(v___x_2990_, v_val_2988_);
v___x_2992_ = lean_array_get_size(v___x_2991_);
v___x_2993_ = lean_unsigned_to_nat(0u);
v___x_2994_ = lean_nat_dec_eq(v___x_2992_, v___x_2993_);
if (v___x_2994_ == 0)
{
lean_object* v_reader_2995_; lean_object* v_writer_2996_; lean_object* v_config_2997_; lean_object* v_events_2998_; lean_object* v_error_2999_; lean_object* v_date_3000_; uint8_t v_keepAlive_3001_; uint8_t v_pullBodyStalled_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3034_; 
v_reader_2995_ = lean_ctor_get(v_machine_2952_, 0);
v_writer_2996_ = lean_ctor_get(v_machine_2952_, 1);
v_config_2997_ = lean_ctor_get(v_machine_2952_, 2);
v_events_2998_ = lean_ctor_get(v_machine_2952_, 3);
v_error_2999_ = lean_ctor_get(v_machine_2952_, 4);
v_date_3000_ = lean_ctor_get(v_machine_2952_, 5);
v_keepAlive_3001_ = lean_ctor_get_uint8(v_machine_2952_, sizeof(void*)*6);
v_pullBodyStalled_3002_ = lean_ctor_get_uint8(v_machine_2952_, sizeof(void*)*6 + 1);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_machine_2952_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3004_ = v_machine_2952_;
v_isShared_3005_ = v_isSharedCheck_3034_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_date_3000_);
lean_inc(v_error_2999_);
lean_inc(v_events_2998_);
lean_inc(v_config_2997_);
lean_inc(v_writer_2996_);
lean_inc(v_reader_2995_);
lean_dec(v_machine_2952_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3034_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___y_3007_; lean_object* v___x_3029_; uint8_t v___x_3030_; 
v___x_3029_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_3030_ = lean_nat_dec_lt(v___x_2993_, v___x_2992_);
if (v___x_3030_ == 0)
{
lean_dec_ref(v___f_2955_);
v___y_3007_ = v___x_2993_;
goto v___jp_3006_;
}
else
{
size_t v___x_3031_; size_t v___x_3032_; lean_object* v___x_3033_; 
v___x_3031_ = ((size_t)0ULL);
v___x_3032_ = lean_usize_of_nat(v___x_2992_);
lean_inc_ref(v___x_2991_);
v___x_3033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3029_, v___f_2955_, v___x_2991_, v___x_3031_, v___x_3032_, v___x_2993_);
v___y_3007_ = v___x_3033_;
goto v___jp_3006_;
}
v___jp_3006_:
{
lean_object* v_userData_3008_; lean_object* v_outputData_3009_; lean_object* v_state_3010_; lean_object* v_knownSize_3011_; lean_object* v_messageHead_3012_; uint8_t v_sentMessage_3013_; uint8_t v_userClosedBody_3014_; uint8_t v_omitBody_3015_; lean_object* v_userDataBytes_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3028_; 
v_userData_3008_ = lean_ctor_get(v_writer_2996_, 0);
v_outputData_3009_ = lean_ctor_get(v_writer_2996_, 1);
v_state_3010_ = lean_ctor_get(v_writer_2996_, 2);
v_knownSize_3011_ = lean_ctor_get(v_writer_2996_, 3);
v_messageHead_3012_ = lean_ctor_get(v_writer_2996_, 4);
v_sentMessage_3013_ = lean_ctor_get_uint8(v_writer_2996_, sizeof(void*)*6);
v_userClosedBody_3014_ = lean_ctor_get_uint8(v_writer_2996_, sizeof(void*)*6 + 1);
v_omitBody_3015_ = lean_ctor_get_uint8(v_writer_2996_, sizeof(void*)*6 + 2);
v_userDataBytes_3016_ = lean_ctor_get(v_writer_2996_, 5);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_writer_2996_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3018_ = v_writer_2996_;
v_isShared_3019_ = v_isSharedCheck_3028_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_userDataBytes_3016_);
lean_inc(v_messageHead_3012_);
lean_inc(v_knownSize_3011_);
lean_inc(v_state_3010_);
lean_inc(v_outputData_3009_);
lean_inc(v_userData_3008_);
lean_dec(v_writer_2996_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3028_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3020_ = l_Array_append___redArg(v_userData_3008_, v___x_2991_);
lean_dec_ref(v___x_2991_);
v___x_3021_ = lean_nat_add(v_userDataBytes_3016_, v___y_3007_);
lean_dec(v___y_3007_);
lean_dec(v_userDataBytes_3016_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 5, v___x_3021_);
lean_ctor_set(v___x_3018_, 0, v___x_3020_);
v___x_3023_ = v___x_3018_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_outputData_3009_);
lean_ctor_set(v_reuseFailAlloc_3027_, 2, v_state_3010_);
lean_ctor_set(v_reuseFailAlloc_3027_, 3, v_knownSize_3011_);
lean_ctor_set(v_reuseFailAlloc_3027_, 4, v_messageHead_3012_);
lean_ctor_set(v_reuseFailAlloc_3027_, 5, v___x_3021_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, sizeof(void*)*6, v_sentMessage_3013_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, sizeof(void*)*6 + 1, v_userClosedBody_3014_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, sizeof(void*)*6 + 2, v_omitBody_3015_);
v___x_3023_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3025_; 
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 1, v___x_3023_);
v___x_3025_ = v___x_3004_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_reader_2995_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3026_, 2, v_config_2997_);
lean_ctor_set(v_reuseFailAlloc_3026_, 3, v_events_2998_);
lean_ctor_set(v_reuseFailAlloc_3026_, 4, v_error_2999_);
lean_ctor_set(v_reuseFailAlloc_3026_, 5, v_date_3000_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, sizeof(void*)*6, v_keepAlive_3001_);
lean_ctor_set_uint8(v_reuseFailAlloc_3026_, sizeof(void*)*6 + 1, v_pullBodyStalled_3002_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
v___y_2959_ = v___x_3025_;
goto v___jp_2958_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2991_);
lean_dec_ref(v___f_2955_);
v___y_2959_ = v_machine_2952_;
goto v___jp_2958_;
}
}
}
}
}
v___jp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2960_, 0, v_body_2951_);
v___x_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___y_2959_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_3036_, lean_object* v_machine_3037_, lean_object* v_isClosed_3038_, lean_object* v___f_3039_, lean_object* v___f_3040_, lean_object* v_x_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_3036_, v_machine_3037_, v_isClosed_3038_, v___f_3039_, v___f_3040_, v_x_3041_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_3045_, lean_object* v_machine_3046_, lean_object* v_body_3047_){
_start:
{
lean_object* v_close_3049_; lean_object* v_isClosed_3050_; lean_object* v_tryRecv_3051_; lean_object* v___f_3052_; lean_object* v___f_3053_; lean_object* v___f_3054_; lean_object* v___f_3055_; lean_object* v___f_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v_close_3049_ = lean_ctor_get(v_inst_3045_, 1);
lean_inc_ref(v_close_3049_);
v_isClosed_3050_ = lean_ctor_get(v_inst_3045_, 2);
lean_inc_ref(v_isClosed_3050_);
v_tryRecv_3051_ = lean_ctor_get(v_inst_3045_, 4);
lean_inc_ref(v_tryRecv_3051_);
lean_dec_ref(v_inst_3045_);
lean_inc_ref(v_machine_3046_);
v___f_3052_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3052_, 0, v_machine_3046_);
lean_inc_ref(v___f_3052_);
v___f_3053_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3053_, 0, v___f_3052_);
lean_inc_n(v_body_3047_, 2);
v___f_3054_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3054_, 0, v_close_3049_);
lean_closure_set(v___f_3054_, 1, v_body_3047_);
lean_closure_set(v___f_3054_, 2, v___f_3053_);
lean_closure_set(v___f_3054_, 3, v___f_3052_);
v___f_3055_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_3056_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_3056_, 0, v_body_3047_);
lean_closure_set(v___f_3056_, 1, v_machine_3046_);
lean_closure_set(v___f_3056_, 2, v_isClosed_3050_);
lean_closure_set(v___f_3056_, 3, v___f_3054_);
lean_closure_set(v___f_3056_, 4, v___f_3055_);
v___x_3057_ = lean_unsigned_to_nat(0u);
v___x_3058_ = 0;
v___x_3059_ = lean_apply_2(v_tryRecv_3051_, v_body_3047_, lean_box(0));
v___x_3060_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3057_, v___x_3058_, v___x_3059_, v___f_3056_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_3061_, lean_object* v_machine_3062_, lean_object* v_body_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3061_, v_machine_3062_, v_body_3063_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_3066_, lean_object* v_inst_3067_, lean_object* v_machine_3068_, lean_object* v_body_3069_){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3067_, v_machine_3068_, v_body_3069_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_3072_, lean_object* v_inst_3073_, lean_object* v_machine_3074_, lean_object* v_body_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_3072_, v_inst_3073_, v_machine_3074_, v_body_3075_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_3084_, lean_object* v_____r_3085_, lean_object* v_st_3086_){
_start:
{
lean_object* v_machine_3088_; lean_object* v_requestStream_3089_; lean_object* v_keepAliveTimeout_3090_; lean_object* v_currentTimeout_3091_; lean_object* v_headerTimeout_3092_; lean_object* v_response_3093_; lean_object* v_respStream_3094_; uint8_t v_requiresData_3095_; lean_object* v_expectData_3096_; uint8_t v_handlerDispatched_3097_; lean_object* v_pendingHead_3098_; uint8_t v_requestFinalOffered_3099_; lean_object* v_handlerTask_3100_; lean_object* v_dateSecond_3101_; uint8_t v_peerClosed_3102_; uint8_t v_requestEnded_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3184_; 
v_machine_3088_ = lean_ctor_get(v_st_3086_, 0);
v_requestStream_3089_ = lean_ctor_get(v_st_3086_, 1);
v_keepAliveTimeout_3090_ = lean_ctor_get(v_st_3086_, 2);
v_currentTimeout_3091_ = lean_ctor_get(v_st_3086_, 3);
v_headerTimeout_3092_ = lean_ctor_get(v_st_3086_, 4);
v_response_3093_ = lean_ctor_get(v_st_3086_, 5);
v_respStream_3094_ = lean_ctor_get(v_st_3086_, 6);
v_requiresData_3095_ = lean_ctor_get_uint8(v_st_3086_, sizeof(void*)*11);
v_expectData_3096_ = lean_ctor_get(v_st_3086_, 7);
v_handlerDispatched_3097_ = lean_ctor_get_uint8(v_st_3086_, sizeof(void*)*11 + 1);
v_pendingHead_3098_ = lean_ctor_get(v_st_3086_, 8);
v_requestFinalOffered_3099_ = lean_ctor_get_uint8(v_st_3086_, sizeof(void*)*11 + 2);
v_handlerTask_3100_ = lean_ctor_get(v_st_3086_, 9);
v_dateSecond_3101_ = lean_ctor_get(v_st_3086_, 10);
v_peerClosed_3102_ = lean_ctor_get_uint8(v_st_3086_, sizeof(void*)*11 + 3);
v_requestEnded_3103_ = lean_ctor_get_uint8(v_st_3086_, sizeof(void*)*11 + 4);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_st_3086_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3105_ = v_st_3086_;
v_isShared_3106_ = v_isSharedCheck_3184_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_dateSecond_3101_);
lean_inc(v_handlerTask_3100_);
lean_inc(v_pendingHead_3098_);
lean_inc(v_expectData_3096_);
lean_inc(v_respStream_3094_);
lean_inc(v_response_3093_);
lean_inc(v_headerTimeout_3092_);
lean_inc(v_currentTimeout_3091_);
lean_inc(v_keepAliveTimeout_3090_);
lean_inc(v_requestStream_3089_);
lean_inc(v_machine_3088_);
lean_dec(v_st_3086_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3184_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___y_3108_; lean_object* v_reader_3117_; lean_object* v_state_3118_; 
v_reader_3117_ = lean_ctor_get(v_machine_3088_, 0);
lean_inc_ref(v_reader_3117_);
v_state_3118_ = lean_ctor_get(v_reader_3117_, 0);
lean_inc(v_state_3118_);
if (lean_obj_tag(v_state_3118_) == 6)
{
lean_dec_ref(v_reader_3117_);
lean_dec_ref(v_val_3084_);
v___y_3108_ = v_machine_3088_;
goto v___jp_3107_;
}
else
{
if (lean_obj_tag(v_state_3118_) == 7)
{
lean_dec_ref_known(v_state_3118_, 1);
lean_dec_ref(v_reader_3117_);
lean_dec_ref(v_val_3084_);
v___y_3108_ = v_machine_3088_;
goto v___jp_3107_;
}
else
{
lean_object* v_input_3119_; lean_object* v_writer_3120_; lean_object* v_config_3121_; lean_object* v_events_3122_; lean_object* v_error_3123_; lean_object* v_date_3124_; uint8_t v_keepAlive_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3182_; 
v_input_3119_ = lean_ctor_get(v_reader_3117_, 1);
lean_inc_ref(v_input_3119_);
v_writer_3120_ = lean_ctor_get(v_machine_3088_, 1);
v_config_3121_ = lean_ctor_get(v_machine_3088_, 2);
v_events_3122_ = lean_ctor_get(v_machine_3088_, 3);
v_error_3123_ = lean_ctor_get(v_machine_3088_, 4);
v_date_3124_ = lean_ctor_get(v_machine_3088_, 5);
v_keepAlive_3125_ = lean_ctor_get_uint8(v_machine_3088_, sizeof(void*)*6);
v_isSharedCheck_3182_ = !lean_is_exclusive(v_machine_3088_);
if (v_isSharedCheck_3182_ == 0)
{
lean_object* v_unused_3183_; 
v_unused_3183_ = lean_ctor_get(v_machine_3088_, 0);
lean_dec(v_unused_3183_);
v___x_3127_ = v_machine_3088_;
v_isShared_3128_ = v_isSharedCheck_3182_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_date_3124_);
lean_inc(v_error_3123_);
lean_inc(v_events_3122_);
lean_inc(v_config_3121_);
lean_inc(v_writer_3120_);
lean_dec(v_machine_3088_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3182_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v_messageHead_3129_; lean_object* v_messageCount_3130_; lean_object* v_bodyBytesRead_3131_; lean_object* v_headerBytesRead_3132_; uint8_t v_noMoreInput_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3179_; 
v_messageHead_3129_ = lean_ctor_get(v_reader_3117_, 2);
v_messageCount_3130_ = lean_ctor_get(v_reader_3117_, 3);
v_bodyBytesRead_3131_ = lean_ctor_get(v_reader_3117_, 4);
v_headerBytesRead_3132_ = lean_ctor_get(v_reader_3117_, 5);
v_noMoreInput_3133_ = lean_ctor_get_uint8(v_reader_3117_, sizeof(void*)*6);
v_isSharedCheck_3179_ = !lean_is_exclusive(v_reader_3117_);
if (v_isSharedCheck_3179_ == 0)
{
lean_object* v_unused_3180_; lean_object* v_unused_3181_; 
v_unused_3180_ = lean_ctor_get(v_reader_3117_, 1);
lean_dec(v_unused_3180_);
v_unused_3181_ = lean_ctor_get(v_reader_3117_, 0);
lean_dec(v_unused_3181_);
v___x_3135_ = v_reader_3117_;
v_isShared_3136_ = v_isSharedCheck_3179_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_headerBytesRead_3132_);
lean_inc(v_bodyBytesRead_3131_);
lean_inc(v_messageCount_3130_);
lean_inc(v_messageHead_3129_);
lean_dec(v_reader_3117_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3179_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v_array_3137_; lean_object* v_idx_3138_; uint8_t v___x_3139_; lean_object* v___y_3141_; lean_object* v___x_3170_; uint8_t v___x_3171_; 
v_array_3137_ = lean_ctor_get(v_input_3119_, 0);
lean_inc_ref(v_array_3137_);
v_idx_3138_ = lean_ctor_get(v_input_3119_, 1);
lean_inc(v_idx_3138_);
lean_dec_ref(v_input_3119_);
v___x_3139_ = 0;
v___x_3170_ = lean_byte_array_size(v_array_3137_);
v___x_3171_ = lean_nat_dec_le(v___x_3170_, v_idx_3138_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3172_ = l_ByteArray_extract(v_array_3137_, v_idx_3138_, v___x_3170_);
lean_dec_ref(v_array_3137_);
v___x_3173_ = lean_unsigned_to_nat(0u);
v___x_3174_ = lean_byte_array_size(v___x_3172_);
v___x_3175_ = lean_byte_array_size(v_val_3084_);
v___x_3176_ = lean_byte_array_copy_slice(v_val_3084_, v___x_3173_, v___x_3172_, v___x_3174_, v___x_3175_, v___x_3171_);
lean_dec_ref(v_val_3084_);
v___x_3177_ = l_ByteArray_mkIterator(v___x_3176_);
v___y_3141_ = v___x_3177_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3178_; 
lean_dec(v_idx_3138_);
lean_dec_ref(v_array_3137_);
v___x_3178_ = l_ByteArray_mkIterator(v_val_3084_);
v___y_3141_ = v___x_3178_;
goto v___jp_3140_;
}
v___jp_3140_:
{
lean_object* v_maxHeaderBytes_3142_; lean_object* v_maxStartLineLength_3143_; lean_object* v_maxChunkLineLength_3144_; lean_object* v_maxBodySize_3145_; lean_object* v_array_3146_; lean_object* v_idx_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v_maxHeaderBytes_3142_ = lean_ctor_get(v_config_3121_, 2);
v_maxStartLineLength_3143_ = lean_ctor_get(v_config_3121_, 5);
v_maxChunkLineLength_3144_ = lean_ctor_get(v_config_3121_, 13);
v_maxBodySize_3145_ = lean_ctor_get(v_config_3121_, 15);
v_array_3146_ = lean_ctor_get(v___y_3141_, 0);
v_idx_3147_ = lean_ctor_get(v___y_3141_, 1);
v___x_3148_ = lean_nat_add(v_maxBodySize_3145_, v_maxHeaderBytes_3142_);
v___x_3149_ = lean_nat_add(v___x_3148_, v_maxStartLineLength_3143_);
lean_dec(v___x_3148_);
v___x_3150_ = lean_nat_add(v___x_3149_, v_maxChunkLineLength_3144_);
lean_dec(v___x_3149_);
v___x_3151_ = lean_byte_array_size(v_array_3146_);
v___x_3152_ = lean_nat_sub(v___x_3151_, v_idx_3147_);
v___x_3153_ = lean_nat_dec_lt(v___x_3150_, v___x_3152_);
lean_dec(v___x_3152_);
lean_dec(v___x_3150_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3155_; 
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 1, v___y_3141_);
v___x_3155_ = v___x_3135_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_state_3118_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___y_3141_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_messageHead_3129_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_messageCount_3130_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_bodyBytesRead_3131_);
lean_ctor_set(v_reuseFailAlloc_3159_, 5, v_headerBytesRead_3132_);
lean_ctor_set_uint8(v_reuseFailAlloc_3159_, sizeof(void*)*6, v_noMoreInput_3133_);
v___x_3155_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v_machine_3157_; 
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v___x_3155_);
v_machine_3157_ = v___x_3127_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_writer_3120_);
lean_ctor_set(v_reuseFailAlloc_3158_, 2, v_config_3121_);
lean_ctor_set(v_reuseFailAlloc_3158_, 3, v_events_3122_);
lean_ctor_set(v_reuseFailAlloc_3158_, 4, v_error_3123_);
lean_ctor_set(v_reuseFailAlloc_3158_, 5, v_date_3124_);
lean_ctor_set_uint8(v_reuseFailAlloc_3158_, sizeof(void*)*6, v_keepAlive_3125_);
v_machine_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_ctor_set_uint8(v_machine_3157_, sizeof(void*)*6 + 1, v___x_3139_);
v___y_3108_ = v_machine_3157_;
goto v___jp_3107_;
}
}
}
else
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
lean_dec(v_error_3123_);
lean_dec(v_state_3118_);
v___x_3160_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_3161_ = lean_array_push(v_events_3122_, v___x_3160_);
v___x_3162_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 1, v___y_3141_);
lean_ctor_set(v___x_3135_, 0, v___x_3162_);
v___x_3164_ = v___x_3135_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___y_3141_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v_messageHead_3129_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v_messageCount_3130_);
lean_ctor_set(v_reuseFailAlloc_3169_, 4, v_bodyBytesRead_3131_);
lean_ctor_set(v_reuseFailAlloc_3169_, 5, v_headerBytesRead_3132_);
lean_ctor_set_uint8(v_reuseFailAlloc_3169_, sizeof(void*)*6, v_noMoreInput_3133_);
v___x_3164_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3165_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__2));
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 4, v___x_3165_);
lean_ctor_set(v___x_3127_, 3, v___x_3161_);
lean_ctor_set(v___x_3127_, 0, v___x_3164_);
v___x_3167_ = v___x_3127_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_writer_3120_);
lean_ctor_set(v_reuseFailAlloc_3168_, 2, v_config_3121_);
lean_ctor_set(v_reuseFailAlloc_3168_, 3, v___x_3161_);
lean_ctor_set(v_reuseFailAlloc_3168_, 4, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3168_, 5, v_date_3124_);
lean_ctor_set_uint8(v_reuseFailAlloc_3168_, sizeof(void*)*6, v_keepAlive_3125_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_ctor_set_uint8(v___x_3167_, sizeof(void*)*6 + 1, v___x_3139_);
v___y_3108_ = v___x_3167_;
goto v___jp_3107_;
}
}
}
}
}
}
}
}
v___jp_3107_:
{
lean_object* v___x_3110_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___y_3108_);
v___x_3110_ = v___x_3105_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___y_3108_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_requestStream_3089_);
lean_ctor_set(v_reuseFailAlloc_3116_, 2, v_keepAliveTimeout_3090_);
lean_ctor_set(v_reuseFailAlloc_3116_, 3, v_currentTimeout_3091_);
lean_ctor_set(v_reuseFailAlloc_3116_, 4, v_headerTimeout_3092_);
lean_ctor_set(v_reuseFailAlloc_3116_, 5, v_response_3093_);
lean_ctor_set(v_reuseFailAlloc_3116_, 6, v_respStream_3094_);
lean_ctor_set(v_reuseFailAlloc_3116_, 7, v_expectData_3096_);
lean_ctor_set(v_reuseFailAlloc_3116_, 8, v_pendingHead_3098_);
lean_ctor_set(v_reuseFailAlloc_3116_, 9, v_handlerTask_3100_);
lean_ctor_set(v_reuseFailAlloc_3116_, 10, v_dateSecond_3101_);
lean_ctor_set_uint8(v_reuseFailAlloc_3116_, sizeof(void*)*11, v_requiresData_3095_);
lean_ctor_set_uint8(v_reuseFailAlloc_3116_, sizeof(void*)*11 + 1, v_handlerDispatched_3097_);
lean_ctor_set_uint8(v_reuseFailAlloc_3116_, sizeof(void*)*11 + 2, v_requestFinalOffered_3099_);
lean_ctor_set_uint8(v_reuseFailAlloc_3116_, sizeof(void*)*11 + 3, v_peerClosed_3102_);
lean_ctor_set_uint8(v_reuseFailAlloc_3116_, sizeof(void*)*11 + 4, v_requestEnded_3103_);
v___x_3110_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
uint8_t v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3111_ = 0;
v___x_3112_ = lean_box(v___x_3111_);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3110_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
v___x_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3114_);
return v___x_3115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_3185_, lean_object* v_____r_3186_, lean_object* v_st_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3185_, v_____r_3186_, v_st_3187_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_3190_, lean_object* v_machine_3191_, lean_object* v_requestStream_3192_, lean_object* v_currentTimeout_3193_, lean_object* v_response_3194_, lean_object* v_respStream_3195_, uint8_t v_requiresData_3196_, lean_object* v_expectData_3197_, uint8_t v_handlerDispatched_3198_, lean_object* v_pendingHead_3199_, uint8_t v_requestFinalOffered_3200_, lean_object* v_handlerTask_3201_, lean_object* v_dateSecond_3202_, uint8_t v_peerClosed_3203_, uint8_t v_requestEnded_3204_, lean_object* v___f_3205_, lean_object* v_x_3206_){
_start:
{
if (lean_obj_tag(v_x_3206_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref(v___f_3205_);
lean_dec(v_dateSecond_3202_);
lean_dec(v_handlerTask_3201_);
lean_dec(v_pendingHead_3199_);
lean_dec(v_expectData_3197_);
lean_dec(v_respStream_3195_);
lean_dec_ref(v_response_3194_);
lean_dec(v_currentTimeout_3193_);
lean_dec_ref(v_requestStream_3192_);
lean_dec_ref(v_machine_3191_);
v_a_3208_ = lean_ctor_get(v_x_3206_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_x_3206_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3210_ = v_x_3206_;
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v_x_3206_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3216_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3214_; 
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
return v___x_3214_;
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v_headerTimeout_3218_; lean_object* v_second_3219_; lean_object* v_nano_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v_second_3224_; lean_object* v_nano_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v_nanos_3229_; lean_object* v___x_3230_; lean_object* v_nanos_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v_a_3217_ = lean_ctor_get(v_x_3206_, 0);
lean_inc(v_a_3217_);
lean_dec_ref_known(v_x_3206_, 1);
v_headerTimeout_3218_ = lean_ctor_get(v_config_3190_, 6);
v_second_3219_ = lean_ctor_get(v_a_3217_, 0);
lean_inc(v_second_3219_);
v_nano_3220_ = lean_ctor_get(v_a_3217_, 1);
lean_inc(v_nano_3220_);
lean_dec(v_a_3217_);
v___x_3221_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__2);
v___x_3222_ = lean_int_mul(v_headerTimeout_3218_, v___x_3221_);
v___x_3223_ = l_Std_Time_Duration_ofNanoseconds(v___x_3222_);
lean_dec(v___x_3222_);
v_second_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_second_3224_);
v_nano_3225_ = lean_ctor_get(v___x_3223_, 1);
lean_inc(v_nano_3225_);
lean_dec_ref(v___x_3223_);
v___x_3226_ = lean_box(0);
v___x_3227_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__11___closed__0);
v___x_3228_ = lean_int_mul(v_second_3219_, v___x_3227_);
lean_dec(v_second_3219_);
v_nanos_3229_ = lean_int_add(v___x_3228_, v_nano_3220_);
lean_dec(v_nano_3220_);
lean_dec(v___x_3228_);
v___x_3230_ = lean_int_mul(v_second_3224_, v___x_3227_);
lean_dec(v_second_3224_);
v_nanos_3231_ = lean_int_add(v___x_3230_, v_nano_3225_);
lean_dec(v_nano_3225_);
lean_dec(v___x_3230_);
v___x_3232_ = lean_int_add(v_nanos_3229_, v_nanos_3231_);
lean_dec(v_nanos_3231_);
lean_dec(v_nanos_3229_);
v___x_3233_ = l_Std_Time_Duration_ofNanoseconds(v___x_3232_);
lean_dec(v___x_3232_);
v___x_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
v___x_3235_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v___x_3235_, 0, v_machine_3191_);
lean_ctor_set(v___x_3235_, 1, v_requestStream_3192_);
lean_ctor_set(v___x_3235_, 2, v___x_3226_);
lean_ctor_set(v___x_3235_, 3, v_currentTimeout_3193_);
lean_ctor_set(v___x_3235_, 4, v___x_3234_);
lean_ctor_set(v___x_3235_, 5, v_response_3194_);
lean_ctor_set(v___x_3235_, 6, v_respStream_3195_);
lean_ctor_set(v___x_3235_, 7, v_expectData_3197_);
lean_ctor_set(v___x_3235_, 8, v_pendingHead_3199_);
lean_ctor_set(v___x_3235_, 9, v_handlerTask_3201_);
lean_ctor_set(v___x_3235_, 10, v_dateSecond_3202_);
lean_ctor_set_uint8(v___x_3235_, sizeof(void*)*11, v_requiresData_3196_);
lean_ctor_set_uint8(v___x_3235_, sizeof(void*)*11 + 1, v_handlerDispatched_3198_);
lean_ctor_set_uint8(v___x_3235_, sizeof(void*)*11 + 2, v_requestFinalOffered_3200_);
lean_ctor_set_uint8(v___x_3235_, sizeof(void*)*11 + 3, v_peerClosed_3203_);
lean_ctor_set_uint8(v___x_3235_, sizeof(void*)*11 + 4, v_requestEnded_3204_);
v___x_3236_ = lean_box(0);
v___x_3237_ = lean_apply_3(v___f_3205_, v___x_3236_, v___x_3235_, lean_box(0));
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_config_3238_ = _args[0];
lean_object* v_machine_3239_ = _args[1];
lean_object* v_requestStream_3240_ = _args[2];
lean_object* v_currentTimeout_3241_ = _args[3];
lean_object* v_response_3242_ = _args[4];
lean_object* v_respStream_3243_ = _args[5];
lean_object* v_requiresData_3244_ = _args[6];
lean_object* v_expectData_3245_ = _args[7];
lean_object* v_handlerDispatched_3246_ = _args[8];
lean_object* v_pendingHead_3247_ = _args[9];
lean_object* v_requestFinalOffered_3248_ = _args[10];
lean_object* v_handlerTask_3249_ = _args[11];
lean_object* v_dateSecond_3250_ = _args[12];
lean_object* v_peerClosed_3251_ = _args[13];
lean_object* v_requestEnded_3252_ = _args[14];
lean_object* v___f_3253_ = _args[15];
lean_object* v_x_3254_ = _args[16];
lean_object* v___y_3255_ = _args[17];
_start:
{
uint8_t v_requiresData_boxed_3256_; uint8_t v_handlerDispatched_boxed_3257_; uint8_t v_requestFinalOffered_boxed_3258_; uint8_t v_peerClosed_boxed_3259_; uint8_t v_requestEnded_boxed_3260_; lean_object* v_res_3261_; 
v_requiresData_boxed_3256_ = lean_unbox(v_requiresData_3244_);
v_handlerDispatched_boxed_3257_ = lean_unbox(v_handlerDispatched_3246_);
v_requestFinalOffered_boxed_3258_ = lean_unbox(v_requestFinalOffered_3248_);
v_peerClosed_boxed_3259_ = lean_unbox(v_peerClosed_3251_);
v_requestEnded_boxed_3260_ = lean_unbox(v_requestEnded_3252_);
v_res_3261_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_3238_, v_machine_3239_, v_requestStream_3240_, v_currentTimeout_3241_, v_response_3242_, v_respStream_3243_, v_requiresData_boxed_3256_, v_expectData_3245_, v_handlerDispatched_boxed_3257_, v_pendingHead_3247_, v_requestFinalOffered_boxed_3258_, v_handlerTask_3249_, v_dateSecond_3250_, v_peerClosed_boxed_3259_, v_requestEnded_boxed_3260_, v___f_3253_, v_x_3254_);
lean_dec_ref(v_config_3238_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_3262_, lean_object* v_requestStream_3263_, lean_object* v_keepAliveTimeout_3264_, lean_object* v_currentTimeout_3265_, lean_object* v_headerTimeout_3266_, lean_object* v_response_3267_, uint8_t v_requiresData_3268_, lean_object* v_expectData_3269_, uint8_t v_handlerDispatched_3270_, lean_object* v_pendingHead_3271_, uint8_t v_requestFinalOffered_3272_, lean_object* v_handlerTask_3273_, lean_object* v_dateSecond_3274_, uint8_t v_peerClosed_3275_, uint8_t v_requestEnded_3276_, lean_object* v_____r_3277_){
_start:
{
lean_object* v_writer_3279_; lean_object* v_reader_3280_; lean_object* v_config_3281_; lean_object* v_events_3282_; lean_object* v_error_3283_; lean_object* v_date_3284_; uint8_t v_keepAlive_3285_; uint8_t v_pullBodyStalled_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3316_; 
v_writer_3279_ = lean_ctor_get(v_machine_3262_, 1);
v_reader_3280_ = lean_ctor_get(v_machine_3262_, 0);
v_config_3281_ = lean_ctor_get(v_machine_3262_, 2);
v_events_3282_ = lean_ctor_get(v_machine_3262_, 3);
v_error_3283_ = lean_ctor_get(v_machine_3262_, 4);
v_date_3284_ = lean_ctor_get(v_machine_3262_, 5);
v_keepAlive_3285_ = lean_ctor_get_uint8(v_machine_3262_, sizeof(void*)*6);
v_pullBodyStalled_3286_ = lean_ctor_get_uint8(v_machine_3262_, sizeof(void*)*6 + 1);
v_isSharedCheck_3316_ = !lean_is_exclusive(v_machine_3262_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3288_ = v_machine_3262_;
v_isShared_3289_ = v_isSharedCheck_3316_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_date_3284_);
lean_inc(v_error_3283_);
lean_inc(v_events_3282_);
lean_inc(v_config_3281_);
lean_inc(v_writer_3279_);
lean_inc(v_reader_3280_);
lean_dec(v_machine_3262_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3316_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v_userData_3290_; lean_object* v_outputData_3291_; lean_object* v_state_3292_; lean_object* v_knownSize_3293_; lean_object* v_messageHead_3294_; uint8_t v_sentMessage_3295_; uint8_t v_omitBody_3296_; lean_object* v_userDataBytes_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3315_; 
v_userData_3290_ = lean_ctor_get(v_writer_3279_, 0);
v_outputData_3291_ = lean_ctor_get(v_writer_3279_, 1);
v_state_3292_ = lean_ctor_get(v_writer_3279_, 2);
v_knownSize_3293_ = lean_ctor_get(v_writer_3279_, 3);
v_messageHead_3294_ = lean_ctor_get(v_writer_3279_, 4);
v_sentMessage_3295_ = lean_ctor_get_uint8(v_writer_3279_, sizeof(void*)*6);
v_omitBody_3296_ = lean_ctor_get_uint8(v_writer_3279_, sizeof(void*)*6 + 2);
v_userDataBytes_3297_ = lean_ctor_get(v_writer_3279_, 5);
v_isSharedCheck_3315_ = !lean_is_exclusive(v_writer_3279_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3299_ = v_writer_3279_;
v_isShared_3300_ = v_isSharedCheck_3315_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_userDataBytes_3297_);
lean_inc(v_messageHead_3294_);
lean_inc(v_knownSize_3293_);
lean_inc(v_state_3292_);
lean_inc(v_outputData_3291_);
lean_inc(v_userData_3290_);
lean_dec(v_writer_3279_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3315_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
uint8_t v___x_3301_; lean_object* v___x_3303_; 
v___x_3301_ = 1;
if (v_isShared_3300_ == 0)
{
v___x_3303_ = v___x_3299_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_userData_3290_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_outputData_3291_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v_state_3292_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v_knownSize_3293_);
lean_ctor_set(v_reuseFailAlloc_3314_, 4, v_messageHead_3294_);
lean_ctor_set(v_reuseFailAlloc_3314_, 5, v_userDataBytes_3297_);
lean_ctor_set_uint8(v_reuseFailAlloc_3314_, sizeof(void*)*6, v_sentMessage_3295_);
lean_ctor_set_uint8(v_reuseFailAlloc_3314_, sizeof(void*)*6 + 2, v_omitBody_3296_);
v___x_3303_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
lean_object* v___x_3305_; 
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*6 + 1, v___x_3301_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 1, v___x_3303_);
v___x_3305_ = v___x_3288_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_reader_3280_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v___x_3303_);
lean_ctor_set(v_reuseFailAlloc_3313_, 2, v_config_3281_);
lean_ctor_set(v_reuseFailAlloc_3313_, 3, v_events_3282_);
lean_ctor_set(v_reuseFailAlloc_3313_, 4, v_error_3283_);
lean_ctor_set(v_reuseFailAlloc_3313_, 5, v_date_3284_);
lean_ctor_set_uint8(v_reuseFailAlloc_3313_, sizeof(void*)*6, v_keepAlive_3285_);
lean_ctor_set_uint8(v_reuseFailAlloc_3313_, sizeof(void*)*6 + 1, v_pullBodyStalled_3286_);
v___x_3305_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3306_ = lean_box(0);
v___x_3307_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v___x_3307_, 0, v___x_3305_);
lean_ctor_set(v___x_3307_, 1, v_requestStream_3263_);
lean_ctor_set(v___x_3307_, 2, v_keepAliveTimeout_3264_);
lean_ctor_set(v___x_3307_, 3, v_currentTimeout_3265_);
lean_ctor_set(v___x_3307_, 4, v_headerTimeout_3266_);
lean_ctor_set(v___x_3307_, 5, v_response_3267_);
lean_ctor_set(v___x_3307_, 6, v___x_3306_);
lean_ctor_set(v___x_3307_, 7, v_expectData_3269_);
lean_ctor_set(v___x_3307_, 8, v_pendingHead_3271_);
lean_ctor_set(v___x_3307_, 9, v_handlerTask_3273_);
lean_ctor_set(v___x_3307_, 10, v_dateSecond_3274_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*11, v_requiresData_3268_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*11 + 1, v_handlerDispatched_3270_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*11 + 2, v_requestFinalOffered_3272_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*11 + 3, v_peerClosed_3275_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*11 + 4, v_requestEnded_3276_);
v___x_3308_ = 0;
v___x_3309_ = lean_box(v___x_3308_);
v___x_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3307_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
v___x_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
return v___x_3312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_machine_3317_ = _args[0];
lean_object* v_requestStream_3318_ = _args[1];
lean_object* v_keepAliveTimeout_3319_ = _args[2];
lean_object* v_currentTimeout_3320_ = _args[3];
lean_object* v_headerTimeout_3321_ = _args[4];
lean_object* v_response_3322_ = _args[5];
lean_object* v_requiresData_3323_ = _args[6];
lean_object* v_expectData_3324_ = _args[7];
lean_object* v_handlerDispatched_3325_ = _args[8];
lean_object* v_pendingHead_3326_ = _args[9];
lean_object* v_requestFinalOffered_3327_ = _args[10];
lean_object* v_handlerTask_3328_ = _args[11];
lean_object* v_dateSecond_3329_ = _args[12];
lean_object* v_peerClosed_3330_ = _args[13];
lean_object* v_requestEnded_3331_ = _args[14];
lean_object* v_____r_3332_ = _args[15];
lean_object* v___y_3333_ = _args[16];
_start:
{
uint8_t v_requiresData_boxed_3334_; uint8_t v_handlerDispatched_boxed_3335_; uint8_t v_requestFinalOffered_boxed_3336_; uint8_t v_peerClosed_boxed_3337_; uint8_t v_requestEnded_boxed_3338_; lean_object* v_res_3339_; 
v_requiresData_boxed_3334_ = lean_unbox(v_requiresData_3323_);
v_handlerDispatched_boxed_3335_ = lean_unbox(v_handlerDispatched_3325_);
v_requestFinalOffered_boxed_3336_ = lean_unbox(v_requestFinalOffered_3327_);
v_peerClosed_boxed_3337_ = lean_unbox(v_peerClosed_3330_);
v_requestEnded_boxed_3338_ = lean_unbox(v_requestEnded_3331_);
v_res_3339_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3317_, v_requestStream_3318_, v_keepAliveTimeout_3319_, v_currentTimeout_3320_, v_headerTimeout_3321_, v_response_3322_, v_requiresData_boxed_3334_, v_expectData_3324_, v_handlerDispatched_boxed_3335_, v_pendingHead_3326_, v_requestFinalOffered_boxed_3336_, v_handlerTask_3328_, v_dateSecond_3329_, v_peerClosed_boxed_3337_, v_requestEnded_boxed_3338_, v_____r_3332_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_3340_, lean_object* v_x_3341_){
_start:
{
if (lean_obj_tag(v_x_3341_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3351_; 
lean_dec_ref(v___f_3340_);
v_a_3343_ = lean_ctor_get(v_x_3341_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v_x_3341_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3345_ = v_x_3341_;
v_isShared_3346_ = v_isSharedCheck_3351_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v_x_3341_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3351_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3349_; 
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
return v___x_3349_;
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3353_; 
v_a_3352_ = lean_ctor_get(v_x_3341_, 0);
lean_inc(v_a_3352_);
lean_dec_ref_known(v_x_3341_, 1);
v___x_3353_ = lean_apply_2(v___f_3340_, v_a_3352_, lean_box(0));
return v___x_3353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_3354_, lean_object* v_x_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_3354_, v_x_3355_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_3358_, lean_object* v_val_3359_, lean_object* v___f_3360_, lean_object* v___f_3361_, lean_object* v_x_3362_){
_start:
{
if (lean_obj_tag(v_x_3362_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3372_; 
lean_dec_ref(v___f_3361_);
lean_dec_ref(v___f_3360_);
lean_dec(v_val_3359_);
lean_dec_ref(v_close_3358_);
v_a_3364_ = lean_ctor_get(v_x_3362_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_x_3362_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3366_ = v_x_3362_;
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v_x_3362_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3372_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; 
v___x_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
return v___x_3370_;
}
}
}
else
{
lean_object* v_a_3373_; uint8_t v___x_3374_; 
v_a_3373_ = lean_ctor_get(v_x_3362_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v_x_3362_, 1);
v___x_3374_ = lean_unbox(v_a_3373_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; lean_object* v___x_3378_; 
lean_dec_ref(v___f_3361_);
v___x_3375_ = lean_unsigned_to_nat(0u);
v___x_3376_ = lean_apply_2(v_close_3358_, v_val_3359_, lean_box(0));
v___x_3377_ = lean_unbox(v_a_3373_);
lean_dec(v_a_3373_);
v___x_3378_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3375_, v___x_3377_, v___x_3376_, v___f_3360_);
return v___x_3378_;
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
lean_dec(v_a_3373_);
lean_dec_ref(v___f_3360_);
lean_dec(v_val_3359_);
lean_dec_ref(v_close_3358_);
v___x_3379_ = lean_box(0);
v___x_3380_ = lean_apply_2(v___f_3361_, v___x_3379_, lean_box(0));
return v___x_3380_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_3381_, lean_object* v_val_3382_, lean_object* v___f_3383_, lean_object* v___f_3384_, lean_object* v_x_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_3381_, v_val_3382_, v___f_3383_, v___f_3384_, v_x_3385_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_____r_3388_, lean_object* v_st_3389_){
_start:
{
uint8_t v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3391_ = 0;
v___x_3392_ = lean_box(v___x_3391_);
v___x_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3393_, 0, v_st_3389_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
v___x_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_____r_3396_, lean_object* v_st_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_____r_3396_, v_st_3397_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object* v___f_3400_, lean_object* v_x_3401_){
_start:
{
if (lean_obj_tag(v_x_3401_) == 0)
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3411_; 
lean_dec_ref(v___f_3400_);
v_a_3403_ = lean_ctor_get(v_x_3401_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v_x_3401_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3405_ = v_x_3401_;
v_isShared_3406_ = v_isSharedCheck_3411_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v_x_3401_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3411_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3409_; 
v___x_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
return v___x_3409_;
}
}
}
else
{
lean_object* v_a_3412_; lean_object* v_fst_3413_; lean_object* v_snd_3414_; lean_object* v___x_3415_; 
v_a_3412_ = lean_ctor_get(v_x_3401_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v_x_3401_, 1);
v_fst_3413_ = lean_ctor_get(v_a_3412_, 0);
lean_inc(v_fst_3413_);
v_snd_3414_ = lean_ctor_get(v_a_3412_, 1);
lean_inc(v_snd_3414_);
lean_dec(v_a_3412_);
v___x_3415_ = lean_apply_3(v___f_3400_, v_fst_3413_, v_snd_3414_, lean_box(0));
return v___x_3415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v___f_3416_, lean_object* v_x_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v___f_3416_, v_x_3417_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_st_3420_, lean_object* v_x_3421_){
_start:
{
if (lean_obj_tag(v_x_3421_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_st_3420_);
v_a_3423_ = lean_ctor_get(v_x_3421_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_x_3421_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3425_ = v_x_3421_;
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v_x_3421_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
}
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3441_; 
v_a_3432_ = lean_ctor_get(v_x_3421_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_x_3421_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3434_ = v_x_3421_;
v_isShared_3435_ = v_isSharedCheck_3441_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v_x_3421_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3441_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v_a_3432_);
lean_ctor_set(v___x_3436_, 1, v_st_3420_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v___x_3436_);
v___x_3438_ = v___x_3434_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3436_);
v___x_3438_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3439_; 
v___x_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3438_);
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_st_3442_, lean_object* v_x_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_st_3442_, v_x_3443_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_inst_3446_, lean_object* v_handler_3447_, lean_object* v___f_3448_, lean_object* v_x_3449_){
_start:
{
if (lean_obj_tag(v_x_3449_) == 0)
{
lean_object* v_a_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v_a_3451_ = lean_ctor_get(v_x_3449_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v_x_3449_, 1);
v___x_3452_ = lean_unsigned_to_nat(0u);
v___x_3453_ = 0;
v___x_3454_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_3446_, v_handler_3447_, v_a_3451_);
v___x_3455_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3452_, v___x_3453_, v___x_3454_, v___f_3448_);
return v___x_3455_;
}
else
{
lean_object* v___x_3456_; 
lean_dec_ref(v___f_3448_);
lean_dec(v_handler_3447_);
lean_dec_ref(v_inst_3446_);
v___x_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3456_, 0, v_x_3449_);
return v___x_3456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_inst_3457_, lean_object* v_handler_3458_, lean_object* v___f_3459_, lean_object* v_x_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_inst_3457_, v_handler_3458_, v___f_3459_, v_x_3460_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(uint8_t v_final_3463_, lean_object* v_st_3464_, lean_object* v___x_3465_, lean_object* v_requestStream_3466_, lean_object* v_keepAliveTimeout_3467_, lean_object* v_currentTimeout_3468_, lean_object* v_headerTimeout_3469_, lean_object* v_response_3470_, lean_object* v_respStream_3471_, uint8_t v_requiresData_3472_, lean_object* v_expectData_3473_, uint8_t v_handlerDispatched_3474_, lean_object* v_pendingHead_3475_, uint8_t v_x_3476_, lean_object* v_handlerTask_3477_, lean_object* v_dateSecond_3478_, uint8_t v_peerClosed_3479_, uint8_t v_requestEnded_3480_, lean_object* v_x_3481_){
_start:
{
if (lean_obj_tag(v_x_3481_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3491_; 
lean_dec(v_dateSecond_3478_);
lean_dec(v_handlerTask_3477_);
lean_dec(v_pendingHead_3475_);
lean_dec(v_expectData_3473_);
lean_dec(v_respStream_3471_);
lean_dec_ref(v_response_3470_);
lean_dec(v_headerTimeout_3469_);
lean_dec(v_currentTimeout_3468_);
lean_dec(v_keepAliveTimeout_3467_);
lean_dec_ref(v_requestStream_3466_);
lean_dec_ref(v___x_3465_);
lean_dec_ref(v_st_3464_);
v_a_3483_ = lean_ctor_get(v_x_3481_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v_x_3481_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3485_ = v_x_3481_;
v_isShared_3486_ = v_isSharedCheck_3491_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v_x_3481_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3491_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
return v___x_3489_;
}
}
}
else
{
lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3508_; 
v_isSharedCheck_3508_ = !lean_is_exclusive(v_x_3481_);
if (v_isSharedCheck_3508_ == 0)
{
lean_object* v_unused_3509_; 
v_unused_3509_ = lean_ctor_get(v_x_3481_, 0);
lean_dec(v_unused_3509_);
v___x_3493_ = v_x_3481_;
v_isShared_3494_ = v_isSharedCheck_3508_;
goto v_resetjp_3492_;
}
else
{
lean_dec(v_x_3481_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3508_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
if (v_final_3463_ == 0)
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3498_; 
lean_dec(v_dateSecond_3478_);
lean_dec(v_handlerTask_3477_);
lean_dec(v_pendingHead_3475_);
lean_dec(v_expectData_3473_);
lean_dec(v_respStream_3471_);
lean_dec_ref(v_response_3470_);
lean_dec(v_headerTimeout_3469_);
lean_dec(v_currentTimeout_3468_);
lean_dec(v_keepAliveTimeout_3467_);
lean_dec_ref(v_requestStream_3466_);
lean_dec_ref(v___x_3465_);
v___x_3495_ = lean_box(0);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set(v___x_3496_, 1, v_st_3464_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v___x_3496_);
v___x_3498_ = v___x_3493_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3498_);
return v___x_3499_;
}
}
else
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3505_; 
lean_dec_ref(v_st_3464_);
v___x_3501_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v___x_3501_, 0, v___x_3465_);
lean_ctor_set(v___x_3501_, 1, v_requestStream_3466_);
lean_ctor_set(v___x_3501_, 2, v_keepAliveTimeout_3467_);
lean_ctor_set(v___x_3501_, 3, v_currentTimeout_3468_);
lean_ctor_set(v___x_3501_, 4, v_headerTimeout_3469_);
lean_ctor_set(v___x_3501_, 5, v_response_3470_);
lean_ctor_set(v___x_3501_, 6, v_respStream_3471_);
lean_ctor_set(v___x_3501_, 7, v_expectData_3473_);
lean_ctor_set(v___x_3501_, 8, v_pendingHead_3475_);
lean_ctor_set(v___x_3501_, 9, v_handlerTask_3477_);
lean_ctor_set(v___x_3501_, 10, v_dateSecond_3478_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*11, v_requiresData_3472_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*11 + 1, v_handlerDispatched_3474_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*11 + 2, v_x_3476_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*11 + 3, v_peerClosed_3479_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*11 + 4, v_requestEnded_3480_);
v___x_3502_ = lean_box(0);
v___x_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
lean_ctor_set(v___x_3503_, 1, v___x_3501_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v___x_3503_);
v___x_3505_ = v___x_3493_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3503_);
v___x_3505_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
lean_object* v___x_3506_; 
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
return v___x_3506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object** _args){
lean_object* v_final_3510_ = _args[0];
lean_object* v_st_3511_ = _args[1];
lean_object* v___x_3512_ = _args[2];
lean_object* v_requestStream_3513_ = _args[3];
lean_object* v_keepAliveTimeout_3514_ = _args[4];
lean_object* v_currentTimeout_3515_ = _args[5];
lean_object* v_headerTimeout_3516_ = _args[6];
lean_object* v_response_3517_ = _args[7];
lean_object* v_respStream_3518_ = _args[8];
lean_object* v_requiresData_3519_ = _args[9];
lean_object* v_expectData_3520_ = _args[10];
lean_object* v_handlerDispatched_3521_ = _args[11];
lean_object* v_pendingHead_3522_ = _args[12];
lean_object* v_x_3523_ = _args[13];
lean_object* v_handlerTask_3524_ = _args[14];
lean_object* v_dateSecond_3525_ = _args[15];
lean_object* v_peerClosed_3526_ = _args[16];
lean_object* v_requestEnded_3527_ = _args[17];
lean_object* v_x_3528_ = _args[18];
lean_object* v___y_3529_ = _args[19];
_start:
{
uint8_t v_final_boxed_3530_; uint8_t v_requiresData_boxed_3531_; uint8_t v_handlerDispatched_boxed_3532_; uint8_t v_x_8301__boxed_3533_; uint8_t v_peerClosed_boxed_3534_; uint8_t v_requestEnded_boxed_3535_; lean_object* v_res_3536_; 
v_final_boxed_3530_ = lean_unbox(v_final_3510_);
v_requiresData_boxed_3531_ = lean_unbox(v_requiresData_3519_);
v_handlerDispatched_boxed_3532_ = lean_unbox(v_handlerDispatched_3521_);
v_x_8301__boxed_3533_ = lean_unbox(v_x_3523_);
v_peerClosed_boxed_3534_ = lean_unbox(v_peerClosed_3526_);
v_requestEnded_boxed_3535_ = lean_unbox(v_requestEnded_3527_);
v_res_3536_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v_final_boxed_3530_, v_st_3511_, v___x_3512_, v_requestStream_3513_, v_keepAliveTimeout_3514_, v_currentTimeout_3515_, v_headerTimeout_3516_, v_response_3517_, v_respStream_3518_, v_requiresData_boxed_3531_, v_expectData_3520_, v_handlerDispatched_boxed_3532_, v_pendingHead_3522_, v_x_8301__boxed_3533_, v_handlerTask_3524_, v_dateSecond_3525_, v_peerClosed_boxed_3534_, v_requestEnded_boxed_3535_, v_x_3528_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_state_3537_, lean_object* v_x_3538_){
_start:
{
if (lean_obj_tag(v_x_3538_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3548_; 
lean_dec_ref(v_state_3537_);
v_a_3540_ = lean_ctor_get(v_x_3538_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_x_3538_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3542_ = v_x_3538_;
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v_x_3538_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3548_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
return v___x_3546_;
}
}
}
else
{
lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3584_; 
v_isSharedCheck_3584_ = !lean_is_exclusive(v_x_3538_);
if (v_isSharedCheck_3584_ == 0)
{
lean_object* v_unused_3585_; 
v_unused_3585_ = lean_ctor_get(v_x_3538_, 0);
lean_dec(v_unused_3585_);
v___x_3550_ = v_x_3538_;
v_isShared_3551_ = v_isSharedCheck_3584_;
goto v_resetjp_3549_;
}
else
{
lean_dec(v_x_3538_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3584_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v_machine_3552_; lean_object* v_requestStream_3553_; lean_object* v_keepAliveTimeout_3554_; lean_object* v_currentTimeout_3555_; lean_object* v_headerTimeout_3556_; lean_object* v_response_3557_; lean_object* v_respStream_3558_; uint8_t v_requiresData_3559_; lean_object* v_expectData_3560_; lean_object* v_pendingHead_3561_; uint8_t v_requestFinalOffered_3562_; lean_object* v_dateSecond_3563_; uint8_t v_peerClosed_3564_; uint8_t v_requestEnded_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3582_; 
v_machine_3552_ = lean_ctor_get(v_state_3537_, 0);
v_requestStream_3553_ = lean_ctor_get(v_state_3537_, 1);
v_keepAliveTimeout_3554_ = lean_ctor_get(v_state_3537_, 2);
v_currentTimeout_3555_ = lean_ctor_get(v_state_3537_, 3);
v_headerTimeout_3556_ = lean_ctor_get(v_state_3537_, 4);
v_response_3557_ = lean_ctor_get(v_state_3537_, 5);
v_respStream_3558_ = lean_ctor_get(v_state_3537_, 6);
v_requiresData_3559_ = lean_ctor_get_uint8(v_state_3537_, sizeof(void*)*11);
v_expectData_3560_ = lean_ctor_get(v_state_3537_, 7);
v_pendingHead_3561_ = lean_ctor_get(v_state_3537_, 8);
v_requestFinalOffered_3562_ = lean_ctor_get_uint8(v_state_3537_, sizeof(void*)*11 + 2);
v_dateSecond_3563_ = lean_ctor_get(v_state_3537_, 10);
v_peerClosed_3564_ = lean_ctor_get_uint8(v_state_3537_, sizeof(void*)*11 + 3);
v_requestEnded_3565_ = lean_ctor_get_uint8(v_state_3537_, sizeof(void*)*11 + 4);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_state_3537_);
if (v_isSharedCheck_3582_ == 0)
{
lean_object* v_unused_3583_; 
v_unused_3583_ = lean_ctor_get(v_state_3537_, 9);
lean_dec(v_unused_3583_);
v___x_3567_ = v_state_3537_;
v_isShared_3568_ = v_isSharedCheck_3582_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_dateSecond_3563_);
lean_inc(v_pendingHead_3561_);
lean_inc(v_expectData_3560_);
lean_inc(v_respStream_3558_);
lean_inc(v_response_3557_);
lean_inc(v_headerTimeout_3556_);
lean_inc(v_currentTimeout_3555_);
lean_inc(v_keepAliveTimeout_3554_);
lean_inc(v_requestStream_3553_);
lean_inc(v_machine_3552_);
lean_dec(v_state_3537_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3582_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3569_ = lean_box(52);
v___x_3570_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3552_, v___x_3569_);
v___x_3571_ = 0;
v___x_3572_ = lean_box(0);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 9, v___x_3572_);
lean_ctor_set(v___x_3567_, 0, v___x_3570_);
v___x_3574_ = v___x_3567_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3581_, 1, v_requestStream_3553_);
lean_ctor_set(v_reuseFailAlloc_3581_, 2, v_keepAliveTimeout_3554_);
lean_ctor_set(v_reuseFailAlloc_3581_, 3, v_currentTimeout_3555_);
lean_ctor_set(v_reuseFailAlloc_3581_, 4, v_headerTimeout_3556_);
lean_ctor_set(v_reuseFailAlloc_3581_, 5, v_response_3557_);
lean_ctor_set(v_reuseFailAlloc_3581_, 6, v_respStream_3558_);
lean_ctor_set(v_reuseFailAlloc_3581_, 7, v_expectData_3560_);
lean_ctor_set(v_reuseFailAlloc_3581_, 8, v_pendingHead_3561_);
lean_ctor_set(v_reuseFailAlloc_3581_, 9, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3581_, 10, v_dateSecond_3563_);
lean_ctor_set_uint8(v_reuseFailAlloc_3581_, sizeof(void*)*11, v_requiresData_3559_);
lean_ctor_set_uint8(v_reuseFailAlloc_3581_, sizeof(void*)*11 + 2, v_requestFinalOffered_3562_);
lean_ctor_set_uint8(v_reuseFailAlloc_3581_, sizeof(void*)*11 + 3, v_peerClosed_3564_);
lean_ctor_set_uint8(v_reuseFailAlloc_3581_, sizeof(void*)*11 + 4, v_requestEnded_3565_);
v___x_3574_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3578_; 
lean_ctor_set_uint8(v___x_3574_, sizeof(void*)*11 + 1, v___x_3571_);
v___x_3575_ = lean_box(v___x_3571_);
v___x_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3574_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 0, v___x_3576_);
v___x_3578_ = v___x_3550_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
lean_object* v___x_3579_; 
v___x_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
return v___x_3579_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_state_3586_, lean_object* v_x_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_state_3586_, v_x_3587_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v_machine_3590_, lean_object* v_requestStream_3591_, lean_object* v_keepAliveTimeout_3592_, lean_object* v_currentTimeout_3593_, lean_object* v_headerTimeout_3594_, lean_object* v_response_3595_, lean_object* v_respStream_3596_, uint8_t v_requiresData_3597_, lean_object* v_expectData_3598_, lean_object* v_pendingHead_3599_, uint8_t v_requestFinalOffered_3600_, lean_object* v___x_3601_, lean_object* v_dateSecond_3602_, uint8_t v_peerClosed_3603_, uint8_t v_requestEnded_3604_, lean_object* v_____r_3605_){
_start:
{
uint8_t v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3607_ = 0;
v___x_3608_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v___x_3608_, 0, v_machine_3590_);
lean_ctor_set(v___x_3608_, 1, v_requestStream_3591_);
lean_ctor_set(v___x_3608_, 2, v_keepAliveTimeout_3592_);
lean_ctor_set(v___x_3608_, 3, v_currentTimeout_3593_);
lean_ctor_set(v___x_3608_, 4, v_headerTimeout_3594_);
lean_ctor_set(v___x_3608_, 5, v_response_3595_);
lean_ctor_set(v___x_3608_, 6, v_respStream_3596_);
lean_ctor_set(v___x_3608_, 7, v_expectData_3598_);
lean_ctor_set(v___x_3608_, 8, v_pendingHead_3599_);
lean_ctor_set(v___x_3608_, 9, v___x_3601_);
lean_ctor_set(v___x_3608_, 10, v_dateSecond_3602_);
lean_ctor_set_uint8(v___x_3608_, sizeof(void*)*11, v_requiresData_3597_);
lean_ctor_set_uint8(v___x_3608_, sizeof(void*)*11 + 1, v___x_3607_);
lean_ctor_set_uint8(v___x_3608_, sizeof(void*)*11 + 2, v_requestFinalOffered_3600_);
lean_ctor_set_uint8(v___x_3608_, sizeof(void*)*11 + 3, v_peerClosed_3603_);
lean_ctor_set_uint8(v___x_3608_, sizeof(void*)*11 + 4, v_requestEnded_3604_);
v___x_3609_ = lean_box(v___x_3607_);
v___x_3610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3608_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
v___x_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object** _args){
lean_object* v_machine_3613_ = _args[0];
lean_object* v_requestStream_3614_ = _args[1];
lean_object* v_keepAliveTimeout_3615_ = _args[2];
lean_object* v_currentTimeout_3616_ = _args[3];
lean_object* v_headerTimeout_3617_ = _args[4];
lean_object* v_response_3618_ = _args[5];
lean_object* v_respStream_3619_ = _args[6];
lean_object* v_requiresData_3620_ = _args[7];
lean_object* v_expectData_3621_ = _args[8];
lean_object* v_pendingHead_3622_ = _args[9];
lean_object* v_requestFinalOffered_3623_ = _args[10];
lean_object* v___x_3624_ = _args[11];
lean_object* v_dateSecond_3625_ = _args[12];
lean_object* v_peerClosed_3626_ = _args[13];
lean_object* v_requestEnded_3627_ = _args[14];
lean_object* v_____r_3628_ = _args[15];
lean_object* v___y_3629_ = _args[16];
_start:
{
uint8_t v_requiresData_boxed_3630_; uint8_t v_requestFinalOffered_boxed_3631_; uint8_t v_peerClosed_boxed_3632_; uint8_t v_requestEnded_boxed_3633_; lean_object* v_res_3634_; 
v_requiresData_boxed_3630_ = lean_unbox(v_requiresData_3620_);
v_requestFinalOffered_boxed_3631_ = lean_unbox(v_requestFinalOffered_3623_);
v_peerClosed_boxed_3632_ = lean_unbox(v_peerClosed_3626_);
v_requestEnded_boxed_3633_ = lean_unbox(v_requestEnded_3627_);
v_res_3634_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v_machine_3613_, v_requestStream_3614_, v_keepAliveTimeout_3615_, v_currentTimeout_3616_, v_headerTimeout_3617_, v_response_3618_, v_respStream_3619_, v_requiresData_boxed_3630_, v_expectData_3621_, v_pendingHead_3622_, v_requestFinalOffered_boxed_3631_, v___x_3624_, v_dateSecond_3625_, v_peerClosed_boxed_3632_, v_requestEnded_boxed_3633_, v_____r_3628_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v_close_3635_, lean_object* v_body_3636_, lean_object* v___f_3637_, lean_object* v___f_3638_, lean_object* v_x_3639_){
_start:
{
if (lean_obj_tag(v_x_3639_) == 0)
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3649_; 
lean_dec_ref(v___f_3638_);
lean_dec_ref(v___f_3637_);
lean_dec(v_body_3636_);
lean_dec_ref(v_close_3635_);
v_a_3641_ = lean_ctor_get(v_x_3639_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_x_3639_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3643_ = v_x_3639_;
v_isShared_3644_ = v_isSharedCheck_3649_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v_x_3639_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3649_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
lean_object* v___x_3647_; 
v___x_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
return v___x_3647_;
}
}
}
else
{
lean_object* v_a_3650_; uint8_t v___x_3651_; 
v_a_3650_ = lean_ctor_get(v_x_3639_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v_x_3639_, 1);
v___x_3651_ = lean_unbox(v_a_3650_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; lean_object* v___x_3655_; 
lean_dec_ref(v___f_3638_);
v___x_3652_ = lean_unsigned_to_nat(0u);
v___x_3653_ = lean_apply_2(v_close_3635_, v_body_3636_, lean_box(0));
v___x_3654_ = lean_unbox(v_a_3650_);
lean_dec(v_a_3650_);
v___x_3655_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3652_, v___x_3654_, v___x_3653_, v___f_3637_);
return v___x_3655_;
}
else
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
lean_dec(v_a_3650_);
lean_dec_ref(v___f_3637_);
lean_dec(v_body_3636_);
lean_dec_ref(v_close_3635_);
v___x_3656_ = lean_box(0);
v___x_3657_ = lean_apply_2(v___f_3638_, v___x_3656_, lean_box(0));
return v___x_3657_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v_close_3658_, lean_object* v_body_3659_, lean_object* v___f_3660_, lean_object* v___f_3661_, lean_object* v_x_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v_close_3658_, v_body_3659_, v___f_3660_, v___f_3661_, v_x_3662_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(uint8_t v___x_3665_, lean_object* v_x_3666_){
_start:
{
if (lean_obj_tag(v_x_3666_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3676_; 
v_a_3668_ = lean_ctor_get(v_x_3666_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v_x_3666_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3670_ = v_x_3666_;
v_isShared_3671_ = v_isSharedCheck_3676_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v_x_3666_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3676_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
lean_object* v___x_3674_; 
v___x_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
return v___x_3674_;
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3696_; 
v_a_3677_ = lean_ctor_get(v_x_3666_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v_x_3666_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3679_ = v_x_3666_;
v_isShared_3680_ = v_isSharedCheck_3696_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v_x_3666_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3696_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v_fst_3681_; lean_object* v_snd_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3695_; 
v_fst_3681_ = lean_ctor_get(v_a_3677_, 0);
v_snd_3682_ = lean_ctor_get(v_a_3677_, 1);
v_isSharedCheck_3695_ = !lean_is_exclusive(v_a_3677_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3684_ = v_a_3677_;
v_isShared_3685_ = v_isSharedCheck_3695_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_snd_3682_);
lean_inc(v_fst_3681_);
lean_dec(v_a_3677_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3695_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; lean_object* v___x_3688_; 
v___x_3686_ = lean_box(v___x_3665_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 1, v___x_3686_);
lean_ctor_set(v___x_3684_, 0, v_snd_3682_);
v___x_3688_ = v___x_3684_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_snd_3682_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3689_, 0, v_fst_3681_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 0, v___x_3689_);
v___x_3691_ = v___x_3679_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3692_; 
v___x_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
return v___x_3692_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v___x_3697_, lean_object* v_x_3698_, lean_object* v___y_3699_){
_start:
{
uint8_t v___x_8503__boxed_3700_; lean_object* v_res_3701_; 
v___x_8503__boxed_3700_ = lean_unbox(v___x_3697_);
v_res_3701_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v___x_8503__boxed_3700_, v_x_3698_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(lean_object* v_requestStream_3702_, lean_object* v_keepAliveTimeout_3703_, lean_object* v_currentTimeout_3704_, lean_object* v_headerTimeout_3705_, lean_object* v_response_3706_, uint8_t v_requiresData_3707_, lean_object* v_expectData_3708_, uint8_t v___x_3709_, lean_object* v_pendingHead_3710_, uint8_t v_requestFinalOffered_3711_, lean_object* v_handlerTask_3712_, lean_object* v_dateSecond_3713_, uint8_t v_peerClosed_3714_, uint8_t v_requestEnded_3715_, lean_object* v_____x_3716_){
_start:
{
lean_object* v_snd_3718_; lean_object* v_fst_3719_; lean_object* v_fst_3720_; lean_object* v_snd_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3731_; 
v_snd_3718_ = lean_ctor_get(v_____x_3716_, 1);
lean_inc(v_snd_3718_);
v_fst_3719_ = lean_ctor_get(v_____x_3716_, 0);
lean_inc(v_fst_3719_);
lean_dec_ref(v_____x_3716_);
v_fst_3720_ = lean_ctor_get(v_snd_3718_, 0);
v_snd_3721_ = lean_ctor_get(v_snd_3718_, 1);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_snd_3718_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3723_ = v_snd_3718_;
v_isShared_3724_ = v_isSharedCheck_3731_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_snd_3721_);
lean_inc(v_fst_3720_);
lean_dec(v_snd_3718_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3731_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3725_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v___x_3725_, 0, v_fst_3719_);
lean_ctor_set(v___x_3725_, 1, v_requestStream_3702_);
lean_ctor_set(v___x_3725_, 2, v_keepAliveTimeout_3703_);
lean_ctor_set(v___x_3725_, 3, v_currentTimeout_3704_);
lean_ctor_set(v___x_3725_, 4, v_headerTimeout_3705_);
lean_ctor_set(v___x_3725_, 5, v_response_3706_);
lean_ctor_set(v___x_3725_, 6, v_fst_3720_);
lean_ctor_set(v___x_3725_, 7, v_expectData_3708_);
lean_ctor_set(v___x_3725_, 8, v_pendingHead_3710_);
lean_ctor_set(v___x_3725_, 9, v_handlerTask_3712_);
lean_ctor_set(v___x_3725_, 10, v_dateSecond_3713_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*11, v_requiresData_3707_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*11 + 1, v___x_3709_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*11 + 2, v_requestFinalOffered_3711_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*11 + 3, v_peerClosed_3714_);
lean_ctor_set_uint8(v___x_3725_, sizeof(void*)*11 + 4, v_requestEnded_3715_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3725_);
v___x_3727_ = v___x_3723_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_snd_3721_);
v___x_3727_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
v___x_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
return v___x_3729_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v_requestStream_3732_, lean_object* v_keepAliveTimeout_3733_, lean_object* v_currentTimeout_3734_, lean_object* v_headerTimeout_3735_, lean_object* v_response_3736_, lean_object* v_requiresData_3737_, lean_object* v_expectData_3738_, lean_object* v___x_3739_, lean_object* v_pendingHead_3740_, lean_object* v_requestFinalOffered_3741_, lean_object* v_handlerTask_3742_, lean_object* v_dateSecond_3743_, lean_object* v_peerClosed_3744_, lean_object* v_requestEnded_3745_, lean_object* v_____x_3746_, lean_object* v___y_3747_){
_start:
{
uint8_t v_requiresData_boxed_3748_; uint8_t v___x_8570__boxed_3749_; uint8_t v_requestFinalOffered_boxed_3750_; uint8_t v_peerClosed_boxed_3751_; uint8_t v_requestEnded_boxed_3752_; lean_object* v_res_3753_; 
v_requiresData_boxed_3748_ = lean_unbox(v_requiresData_3737_);
v___x_8570__boxed_3749_ = lean_unbox(v___x_3739_);
v_requestFinalOffered_boxed_3750_ = lean_unbox(v_requestFinalOffered_3741_);
v_peerClosed_boxed_3751_ = lean_unbox(v_peerClosed_3744_);
v_requestEnded_boxed_3752_ = lean_unbox(v_requestEnded_3745_);
v_res_3753_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v_requestStream_3732_, v_keepAliveTimeout_3733_, v_currentTimeout_3734_, v_headerTimeout_3735_, v_response_3736_, v_requiresData_boxed_3748_, v_expectData_3738_, v___x_8570__boxed_3749_, v_pendingHead_3740_, v_requestFinalOffered_boxed_3750_, v_handlerTask_3742_, v_dateSecond_3743_, v_peerClosed_boxed_3751_, v_requestEnded_boxed_3752_, v_____x_3746_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(lean_object* v___f_3754_, lean_object* v_x_3755_){
_start:
{
if (lean_obj_tag(v_x_3755_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3765_; 
lean_dec_ref(v___f_3754_);
v_a_3757_ = lean_ctor_get(v_x_3755_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v_x_3755_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3759_ = v_x_3755_;
v_isShared_3760_ = v_isSharedCheck_3765_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v_x_3755_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3765_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
return v___x_3763_;
}
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3767_; 
v_a_3766_ = lean_ctor_get(v_x_3755_, 0);
lean_inc(v_a_3766_);
lean_dec_ref_known(v_x_3755_, 1);
v___x_3767_ = lean_apply_2(v___f_3754_, v_a_3766_, lean_box(0));
return v___x_3767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___f_3768_, lean_object* v_x_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___f_3768_, v_x_3769_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(lean_object* v_snd_3772_, uint8_t v___x_3773_, lean_object* v_fst_3774_, lean_object* v_x_3775_){
_start:
{
if (lean_obj_tag(v_x_3775_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3785_; 
lean_dec_ref(v_fst_3774_);
lean_dec(v_snd_3772_);
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
lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3796_; 
v_isSharedCheck_3796_ = !lean_is_exclusive(v_x_3775_);
if (v_isSharedCheck_3796_ == 0)
{
lean_object* v_unused_3797_; 
v_unused_3797_ = lean_ctor_get(v_x_3775_, 0);
lean_dec(v_unused_3797_);
v___x_3787_ = v_x_3775_;
v_isShared_3788_ = v_isSharedCheck_3796_;
goto v_resetjp_3786_;
}
else
{
lean_dec(v_x_3775_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3796_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3793_; 
v___x_3789_ = lean_box(v___x_3773_);
v___x_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3790_, 0, v_snd_3772_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3791_, 0, v_fst_3774_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3791_);
v___x_3793_ = v___x_3787_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3791_);
v___x_3793_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
return v___x_3794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v_snd_3798_, lean_object* v___x_3799_, lean_object* v_fst_3800_, lean_object* v_x_3801_, lean_object* v___y_3802_){
_start:
{
uint8_t v___x_8639__boxed_3803_; lean_object* v_res_3804_; 
v___x_8639__boxed_3803_ = lean_unbox(v___x_3799_);
v_res_3804_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v_snd_3798_, v___x_8639__boxed_3803_, v_fst_3800_, v_x_3801_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object* v_inst_3805_, lean_object* v_handler_3806_, uint8_t v___x_3807_, lean_object* v___f_3808_, lean_object* v_x_3809_){
_start:
{
if (lean_obj_tag(v_x_3809_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v_a_3811_ = lean_ctor_get(v_x_3809_, 0);
lean_inc(v_a_3811_);
lean_dec_ref_known(v_x_3809_, 1);
v___x_3812_ = lean_unsigned_to_nat(0u);
v___x_3813_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_3805_, v_handler_3806_, v_a_3811_);
v___x_3814_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3812_, v___x_3807_, v___x_3813_, v___f_3808_);
return v___x_3814_;
}
else
{
lean_object* v___x_3815_; 
lean_dec_ref(v___f_3808_);
lean_dec(v_handler_3806_);
lean_dec_ref(v_inst_3805_);
v___x_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3815_, 0, v_x_3809_);
return v___x_3815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v_inst_3816_, lean_object* v_handler_3817_, lean_object* v___x_3818_, lean_object* v___f_3819_, lean_object* v_x_3820_, lean_object* v___y_3821_){
_start:
{
uint8_t v___x_8697__boxed_3822_; lean_object* v_res_3823_; 
v___x_8697__boxed_3822_ = lean_unbox(v___x_3818_);
v_res_3823_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_inst_3816_, v_handler_3817_, v___x_8697__boxed_3822_, v___f_3819_, v_x_3820_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(uint8_t v___x_3824_, lean_object* v___f_3825_, uint8_t v___x_3826_, lean_object* v_inst_3827_, lean_object* v_handler_3828_, lean_object* v_inst_3829_, lean_object* v___f_3830_, lean_object* v___f_3831_, lean_object* v_x_3832_){
_start:
{
if (lean_obj_tag(v_x_3832_) == 0)
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3842_; 
lean_dec_ref(v___f_3831_);
lean_dec_ref(v___f_3830_);
lean_dec_ref(v_inst_3829_);
lean_dec(v_handler_3828_);
lean_dec_ref(v_inst_3827_);
lean_dec_ref(v___f_3825_);
v_a_3834_ = lean_ctor_get(v_x_3832_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_x_3832_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3836_ = v_x_3832_;
v_isShared_3837_ = v_isSharedCheck_3842_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v_x_3832_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3842_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3840_; 
v___x_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
return v___x_3840_;
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3876_; 
v_a_3843_ = lean_ctor_get(v_x_3832_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v_x_3832_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3845_ = v_x_3832_;
v_isShared_3846_ = v_isSharedCheck_3876_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v_x_3832_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3876_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v_snd_3847_; 
v_snd_3847_ = lean_ctor_get(v_a_3843_, 1);
lean_inc(v_snd_3847_);
if (lean_obj_tag(v_snd_3847_) == 0)
{
lean_object* v_fst_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3863_; 
lean_dec_ref(v___f_3831_);
lean_dec_ref(v___f_3830_);
lean_dec_ref(v_inst_3829_);
lean_dec(v_handler_3828_);
lean_dec_ref(v_inst_3827_);
v_fst_3848_ = lean_ctor_get(v_a_3843_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_a_3843_);
if (v_isSharedCheck_3863_ == 0)
{
lean_object* v_unused_3864_; 
v_unused_3864_ = lean_ctor_get(v_a_3843_, 1);
lean_dec(v_unused_3864_);
v___x_3850_ = v_a_3843_;
v_isShared_3851_ = v_isSharedCheck_3863_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_fst_3848_);
lean_dec(v_a_3843_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3863_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3852_ = lean_box(v___x_3824_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 1, v___x_3852_);
lean_ctor_set(v___x_3850_, 0, v_snd_3847_);
v___x_3854_ = v___x_3850_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_snd_3847_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v___x_3852_);
v___x_3854_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3855_, 0, v_fst_3848_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
v___x_3856_ = lean_unsigned_to_nat(0u);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3855_);
v___x_3858_ = v___x_3845_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3855_);
v___x_3858_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3858_);
v___x_3860_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3856_, v___x_3824_, v___x_3859_, v___f_3825_);
return v___x_3860_;
}
}
}
}
else
{
lean_object* v_fst_3865_; lean_object* v_val_3866_; lean_object* v___x_3867_; lean_object* v___f_3868_; lean_object* v___x_3869_; lean_object* v___f_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
lean_del_object(v___x_3845_);
lean_dec_ref(v___f_3825_);
v_fst_3865_ = lean_ctor_get(v_a_3843_, 0);
lean_inc_n(v_fst_3865_, 2);
lean_dec(v_a_3843_);
v_val_3866_ = lean_ctor_get(v_snd_3847_, 0);
lean_inc(v_val_3866_);
v___x_3867_ = lean_box(v___x_3826_);
v___f_3868_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 5, 3);
lean_closure_set(v___f_3868_, 0, v_snd_3847_);
lean_closure_set(v___f_3868_, 1, v___x_3867_);
lean_closure_set(v___f_3868_, 2, v_fst_3865_);
v___x_3869_ = lean_box(v___x_3824_);
v___f_3870_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 6, 4);
lean_closure_set(v___f_3870_, 0, v_inst_3827_);
lean_closure_set(v___f_3870_, 1, v_handler_3828_);
lean_closure_set(v___f_3870_, 2, v___x_3869_);
lean_closure_set(v___f_3870_, 3, v___f_3868_);
v___x_3871_ = lean_unsigned_to_nat(0u);
v___x_3872_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3829_, v_fst_3865_, v_val_3866_);
v___x_3873_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3871_, v___x_3824_, v___x_3872_, v___f_3830_);
v___x_3874_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3871_, v___x_3824_, v___x_3873_, v___f_3870_);
v___x_3875_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3871_, v___x_3824_, v___x_3874_, v___f_3831_);
return v___x_3875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v___x_3877_, lean_object* v___f_3878_, lean_object* v___x_3879_, lean_object* v_inst_3880_, lean_object* v_handler_3881_, lean_object* v_inst_3882_, lean_object* v___f_3883_, lean_object* v___f_3884_, lean_object* v_x_3885_, lean_object* v___y_3886_){
_start:
{
uint8_t v___x_8722__boxed_3887_; uint8_t v___x_8724__boxed_3888_; lean_object* v_res_3889_; 
v___x_8722__boxed_3887_ = lean_unbox(v___x_3877_);
v___x_8724__boxed_3888_ = lean_unbox(v___x_3879_);
v_res_3889_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v___x_8722__boxed_3887_, v___f_3878_, v___x_8724__boxed_3888_, v_inst_3880_, v_handler_3881_, v_inst_3882_, v___f_3883_, v___f_3884_, v_x_3885_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19(uint8_t v___x_3890_, uint8_t v___x_3891_, lean_object* v_inst_3892_, lean_object* v_handler_3893_, lean_object* v_inst_3894_, lean_object* v___f_3895_, lean_object* v_a_3896_, lean_object* v_x_3897_){
_start:
{
if (lean_obj_tag(v_x_3897_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3907_; 
lean_dec_ref(v_a_3896_);
lean_dec_ref(v___f_3895_);
lean_dec_ref(v_inst_3894_);
lean_dec(v_handler_3893_);
lean_dec_ref(v_inst_3892_);
v_a_3899_ = lean_ctor_get(v_x_3897_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v_x_3897_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3901_ = v_x_3897_;
v_isShared_3902_ = v_isSharedCheck_3907_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v_x_3897_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3907_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3905_; 
v___x_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
return v___x_3905_;
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v_machine_3909_; lean_object* v_requestStream_3910_; lean_object* v_keepAliveTimeout_3911_; lean_object* v_currentTimeout_3912_; lean_object* v_headerTimeout_3913_; lean_object* v_response_3914_; uint8_t v_requiresData_3915_; lean_object* v_expectData_3916_; lean_object* v_pendingHead_3917_; uint8_t v_requestFinalOffered_3918_; lean_object* v_handlerTask_3919_; lean_object* v_dateSecond_3920_; uint8_t v_peerClosed_3921_; uint8_t v_requestEnded_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___f_3928_; lean_object* v___f_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___f_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v_a_3908_ = lean_ctor_get(v_x_3897_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v_x_3897_, 1);
v_machine_3909_ = lean_ctor_get(v_a_3908_, 0);
lean_inc_ref(v_machine_3909_);
v_requestStream_3910_ = lean_ctor_get(v_a_3908_, 1);
lean_inc_ref(v_requestStream_3910_);
v_keepAliveTimeout_3911_ = lean_ctor_get(v_a_3908_, 2);
lean_inc(v_keepAliveTimeout_3911_);
v_currentTimeout_3912_ = lean_ctor_get(v_a_3908_, 3);
lean_inc(v_currentTimeout_3912_);
v_headerTimeout_3913_ = lean_ctor_get(v_a_3908_, 4);
lean_inc(v_headerTimeout_3913_);
v_response_3914_ = lean_ctor_get(v_a_3908_, 5);
lean_inc_ref(v_response_3914_);
v_requiresData_3915_ = lean_ctor_get_uint8(v_a_3908_, sizeof(void*)*11);
v_expectData_3916_ = lean_ctor_get(v_a_3908_, 7);
lean_inc(v_expectData_3916_);
v_pendingHead_3917_ = lean_ctor_get(v_a_3908_, 8);
lean_inc(v_pendingHead_3917_);
v_requestFinalOffered_3918_ = lean_ctor_get_uint8(v_a_3908_, sizeof(void*)*11 + 2);
v_handlerTask_3919_ = lean_ctor_get(v_a_3908_, 9);
lean_inc(v_handlerTask_3919_);
v_dateSecond_3920_ = lean_ctor_get(v_a_3908_, 10);
lean_inc(v_dateSecond_3920_);
v_peerClosed_3921_ = lean_ctor_get_uint8(v_a_3908_, sizeof(void*)*11 + 3);
v_requestEnded_3922_ = lean_ctor_get_uint8(v_a_3908_, sizeof(void*)*11 + 4);
lean_dec(v_a_3908_);
v___x_3923_ = lean_box(v_requiresData_3915_);
v___x_3924_ = lean_box(v___x_3890_);
v___x_3925_ = lean_box(v_requestFinalOffered_3918_);
v___x_3926_ = lean_box(v_peerClosed_3921_);
v___x_3927_ = lean_box(v_requestEnded_3922_);
v___f_3928_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 16, 14);
lean_closure_set(v___f_3928_, 0, v_requestStream_3910_);
lean_closure_set(v___f_3928_, 1, v_keepAliveTimeout_3911_);
lean_closure_set(v___f_3928_, 2, v_currentTimeout_3912_);
lean_closure_set(v___f_3928_, 3, v_headerTimeout_3913_);
lean_closure_set(v___f_3928_, 4, v_response_3914_);
lean_closure_set(v___f_3928_, 5, v___x_3923_);
lean_closure_set(v___f_3928_, 6, v_expectData_3916_);
lean_closure_set(v___f_3928_, 7, v___x_3924_);
lean_closure_set(v___f_3928_, 8, v_pendingHead_3917_);
lean_closure_set(v___f_3928_, 9, v___x_3925_);
lean_closure_set(v___f_3928_, 10, v_handlerTask_3919_);
lean_closure_set(v___f_3928_, 11, v_dateSecond_3920_);
lean_closure_set(v___f_3928_, 12, v___x_3926_);
lean_closure_set(v___f_3928_, 13, v___x_3927_);
v___f_3929_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed), 3, 1);
lean_closure_set(v___f_3929_, 0, v___f_3928_);
v___x_3930_ = lean_box(v___x_3890_);
v___x_3931_ = lean_box(v___x_3891_);
lean_inc_ref(v_inst_3894_);
lean_inc_ref(v___f_3929_);
v___f_3932_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 10, 8);
lean_closure_set(v___f_3932_, 0, v___x_3930_);
lean_closure_set(v___f_3932_, 1, v___f_3929_);
lean_closure_set(v___f_3932_, 2, v___x_3931_);
lean_closure_set(v___f_3932_, 3, v_inst_3892_);
lean_closure_set(v___f_3932_, 4, v_handler_3893_);
lean_closure_set(v___f_3932_, 5, v_inst_3894_);
lean_closure_set(v___f_3932_, 6, v___f_3895_);
lean_closure_set(v___f_3932_, 7, v___f_3929_);
v___x_3933_ = lean_unsigned_to_nat(0u);
v___x_3934_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3894_, v_machine_3909_, v_a_3896_);
v___x_3935_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3933_, v___x_3890_, v___x_3934_, v___f_3932_);
return v___x_3935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19___boxed(lean_object* v___x_3936_, lean_object* v___x_3937_, lean_object* v_inst_3938_, lean_object* v_handler_3939_, lean_object* v_inst_3940_, lean_object* v___f_3941_, lean_object* v_a_3942_, lean_object* v_x_3943_, lean_object* v___y_3944_){
_start:
{
uint8_t v___x_8835__boxed_3945_; uint8_t v___x_8836__boxed_3946_; lean_object* v_res_3947_; 
v___x_8835__boxed_3945_ = lean_unbox(v___x_3936_);
v___x_8836__boxed_3946_ = lean_unbox(v___x_3937_);
v_res_3947_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19(v___x_8835__boxed_3945_, v___x_8836__boxed_3946_, v_inst_3938_, v_handler_3939_, v_inst_3940_, v___f_3941_, v_a_3942_, v_x_3943_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20(lean_object* v_state_3948_, lean_object* v_x_3949_){
_start:
{
if (lean_obj_tag(v_x_3949_) == 0)
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3959_; 
lean_dec_ref(v_state_3948_);
v_a_3951_ = lean_ctor_get(v_x_3949_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v_x_3949_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3953_ = v_x_3949_;
v_isShared_3954_ = v_isSharedCheck_3959_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v_x_3949_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3959_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
lean_object* v___x_3957_; 
v___x_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3956_);
return v___x_3957_;
}
}
}
else
{
lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3994_; 
v_isSharedCheck_3994_ = !lean_is_exclusive(v_x_3949_);
if (v_isSharedCheck_3994_ == 0)
{
lean_object* v_unused_3995_; 
v_unused_3995_ = lean_ctor_get(v_x_3949_, 0);
lean_dec(v_unused_3995_);
v___x_3961_ = v_x_3949_;
v_isShared_3962_ = v_isSharedCheck_3994_;
goto v_resetjp_3960_;
}
else
{
lean_dec(v_x_3949_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3994_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v_machine_3963_; lean_object* v_requestStream_3964_; lean_object* v_keepAliveTimeout_3965_; lean_object* v_currentTimeout_3966_; lean_object* v_headerTimeout_3967_; lean_object* v_response_3968_; lean_object* v_respStream_3969_; uint8_t v_requiresData_3970_; lean_object* v_expectData_3971_; lean_object* v_pendingHead_3972_; uint8_t v_requestFinalOffered_3973_; lean_object* v_handlerTask_3974_; lean_object* v_dateSecond_3975_; uint8_t v_peerClosed_3976_; uint8_t v_requestEnded_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3993_; 
v_machine_3963_ = lean_ctor_get(v_state_3948_, 0);
v_requestStream_3964_ = lean_ctor_get(v_state_3948_, 1);
v_keepAliveTimeout_3965_ = lean_ctor_get(v_state_3948_, 2);
v_currentTimeout_3966_ = lean_ctor_get(v_state_3948_, 3);
v_headerTimeout_3967_ = lean_ctor_get(v_state_3948_, 4);
v_response_3968_ = lean_ctor_get(v_state_3948_, 5);
v_respStream_3969_ = lean_ctor_get(v_state_3948_, 6);
v_requiresData_3970_ = lean_ctor_get_uint8(v_state_3948_, sizeof(void*)*11);
v_expectData_3971_ = lean_ctor_get(v_state_3948_, 7);
v_pendingHead_3972_ = lean_ctor_get(v_state_3948_, 8);
v_requestFinalOffered_3973_ = lean_ctor_get_uint8(v_state_3948_, sizeof(void*)*11 + 2);
v_handlerTask_3974_ = lean_ctor_get(v_state_3948_, 9);
v_dateSecond_3975_ = lean_ctor_get(v_state_3948_, 10);
v_peerClosed_3976_ = lean_ctor_get_uint8(v_state_3948_, sizeof(void*)*11 + 3);
v_requestEnded_3977_ = lean_ctor_get_uint8(v_state_3948_, sizeof(void*)*11 + 4);
v_isSharedCheck_3993_ = !lean_is_exclusive(v_state_3948_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3979_ = v_state_3948_;
v_isShared_3980_ = v_isSharedCheck_3993_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_dateSecond_3975_);
lean_inc(v_handlerTask_3974_);
lean_inc(v_pendingHead_3972_);
lean_inc(v_expectData_3971_);
lean_inc(v_respStream_3969_);
lean_inc(v_response_3968_);
lean_inc(v_headerTimeout_3967_);
lean_inc(v_currentTimeout_3966_);
lean_inc(v_keepAliveTimeout_3965_);
lean_inc(v_requestStream_3964_);
lean_inc(v_machine_3963_);
lean_dec(v_state_3948_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3993_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; lean_object* v___x_3985_; 
v___x_3981_ = lean_box(31);
v___x_3982_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3963_, v___x_3981_);
v___x_3983_ = 0;
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 0, v___x_3982_);
v___x_3985_ = v___x_3979_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3982_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v_requestStream_3964_);
lean_ctor_set(v_reuseFailAlloc_3992_, 2, v_keepAliveTimeout_3965_);
lean_ctor_set(v_reuseFailAlloc_3992_, 3, v_currentTimeout_3966_);
lean_ctor_set(v_reuseFailAlloc_3992_, 4, v_headerTimeout_3967_);
lean_ctor_set(v_reuseFailAlloc_3992_, 5, v_response_3968_);
lean_ctor_set(v_reuseFailAlloc_3992_, 6, v_respStream_3969_);
lean_ctor_set(v_reuseFailAlloc_3992_, 7, v_expectData_3971_);
lean_ctor_set(v_reuseFailAlloc_3992_, 8, v_pendingHead_3972_);
lean_ctor_set(v_reuseFailAlloc_3992_, 9, v_handlerTask_3974_);
lean_ctor_set(v_reuseFailAlloc_3992_, 10, v_dateSecond_3975_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, sizeof(void*)*11, v_requiresData_3970_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, sizeof(void*)*11 + 2, v_requestFinalOffered_3973_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, sizeof(void*)*11 + 3, v_peerClosed_3976_);
lean_ctor_set_uint8(v_reuseFailAlloc_3992_, sizeof(void*)*11 + 4, v_requestEnded_3977_);
v___x_3985_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3989_; 
lean_ctor_set_uint8(v___x_3985_, sizeof(void*)*11 + 1, v___x_3983_);
v___x_3986_ = lean_box(v___x_3983_);
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3985_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 0, v___x_3987_);
v___x_3989_ = v___x_3961_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3987_);
v___x_3989_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
lean_object* v___x_3990_; 
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
return v___x_3990_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20___boxed(lean_object* v_state_3996_, lean_object* v_x_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20(v_state_3996_, v_x_3997_);
return v_res_3999_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__4(void){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__3));
v___x_4008_ = lean_mk_io_user_error(v___x_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_4009_, lean_object* v_inst_4010_, lean_object* v_handler_4011_, lean_object* v_config_4012_, lean_object* v_event_4013_, lean_object* v_state_4014_){
_start:
{
switch(lean_obj_tag(v_event_4013_))
{
case 0:
{
lean_object* v_x_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4140_; 
lean_dec(v_handler_4011_);
lean_dec_ref(v_inst_4010_);
lean_dec_ref(v_inst_4009_);
v_x_4022_ = lean_ctor_get(v_event_4013_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v_event_4013_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4024_ = v_event_4013_;
v_isShared_4025_ = v_isSharedCheck_4140_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_x_4022_);
lean_dec(v_event_4013_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4140_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
if (lean_obj_tag(v_x_4022_) == 0)
{
lean_object* v_machine_4026_; lean_object* v_reader_4027_; lean_object* v_requestStream_4028_; lean_object* v_keepAliveTimeout_4029_; lean_object* v_currentTimeout_4030_; lean_object* v_headerTimeout_4031_; lean_object* v_response_4032_; lean_object* v_respStream_4033_; uint8_t v_requiresData_4034_; lean_object* v_expectData_4035_; uint8_t v_handlerDispatched_4036_; lean_object* v_pendingHead_4037_; uint8_t v_requestFinalOffered_4038_; lean_object* v_handlerTask_4039_; lean_object* v_dateSecond_4040_; uint8_t v_requestEnded_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4083_; 
lean_dec_ref(v_config_4012_);
v_machine_4026_ = lean_ctor_get(v_state_4014_, 0);
lean_inc_ref(v_machine_4026_);
v_reader_4027_ = lean_ctor_get(v_machine_4026_, 0);
lean_inc_ref(v_reader_4027_);
v_requestStream_4028_ = lean_ctor_get(v_state_4014_, 1);
v_keepAliveTimeout_4029_ = lean_ctor_get(v_state_4014_, 2);
v_currentTimeout_4030_ = lean_ctor_get(v_state_4014_, 3);
v_headerTimeout_4031_ = lean_ctor_get(v_state_4014_, 4);
v_response_4032_ = lean_ctor_get(v_state_4014_, 5);
v_respStream_4033_ = lean_ctor_get(v_state_4014_, 6);
v_requiresData_4034_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11);
v_expectData_4035_ = lean_ctor_get(v_state_4014_, 7);
v_handlerDispatched_4036_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 1);
v_pendingHead_4037_ = lean_ctor_get(v_state_4014_, 8);
v_requestFinalOffered_4038_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 2);
v_handlerTask_4039_ = lean_ctor_get(v_state_4014_, 9);
v_dateSecond_4040_ = lean_ctor_get(v_state_4014_, 10);
v_requestEnded_4041_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 4);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_state_4014_);
if (v_isSharedCheck_4083_ == 0)
{
lean_object* v_unused_4084_; 
v_unused_4084_ = lean_ctor_get(v_state_4014_, 0);
lean_dec(v_unused_4084_);
v___x_4043_ = v_state_4014_;
v_isShared_4044_ = v_isSharedCheck_4083_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_dateSecond_4040_);
lean_inc(v_handlerTask_4039_);
lean_inc(v_pendingHead_4037_);
lean_inc(v_expectData_4035_);
lean_inc(v_respStream_4033_);
lean_inc(v_response_4032_);
lean_inc(v_headerTimeout_4031_);
lean_inc(v_currentTimeout_4030_);
lean_inc(v_keepAliveTimeout_4029_);
lean_inc(v_requestStream_4028_);
lean_dec(v_state_4014_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4083_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v_writer_4045_; lean_object* v_config_4046_; lean_object* v_events_4047_; lean_object* v_error_4048_; lean_object* v_date_4049_; uint8_t v_keepAlive_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4081_; 
v_writer_4045_ = lean_ctor_get(v_machine_4026_, 1);
v_config_4046_ = lean_ctor_get(v_machine_4026_, 2);
v_events_4047_ = lean_ctor_get(v_machine_4026_, 3);
v_error_4048_ = lean_ctor_get(v_machine_4026_, 4);
v_date_4049_ = lean_ctor_get(v_machine_4026_, 5);
v_keepAlive_4050_ = lean_ctor_get_uint8(v_machine_4026_, sizeof(void*)*6);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_machine_4026_);
if (v_isSharedCheck_4081_ == 0)
{
lean_object* v_unused_4082_; 
v_unused_4082_ = lean_ctor_get(v_machine_4026_, 0);
lean_dec(v_unused_4082_);
v___x_4052_ = v_machine_4026_;
v_isShared_4053_ = v_isSharedCheck_4081_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_date_4049_);
lean_inc(v_error_4048_);
lean_inc(v_events_4047_);
lean_inc(v_config_4046_);
lean_inc(v_writer_4045_);
lean_dec(v_machine_4026_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4081_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v_state_4054_; lean_object* v_input_4055_; lean_object* v_messageHead_4056_; lean_object* v_messageCount_4057_; lean_object* v_bodyBytesRead_4058_; lean_object* v_headerBytesRead_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4080_; 
v_state_4054_ = lean_ctor_get(v_reader_4027_, 0);
v_input_4055_ = lean_ctor_get(v_reader_4027_, 1);
v_messageHead_4056_ = lean_ctor_get(v_reader_4027_, 2);
v_messageCount_4057_ = lean_ctor_get(v_reader_4027_, 3);
v_bodyBytesRead_4058_ = lean_ctor_get(v_reader_4027_, 4);
v_headerBytesRead_4059_ = lean_ctor_get(v_reader_4027_, 5);
v_isSharedCheck_4080_ = !lean_is_exclusive(v_reader_4027_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4061_ = v_reader_4027_;
v_isShared_4062_ = v_isSharedCheck_4080_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_headerBytesRead_4059_);
lean_inc(v_bodyBytesRead_4058_);
lean_inc(v_messageCount_4057_);
lean_inc(v_messageHead_4056_);
lean_inc(v_input_4055_);
lean_inc(v_state_4054_);
lean_dec(v_reader_4027_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4080_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
uint8_t v___x_4063_; lean_object* v___x_4065_; 
v___x_4063_ = 1;
if (v_isShared_4062_ == 0)
{
v___x_4065_ = v___x_4061_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_state_4054_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_input_4055_);
lean_ctor_set(v_reuseFailAlloc_4079_, 2, v_messageHead_4056_);
lean_ctor_set(v_reuseFailAlloc_4079_, 3, v_messageCount_4057_);
lean_ctor_set(v_reuseFailAlloc_4079_, 4, v_bodyBytesRead_4058_);
lean_ctor_set(v_reuseFailAlloc_4079_, 5, v_headerBytesRead_4059_);
v___x_4065_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
uint8_t v___x_4066_; lean_object* v___x_4068_; 
lean_ctor_set_uint8(v___x_4065_, sizeof(void*)*6, v___x_4063_);
v___x_4066_ = 0;
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4065_);
v___x_4068_ = v___x_4052_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4065_);
lean_ctor_set(v_reuseFailAlloc_4078_, 1, v_writer_4045_);
lean_ctor_set(v_reuseFailAlloc_4078_, 2, v_config_4046_);
lean_ctor_set(v_reuseFailAlloc_4078_, 3, v_events_4047_);
lean_ctor_set(v_reuseFailAlloc_4078_, 4, v_error_4048_);
lean_ctor_set(v_reuseFailAlloc_4078_, 5, v_date_4049_);
lean_ctor_set_uint8(v_reuseFailAlloc_4078_, sizeof(void*)*6, v_keepAlive_4050_);
v___x_4068_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
lean_object* v___x_4070_; 
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*6 + 1, v___x_4066_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 0, v___x_4068_);
v___x_4070_ = v___x_4043_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4068_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v_requestStream_4028_);
lean_ctor_set(v_reuseFailAlloc_4077_, 2, v_keepAliveTimeout_4029_);
lean_ctor_set(v_reuseFailAlloc_4077_, 3, v_currentTimeout_4030_);
lean_ctor_set(v_reuseFailAlloc_4077_, 4, v_headerTimeout_4031_);
lean_ctor_set(v_reuseFailAlloc_4077_, 5, v_response_4032_);
lean_ctor_set(v_reuseFailAlloc_4077_, 6, v_respStream_4033_);
lean_ctor_set(v_reuseFailAlloc_4077_, 7, v_expectData_4035_);
lean_ctor_set(v_reuseFailAlloc_4077_, 8, v_pendingHead_4037_);
lean_ctor_set(v_reuseFailAlloc_4077_, 9, v_handlerTask_4039_);
lean_ctor_set(v_reuseFailAlloc_4077_, 10, v_dateSecond_4040_);
lean_ctor_set_uint8(v_reuseFailAlloc_4077_, sizeof(void*)*11, v_requiresData_4034_);
lean_ctor_set_uint8(v_reuseFailAlloc_4077_, sizeof(void*)*11 + 1, v_handlerDispatched_4036_);
lean_ctor_set_uint8(v_reuseFailAlloc_4077_, sizeof(void*)*11 + 2, v_requestFinalOffered_4038_);
lean_ctor_set_uint8(v_reuseFailAlloc_4077_, sizeof(void*)*11 + 4, v_requestEnded_4041_);
v___x_4070_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4074_; 
lean_ctor_set_uint8(v___x_4070_, sizeof(void*)*11 + 3, v___x_4063_);
v___x_4071_ = lean_box(v___x_4066_);
v___x_4072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4070_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set_tag(v___x_4024_, 1);
lean_ctor_set(v___x_4024_, 0, v___x_4072_);
v___x_4074_ = v___x_4024_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
return v___x_4075_;
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
lean_object* v_val_4085_; lean_object* v_machine_4086_; lean_object* v_requestStream_4087_; lean_object* v_keepAliveTimeout_4088_; lean_object* v_currentTimeout_4089_; lean_object* v_response_4090_; lean_object* v_respStream_4091_; uint8_t v_requiresData_4092_; lean_object* v_expectData_4093_; uint8_t v_handlerDispatched_4094_; lean_object* v_pendingHead_4095_; uint8_t v_requestFinalOffered_4096_; lean_object* v_handlerTask_4097_; lean_object* v_dateSecond_4098_; uint8_t v_peerClosed_4099_; uint8_t v_requestEnded_4100_; lean_object* v___f_4101_; 
lean_del_object(v___x_4024_);
v_val_4085_ = lean_ctor_get(v_x_4022_, 0);
lean_inc_n(v_val_4085_, 2);
lean_dec_ref_known(v_x_4022_, 1);
v_machine_4086_ = lean_ctor_get(v_state_4014_, 0);
v_requestStream_4087_ = lean_ctor_get(v_state_4014_, 1);
v_keepAliveTimeout_4088_ = lean_ctor_get(v_state_4014_, 2);
lean_inc(v_keepAliveTimeout_4088_);
v_currentTimeout_4089_ = lean_ctor_get(v_state_4014_, 3);
v_response_4090_ = lean_ctor_get(v_state_4014_, 5);
v_respStream_4091_ = lean_ctor_get(v_state_4014_, 6);
v_requiresData_4092_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11);
v_expectData_4093_ = lean_ctor_get(v_state_4014_, 7);
v_handlerDispatched_4094_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 1);
v_pendingHead_4095_ = lean_ctor_get(v_state_4014_, 8);
v_requestFinalOffered_4096_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 2);
v_handlerTask_4097_ = lean_ctor_get(v_state_4014_, 9);
v_dateSecond_4098_ = lean_ctor_get(v_state_4014_, 10);
v_peerClosed_4099_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 3);
v_requestEnded_4100_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 4);
v___f_4101_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4101_, 0, v_val_4085_);
if (lean_obj_tag(v_keepAliveTimeout_4088_) == 0)
{
lean_object* v___x_4102_; lean_object* v___x_4103_; 
lean_dec_ref(v___f_4101_);
lean_dec_ref(v_config_4012_);
v___x_4102_ = lean_box(0);
v___x_4103_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_4085_, v___x_4102_, v_state_4014_);
return v___x_4103_;
}
else
{
lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4138_; 
lean_inc(v_dateSecond_4098_);
lean_inc(v_handlerTask_4097_);
lean_inc(v_pendingHead_4095_);
lean_inc(v_expectData_4093_);
lean_inc(v_respStream_4091_);
lean_inc_ref(v_response_4090_);
lean_inc(v_currentTimeout_4089_);
lean_inc_ref(v_requestStream_4087_);
lean_inc_ref(v_machine_4086_);
lean_dec(v_val_4085_);
lean_dec_ref(v_state_4014_);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_keepAliveTimeout_4088_);
if (v_isSharedCheck_4138_ == 0)
{
lean_object* v_unused_4139_; 
v_unused_4139_ = lean_ctor_get(v_keepAliveTimeout_4088_, 0);
lean_dec(v_unused_4139_);
v___x_4105_ = v_keepAliveTimeout_4088_;
v_isShared_4106_ = v_isSharedCheck_4138_;
goto v_resetjp_4104_;
}
else
{
lean_dec(v_keepAliveTimeout_4088_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4138_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___f_4112_; lean_object* v___x_4113_; uint8_t v___x_4114_; lean_object* v_val_4116_; lean_object* v___x_4121_; 
v___x_4107_ = lean_box(v_requiresData_4092_);
v___x_4108_ = lean_box(v_handlerDispatched_4094_);
v___x_4109_ = lean_box(v_requestFinalOffered_4096_);
v___x_4110_ = lean_box(v_peerClosed_4099_);
v___x_4111_ = lean_box(v_requestEnded_4100_);
v___f_4112_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 18, 16);
lean_closure_set(v___f_4112_, 0, v_config_4012_);
lean_closure_set(v___f_4112_, 1, v_machine_4086_);
lean_closure_set(v___f_4112_, 2, v_requestStream_4087_);
lean_closure_set(v___f_4112_, 3, v_currentTimeout_4089_);
lean_closure_set(v___f_4112_, 4, v_response_4090_);
lean_closure_set(v___f_4112_, 5, v_respStream_4091_);
lean_closure_set(v___f_4112_, 6, v___x_4107_);
lean_closure_set(v___f_4112_, 7, v_expectData_4093_);
lean_closure_set(v___f_4112_, 8, v___x_4108_);
lean_closure_set(v___f_4112_, 9, v_pendingHead_4095_);
lean_closure_set(v___f_4112_, 10, v___x_4109_);
lean_closure_set(v___f_4112_, 11, v_handlerTask_4097_);
lean_closure_set(v___f_4112_, 12, v_dateSecond_4098_);
lean_closure_set(v___f_4112_, 13, v___x_4110_);
lean_closure_set(v___f_4112_, 14, v___x_4111_);
lean_closure_set(v___f_4112_, 15, v___f_4101_);
v___x_4113_ = lean_unsigned_to_nat(0u);
v___x_4114_ = 0;
v___x_4121_ = lean_get_current_time();
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4121_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4121_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
lean_ctor_set_tag(v___x_4124_, 1);
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
v_val_4116_ = v___x_4127_;
goto v___jp_4115_;
}
}
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
v_a_4130_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4121_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4121_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
lean_ctor_set_tag(v___x_4132_, 0);
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
v_val_4116_ = v___x_4135_;
goto v___jp_4115_;
}
}
}
v___jp_4115_:
{
lean_object* v___x_4118_; 
if (v_isShared_4106_ == 0)
{
lean_ctor_set_tag(v___x_4105_, 0);
lean_ctor_set(v___x_4105_, 0, v_val_4116_);
v___x_4118_ = v___x_4105_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_val_4116_);
v___x_4118_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
lean_object* v___x_4119_; 
v___x_4119_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4113_, v___x_4114_, v___x_4118_, v___f_4112_);
return v___x_4119_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_x_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4264_; 
lean_dec_ref(v_config_4012_);
lean_dec(v_handler_4011_);
lean_dec_ref(v_inst_4009_);
v_x_4141_ = lean_ctor_get(v_event_4013_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_event_4013_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4143_ = v_event_4013_;
v_isShared_4144_ = v_isSharedCheck_4264_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_x_4141_);
lean_dec(v_event_4013_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4264_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
if (lean_obj_tag(v_x_4141_) == 0)
{
lean_object* v_machine_4145_; lean_object* v_requestStream_4146_; lean_object* v_keepAliveTimeout_4147_; lean_object* v_currentTimeout_4148_; lean_object* v_headerTimeout_4149_; lean_object* v_response_4150_; lean_object* v_respStream_4151_; uint8_t v_requiresData_4152_; lean_object* v_expectData_4153_; uint8_t v_handlerDispatched_4154_; lean_object* v_pendingHead_4155_; uint8_t v_requestFinalOffered_4156_; lean_object* v_handlerTask_4157_; lean_object* v_dateSecond_4158_; uint8_t v_peerClosed_4159_; uint8_t v_requestEnded_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___f_4166_; 
lean_del_object(v___x_4143_);
v_machine_4145_ = lean_ctor_get(v_state_4014_, 0);
lean_inc_ref_n(v_machine_4145_, 2);
v_requestStream_4146_ = lean_ctor_get(v_state_4014_, 1);
lean_inc_ref_n(v_requestStream_4146_, 2);
v_keepAliveTimeout_4147_ = lean_ctor_get(v_state_4014_, 2);
lean_inc_n(v_keepAliveTimeout_4147_, 2);
v_currentTimeout_4148_ = lean_ctor_get(v_state_4014_, 3);
lean_inc_n(v_currentTimeout_4148_, 2);
v_headerTimeout_4149_ = lean_ctor_get(v_state_4014_, 4);
lean_inc_n(v_headerTimeout_4149_, 2);
v_response_4150_ = lean_ctor_get(v_state_4014_, 5);
lean_inc_ref_n(v_response_4150_, 2);
v_respStream_4151_ = lean_ctor_get(v_state_4014_, 6);
lean_inc(v_respStream_4151_);
v_requiresData_4152_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11);
v_expectData_4153_ = lean_ctor_get(v_state_4014_, 7);
lean_inc_n(v_expectData_4153_, 2);
v_handlerDispatched_4154_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 1);
v_pendingHead_4155_ = lean_ctor_get(v_state_4014_, 8);
lean_inc_n(v_pendingHead_4155_, 2);
v_requestFinalOffered_4156_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 2);
v_handlerTask_4157_ = lean_ctor_get(v_state_4014_, 9);
lean_inc_n(v_handlerTask_4157_, 2);
v_dateSecond_4158_ = lean_ctor_get(v_state_4014_, 10);
lean_inc_n(v_dateSecond_4158_, 2);
v_peerClosed_4159_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 3);
v_requestEnded_4160_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 4);
lean_dec_ref(v_state_4014_);
v___x_4161_ = lean_box(v_requiresData_4152_);
v___x_4162_ = lean_box(v_handlerDispatched_4154_);
v___x_4163_ = lean_box(v_requestFinalOffered_4156_);
v___x_4164_ = lean_box(v_peerClosed_4159_);
v___x_4165_ = lean_box(v_requestEnded_4160_);
v___f_4166_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 17, 15);
lean_closure_set(v___f_4166_, 0, v_machine_4145_);
lean_closure_set(v___f_4166_, 1, v_requestStream_4146_);
lean_closure_set(v___f_4166_, 2, v_keepAliveTimeout_4147_);
lean_closure_set(v___f_4166_, 3, v_currentTimeout_4148_);
lean_closure_set(v___f_4166_, 4, v_headerTimeout_4149_);
lean_closure_set(v___f_4166_, 5, v_response_4150_);
lean_closure_set(v___f_4166_, 6, v___x_4161_);
lean_closure_set(v___f_4166_, 7, v_expectData_4153_);
lean_closure_set(v___f_4166_, 8, v___x_4162_);
lean_closure_set(v___f_4166_, 9, v_pendingHead_4155_);
lean_closure_set(v___f_4166_, 10, v___x_4163_);
lean_closure_set(v___f_4166_, 11, v_handlerTask_4157_);
lean_closure_set(v___f_4166_, 12, v_dateSecond_4158_);
lean_closure_set(v___f_4166_, 13, v___x_4164_);
lean_closure_set(v___f_4166_, 14, v___x_4165_);
if (lean_obj_tag(v_respStream_4151_) == 1)
{
lean_object* v_val_4167_; lean_object* v_close_4168_; lean_object* v_isClosed_4169_; lean_object* v___f_4170_; lean_object* v___f_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
lean_dec(v_dateSecond_4158_);
lean_dec(v_handlerTask_4157_);
lean_dec(v_pendingHead_4155_);
lean_dec(v_expectData_4153_);
lean_dec_ref(v_response_4150_);
lean_dec(v_headerTimeout_4149_);
lean_dec(v_currentTimeout_4148_);
lean_dec(v_keepAliveTimeout_4147_);
lean_dec_ref(v_requestStream_4146_);
lean_dec_ref(v_machine_4145_);
v_val_4167_ = lean_ctor_get(v_respStream_4151_, 0);
lean_inc_n(v_val_4167_, 2);
lean_dec_ref_known(v_respStream_4151_, 1);
v_close_4168_ = lean_ctor_get(v_inst_4010_, 1);
lean_inc_ref(v_close_4168_);
v_isClosed_4169_ = lean_ctor_get(v_inst_4010_, 2);
lean_inc_ref(v_isClosed_4169_);
lean_dec_ref(v_inst_4010_);
lean_inc_ref(v___f_4166_);
v___f_4170_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4170_, 0, v___f_4166_);
v___f_4171_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_4171_, 0, v_close_4168_);
lean_closure_set(v___f_4171_, 1, v_val_4167_);
lean_closure_set(v___f_4171_, 2, v___f_4170_);
lean_closure_set(v___f_4171_, 3, v___f_4166_);
v___x_4172_ = lean_unsigned_to_nat(0u);
v___x_4173_ = 0;
v___x_4174_ = lean_apply_2(v_isClosed_4169_, v_val_4167_, lean_box(0));
v___x_4175_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4172_, v___x_4173_, v___x_4174_, v___f_4171_);
return v___x_4175_;
}
else
{
lean_object* v___x_4176_; lean_object* v___x_4177_; 
lean_dec_ref(v___f_4166_);
lean_dec(v_respStream_4151_);
lean_dec_ref(v_inst_4010_);
v___x_4176_ = lean_box(0);
v___x_4177_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_4145_, v_requestStream_4146_, v_keepAliveTimeout_4147_, v_currentTimeout_4148_, v_headerTimeout_4149_, v_response_4150_, v_requiresData_4152_, v_expectData_4153_, v_handlerDispatched_4154_, v_pendingHead_4155_, v_requestFinalOffered_4156_, v_handlerTask_4157_, v_dateSecond_4158_, v_peerClosed_4159_, v_requestEnded_4160_, v___x_4176_);
return v___x_4177_;
}
}
else
{
lean_object* v_val_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4263_; 
lean_dec_ref(v_inst_4010_);
v_val_4178_ = lean_ctor_get(v_x_4141_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v_x_4141_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4180_ = v_x_4141_;
v_isShared_4181_ = v_isSharedCheck_4263_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_val_4178_);
lean_dec(v_x_4141_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4263_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v_machine_4182_; lean_object* v_requestStream_4183_; lean_object* v_keepAliveTimeout_4184_; lean_object* v_currentTimeout_4185_; lean_object* v_headerTimeout_4186_; lean_object* v_response_4187_; lean_object* v_respStream_4188_; uint8_t v_requiresData_4189_; lean_object* v_expectData_4190_; uint8_t v_handlerDispatched_4191_; lean_object* v_pendingHead_4192_; uint8_t v_requestFinalOffered_4193_; lean_object* v_handlerTask_4194_; lean_object* v_dateSecond_4195_; uint8_t v_peerClosed_4196_; uint8_t v_requestEnded_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4262_; 
v_machine_4182_ = lean_ctor_get(v_state_4014_, 0);
v_requestStream_4183_ = lean_ctor_get(v_state_4014_, 1);
v_keepAliveTimeout_4184_ = lean_ctor_get(v_state_4014_, 2);
v_currentTimeout_4185_ = lean_ctor_get(v_state_4014_, 3);
v_headerTimeout_4186_ = lean_ctor_get(v_state_4014_, 4);
v_response_4187_ = lean_ctor_get(v_state_4014_, 5);
v_respStream_4188_ = lean_ctor_get(v_state_4014_, 6);
v_requiresData_4189_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11);
v_expectData_4190_ = lean_ctor_get(v_state_4014_, 7);
v_handlerDispatched_4191_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 1);
v_pendingHead_4192_ = lean_ctor_get(v_state_4014_, 8);
v_requestFinalOffered_4193_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 2);
v_handlerTask_4194_ = lean_ctor_get(v_state_4014_, 9);
v_dateSecond_4195_ = lean_ctor_get(v_state_4014_, 10);
v_peerClosed_4196_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 3);
v_requestEnded_4197_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 4);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_state_4014_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4199_ = v_state_4014_;
v_isShared_4200_ = v_isSharedCheck_4262_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_dateSecond_4195_);
lean_inc(v_handlerTask_4194_);
lean_inc(v_pendingHead_4192_);
lean_inc(v_expectData_4190_);
lean_inc(v_respStream_4188_);
lean_inc(v_response_4187_);
lean_inc(v_headerTimeout_4186_);
lean_inc(v_currentTimeout_4185_);
lean_inc(v_keepAliveTimeout_4184_);
lean_inc(v_requestStream_4183_);
lean_inc(v_machine_4182_);
lean_dec(v_state_4014_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4262_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___y_4202_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4215_ = lean_unsigned_to_nat(1u);
v___x_4216_ = lean_mk_empty_array_with_capacity(v___x_4215_);
v___x_4217_ = lean_array_push(v___x_4216_, v_val_4178_);
v___x_4218_ = lean_array_get_size(v___x_4217_);
v___x_4219_ = lean_unsigned_to_nat(0u);
v___x_4220_ = lean_nat_dec_eq(v___x_4218_, v___x_4219_);
if (v___x_4220_ == 0)
{
lean_object* v_reader_4221_; lean_object* v_writer_4222_; lean_object* v_config_4223_; lean_object* v_events_4224_; lean_object* v_error_4225_; lean_object* v_date_4226_; uint8_t v_keepAlive_4227_; uint8_t v_pullBodyStalled_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4261_; 
v_reader_4221_ = lean_ctor_get(v_machine_4182_, 0);
v_writer_4222_ = lean_ctor_get(v_machine_4182_, 1);
v_config_4223_ = lean_ctor_get(v_machine_4182_, 2);
v_events_4224_ = lean_ctor_get(v_machine_4182_, 3);
v_error_4225_ = lean_ctor_get(v_machine_4182_, 4);
v_date_4226_ = lean_ctor_get(v_machine_4182_, 5);
v_keepAlive_4227_ = lean_ctor_get_uint8(v_machine_4182_, sizeof(void*)*6);
v_pullBodyStalled_4228_ = lean_ctor_get_uint8(v_machine_4182_, sizeof(void*)*6 + 1);
v_isSharedCheck_4261_ = !lean_is_exclusive(v_machine_4182_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4230_ = v_machine_4182_;
v_isShared_4231_ = v_isSharedCheck_4261_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_date_4226_);
lean_inc(v_error_4225_);
lean_inc(v_events_4224_);
lean_inc(v_config_4223_);
lean_inc(v_writer_4222_);
lean_inc(v_reader_4221_);
lean_dec(v_machine_4182_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4261_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___y_4233_; lean_object* v___x_4255_; uint8_t v___x_4256_; 
v___x_4255_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_4256_ = lean_nat_dec_lt(v___x_4219_, v___x_4218_);
if (v___x_4256_ == 0)
{
v___y_4233_ = v___x_4219_;
goto v___jp_4232_;
}
else
{
lean_object* v___f_4257_; size_t v___x_4258_; size_t v___x_4259_; lean_object* v___x_4260_; 
v___f_4257_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_4258_ = ((size_t)0ULL);
v___x_4259_ = lean_usize_of_nat(v___x_4218_);
lean_inc_ref(v___x_4217_);
v___x_4260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4255_, v___f_4257_, v___x_4217_, v___x_4258_, v___x_4259_, v___x_4219_);
v___y_4233_ = v___x_4260_;
goto v___jp_4232_;
}
v___jp_4232_:
{
lean_object* v_userData_4234_; lean_object* v_outputData_4235_; lean_object* v_state_4236_; lean_object* v_knownSize_4237_; lean_object* v_messageHead_4238_; uint8_t v_sentMessage_4239_; uint8_t v_userClosedBody_4240_; uint8_t v_omitBody_4241_; lean_object* v_userDataBytes_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4254_; 
v_userData_4234_ = lean_ctor_get(v_writer_4222_, 0);
v_outputData_4235_ = lean_ctor_get(v_writer_4222_, 1);
v_state_4236_ = lean_ctor_get(v_writer_4222_, 2);
v_knownSize_4237_ = lean_ctor_get(v_writer_4222_, 3);
v_messageHead_4238_ = lean_ctor_get(v_writer_4222_, 4);
v_sentMessage_4239_ = lean_ctor_get_uint8(v_writer_4222_, sizeof(void*)*6);
v_userClosedBody_4240_ = lean_ctor_get_uint8(v_writer_4222_, sizeof(void*)*6 + 1);
v_omitBody_4241_ = lean_ctor_get_uint8(v_writer_4222_, sizeof(void*)*6 + 2);
v_userDataBytes_4242_ = lean_ctor_get(v_writer_4222_, 5);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_writer_4222_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4244_ = v_writer_4222_;
v_isShared_4245_ = v_isSharedCheck_4254_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_userDataBytes_4242_);
lean_inc(v_messageHead_4238_);
lean_inc(v_knownSize_4237_);
lean_inc(v_state_4236_);
lean_inc(v_outputData_4235_);
lean_inc(v_userData_4234_);
lean_dec(v_writer_4222_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4254_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4249_; 
v___x_4246_ = l_Array_append___redArg(v_userData_4234_, v___x_4217_);
lean_dec_ref(v___x_4217_);
v___x_4247_ = lean_nat_add(v_userDataBytes_4242_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec(v_userDataBytes_4242_);
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 5, v___x_4247_);
lean_ctor_set(v___x_4244_, 0, v___x_4246_);
v___x_4249_ = v___x_4244_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4246_);
lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_outputData_4235_);
lean_ctor_set(v_reuseFailAlloc_4253_, 2, v_state_4236_);
lean_ctor_set(v_reuseFailAlloc_4253_, 3, v_knownSize_4237_);
lean_ctor_set(v_reuseFailAlloc_4253_, 4, v_messageHead_4238_);
lean_ctor_set(v_reuseFailAlloc_4253_, 5, v___x_4247_);
lean_ctor_set_uint8(v_reuseFailAlloc_4253_, sizeof(void*)*6, v_sentMessage_4239_);
lean_ctor_set_uint8(v_reuseFailAlloc_4253_, sizeof(void*)*6 + 1, v_userClosedBody_4240_);
lean_ctor_set_uint8(v_reuseFailAlloc_4253_, sizeof(void*)*6 + 2, v_omitBody_4241_);
v___x_4249_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v___x_4251_; 
if (v_isShared_4231_ == 0)
{
lean_ctor_set(v___x_4230_, 1, v___x_4249_);
v___x_4251_ = v___x_4230_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_reader_4221_);
lean_ctor_set(v_reuseFailAlloc_4252_, 1, v___x_4249_);
lean_ctor_set(v_reuseFailAlloc_4252_, 2, v_config_4223_);
lean_ctor_set(v_reuseFailAlloc_4252_, 3, v_events_4224_);
lean_ctor_set(v_reuseFailAlloc_4252_, 4, v_error_4225_);
lean_ctor_set(v_reuseFailAlloc_4252_, 5, v_date_4226_);
lean_ctor_set_uint8(v_reuseFailAlloc_4252_, sizeof(void*)*6, v_keepAlive_4227_);
lean_ctor_set_uint8(v_reuseFailAlloc_4252_, sizeof(void*)*6 + 1, v_pullBodyStalled_4228_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
v___y_4202_ = v___x_4251_;
goto v___jp_4201_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_4217_);
v___y_4202_ = v_machine_4182_;
goto v___jp_4201_;
}
v___jp_4201_:
{
lean_object* v___x_4204_; 
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v___y_4202_);
v___x_4204_ = v___x_4199_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___y_4202_);
lean_ctor_set(v_reuseFailAlloc_4214_, 1, v_requestStream_4183_);
lean_ctor_set(v_reuseFailAlloc_4214_, 2, v_keepAliveTimeout_4184_);
lean_ctor_set(v_reuseFailAlloc_4214_, 3, v_currentTimeout_4185_);
lean_ctor_set(v_reuseFailAlloc_4214_, 4, v_headerTimeout_4186_);
lean_ctor_set(v_reuseFailAlloc_4214_, 5, v_response_4187_);
lean_ctor_set(v_reuseFailAlloc_4214_, 6, v_respStream_4188_);
lean_ctor_set(v_reuseFailAlloc_4214_, 7, v_expectData_4190_);
lean_ctor_set(v_reuseFailAlloc_4214_, 8, v_pendingHead_4192_);
lean_ctor_set(v_reuseFailAlloc_4214_, 9, v_handlerTask_4194_);
lean_ctor_set(v_reuseFailAlloc_4214_, 10, v_dateSecond_4195_);
lean_ctor_set_uint8(v_reuseFailAlloc_4214_, sizeof(void*)*11, v_requiresData_4189_);
lean_ctor_set_uint8(v_reuseFailAlloc_4214_, sizeof(void*)*11 + 1, v_handlerDispatched_4191_);
lean_ctor_set_uint8(v_reuseFailAlloc_4214_, sizeof(void*)*11 + 2, v_requestFinalOffered_4193_);
lean_ctor_set_uint8(v_reuseFailAlloc_4214_, sizeof(void*)*11 + 3, v_peerClosed_4196_);
lean_ctor_set_uint8(v_reuseFailAlloc_4214_, sizeof(void*)*11 + 4, v_requestEnded_4197_);
v___x_4204_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
uint8_t v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4209_; 
v___x_4205_ = 0;
v___x_4206_ = lean_box(v___x_4205_);
v___x_4207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4204_);
lean_ctor_set(v___x_4207_, 1, v___x_4206_);
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 0, v___x_4207_);
v___x_4209_ = v___x_4180_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4207_);
v___x_4209_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
lean_object* v___x_4211_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set_tag(v___x_4143_, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4209_);
v___x_4211_ = v___x_4143_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v___x_4209_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
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
uint8_t v_x_4265_; 
lean_dec_ref(v_config_4012_);
lean_dec_ref(v_inst_4010_);
v_x_4265_ = lean_ctor_get_uint8(v_event_4013_, 0);
lean_dec_ref_known(v_event_4013_, 0);
if (v_x_4265_ == 0)
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
lean_dec(v_handler_4011_);
lean_dec_ref(v_inst_4009_);
v___x_4266_ = lean_box(v_x_4265_);
v___x_4267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4267_, 0, v_state_4014_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4267_);
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
return v___x_4269_;
}
else
{
lean_object* v_machine_4270_; lean_object* v_requestStream_4271_; lean_object* v_keepAliveTimeout_4272_; lean_object* v_currentTimeout_4273_; lean_object* v_headerTimeout_4274_; lean_object* v_response_4275_; lean_object* v_respStream_4276_; uint8_t v_requiresData_4277_; lean_object* v_expectData_4278_; uint8_t v_handlerDispatched_4279_; lean_object* v_pendingHead_4280_; uint8_t v_requestFinalOffered_4281_; lean_object* v_handlerTask_4282_; lean_object* v_dateSecond_4283_; uint8_t v_peerClosed_4284_; uint8_t v_requestEnded_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4349_; 
v_machine_4270_ = lean_ctor_get(v_state_4014_, 0);
v_requestStream_4271_ = lean_ctor_get(v_state_4014_, 1);
v_keepAliveTimeout_4272_ = lean_ctor_get(v_state_4014_, 2);
v_currentTimeout_4273_ = lean_ctor_get(v_state_4014_, 3);
v_headerTimeout_4274_ = lean_ctor_get(v_state_4014_, 4);
v_response_4275_ = lean_ctor_get(v_state_4014_, 5);
v_respStream_4276_ = lean_ctor_get(v_state_4014_, 6);
v_requiresData_4277_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11);
v_expectData_4278_ = lean_ctor_get(v_state_4014_, 7);
v_handlerDispatched_4279_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 1);
v_pendingHead_4280_ = lean_ctor_get(v_state_4014_, 8);
v_requestFinalOffered_4281_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 2);
v_handlerTask_4282_ = lean_ctor_get(v_state_4014_, 9);
v_dateSecond_4283_ = lean_ctor_get(v_state_4014_, 10);
v_peerClosed_4284_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 3);
v_requestEnded_4285_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 4);
v_isSharedCheck_4349_ = !lean_is_exclusive(v_state_4014_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4287_ = v_state_4014_;
v_isShared_4288_ = v_isSharedCheck_4349_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_dateSecond_4283_);
lean_inc(v_handlerTask_4282_);
lean_inc(v_pendingHead_4280_);
lean_inc(v_expectData_4278_);
lean_inc(v_respStream_4276_);
lean_inc(v_response_4275_);
lean_inc(v_headerTimeout_4274_);
lean_inc(v_currentTimeout_4273_);
lean_inc(v_keepAliveTimeout_4272_);
lean_inc(v_requestStream_4271_);
lean_inc(v_machine_4270_);
lean_dec(v_state_4014_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4349_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
uint8_t v___x_4289_; lean_object* v___x_4290_; lean_object* v_fst_4291_; lean_object* v_reader_4292_; lean_object* v_writer_4293_; lean_object* v_snd_4294_; lean_object* v_config_4295_; lean_object* v_events_4296_; lean_object* v_error_4297_; lean_object* v_date_4298_; uint8_t v_keepAlive_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4346_; 
v___x_4289_ = 0;
v___x_4290_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_4289_, v_machine_4270_);
v_fst_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_fst_4291_);
v_reader_4292_ = lean_ctor_get(v_fst_4291_, 0);
lean_inc_ref(v_reader_4292_);
v_writer_4293_ = lean_ctor_get(v_fst_4291_, 1);
lean_inc_ref(v_writer_4293_);
v_snd_4294_ = lean_ctor_get(v___x_4290_, 1);
lean_inc(v_snd_4294_);
lean_dec_ref(v___x_4290_);
v_config_4295_ = lean_ctor_get(v_fst_4291_, 2);
v_events_4296_ = lean_ctor_get(v_fst_4291_, 3);
v_error_4297_ = lean_ctor_get(v_fst_4291_, 4);
v_date_4298_ = lean_ctor_get(v_fst_4291_, 5);
v_keepAlive_4299_ = lean_ctor_get_uint8(v_fst_4291_, sizeof(void*)*6);
v_isSharedCheck_4346_ = !lean_is_exclusive(v_fst_4291_);
if (v_isSharedCheck_4346_ == 0)
{
lean_object* v_unused_4347_; lean_object* v_unused_4348_; 
v_unused_4347_ = lean_ctor_get(v_fst_4291_, 1);
lean_dec(v_unused_4347_);
v_unused_4348_ = lean_ctor_get(v_fst_4291_, 0);
lean_dec(v_unused_4348_);
v___x_4301_ = v_fst_4291_;
v_isShared_4302_ = v_isSharedCheck_4346_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_date_4298_);
lean_inc(v_error_4297_);
lean_inc(v_events_4296_);
lean_inc(v_config_4295_);
lean_dec(v_fst_4291_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4346_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v_state_4303_; lean_object* v_state_4304_; uint8_t v_sentMessage_4305_; lean_object* v___f_4306_; uint8_t v___y_4308_; uint8_t v___y_4337_; 
v_state_4303_ = lean_ctor_get(v_reader_4292_, 0);
v_state_4304_ = lean_ctor_get(v_writer_4293_, 2);
v_sentMessage_4305_ = lean_ctor_get_uint8(v_writer_4293_, sizeof(void*)*6);
v___f_4306_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
switch(lean_obj_tag(v_state_4304_))
{
case 6:
{
v___y_4337_ = v_x_4265_;
goto v___jp_4336_;
}
case 7:
{
v___y_4337_ = v_x_4265_;
goto v___jp_4336_;
}
default: 
{
if (v_sentMessage_4305_ == 0)
{
v___y_4337_ = v_sentMessage_4305_;
goto v___jp_4336_;
}
else
{
if (lean_obj_tag(v_state_4303_) == 2)
{
lean_object* v_a_4340_; 
v_a_4340_ = lean_ctor_get(v_state_4303_, 0);
if (lean_obj_tag(v_a_4340_) == 0)
{
lean_object* v_remaining_4341_; lean_object* v___x_4342_; uint8_t v___x_4343_; 
v_remaining_4341_ = lean_ctor_get(v_a_4340_, 0);
v___x_4342_ = lean_unsigned_to_nat(0u);
v___x_4343_ = lean_nat_dec_eq(v_remaining_4341_, v___x_4342_);
v___y_4337_ = v___x_4343_;
goto v___jp_4336_;
}
else
{
uint8_t v___x_4344_; 
v___x_4344_ = 0;
v___y_4337_ = v___x_4344_;
goto v___jp_4336_;
}
}
else
{
uint8_t v___x_4345_; 
v___x_4345_ = 0;
v___y_4337_ = v___x_4345_;
goto v___jp_4336_;
}
}
}
}
v___jp_4307_:
{
lean_object* v___x_4310_; 
if (v_isShared_4302_ == 0)
{
v___x_4310_ = v___x_4301_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_reader_4292_);
lean_ctor_set(v_reuseFailAlloc_4335_, 1, v_writer_4293_);
lean_ctor_set(v_reuseFailAlloc_4335_, 2, v_config_4295_);
lean_ctor_set(v_reuseFailAlloc_4335_, 3, v_events_4296_);
lean_ctor_set(v_reuseFailAlloc_4335_, 4, v_error_4297_);
lean_ctor_set(v_reuseFailAlloc_4335_, 5, v_date_4298_);
lean_ctor_set_uint8(v_reuseFailAlloc_4335_, sizeof(void*)*6, v_keepAlive_4299_);
v___x_4310_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
lean_object* v_st_4312_; 
lean_ctor_set_uint8(v___x_4310_, sizeof(void*)*6 + 1, v___y_4308_);
lean_inc(v_dateSecond_4283_);
lean_inc(v_handlerTask_4282_);
lean_inc(v_pendingHead_4280_);
lean_inc(v_expectData_4278_);
lean_inc(v_respStream_4276_);
lean_inc_ref(v_response_4275_);
lean_inc(v_headerTimeout_4274_);
lean_inc(v_currentTimeout_4273_);
lean_inc(v_keepAliveTimeout_4272_);
lean_inc_ref(v_requestStream_4271_);
lean_inc_ref(v___x_4310_);
if (v_isShared_4288_ == 0)
{
lean_ctor_set(v___x_4287_, 0, v___x_4310_);
v_st_4312_ = v___x_4287_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4310_);
lean_ctor_set(v_reuseFailAlloc_4334_, 1, v_requestStream_4271_);
lean_ctor_set(v_reuseFailAlloc_4334_, 2, v_keepAliveTimeout_4272_);
lean_ctor_set(v_reuseFailAlloc_4334_, 3, v_currentTimeout_4273_);
lean_ctor_set(v_reuseFailAlloc_4334_, 4, v_headerTimeout_4274_);
lean_ctor_set(v_reuseFailAlloc_4334_, 5, v_response_4275_);
lean_ctor_set(v_reuseFailAlloc_4334_, 6, v_respStream_4276_);
lean_ctor_set(v_reuseFailAlloc_4334_, 7, v_expectData_4278_);
lean_ctor_set(v_reuseFailAlloc_4334_, 8, v_pendingHead_4280_);
lean_ctor_set(v_reuseFailAlloc_4334_, 9, v_handlerTask_4282_);
lean_ctor_set(v_reuseFailAlloc_4334_, 10, v_dateSecond_4283_);
lean_ctor_set_uint8(v_reuseFailAlloc_4334_, sizeof(void*)*11, v_requiresData_4277_);
lean_ctor_set_uint8(v_reuseFailAlloc_4334_, sizeof(void*)*11 + 1, v_handlerDispatched_4279_);
lean_ctor_set_uint8(v_reuseFailAlloc_4334_, sizeof(void*)*11 + 2, v_requestFinalOffered_4281_);
lean_ctor_set_uint8(v_reuseFailAlloc_4334_, sizeof(void*)*11 + 3, v_peerClosed_4284_);
lean_ctor_set_uint8(v_reuseFailAlloc_4334_, sizeof(void*)*11 + 4, v_requestEnded_4285_);
v_st_4312_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
if (lean_obj_tag(v_snd_4294_) == 1)
{
lean_object* v_val_4313_; uint8_t v_final_4314_; uint8_t v_incomplete_4315_; lean_object* v_chunk_4316_; lean_object* v___f_4317_; lean_object* v___f_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___f_4325_; lean_object* v___x_4326_; uint8_t v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v_val_4313_ = lean_ctor_get(v_snd_4294_, 0);
lean_inc(v_val_4313_);
lean_dec_ref_known(v_snd_4294_, 1);
v_final_4314_ = lean_ctor_get_uint8(v_val_4313_, sizeof(void*)*1);
v_incomplete_4315_ = lean_ctor_get_uint8(v_val_4313_, sizeof(void*)*1 + 1);
v_chunk_4316_ = lean_ctor_get(v_val_4313_, 0);
lean_inc_ref(v_chunk_4316_);
lean_dec(v_val_4313_);
lean_inc_ref(v_st_4312_);
v___f_4317_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_4317_, 0, v_st_4312_);
v___f_4318_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_4318_, 0, v_inst_4009_);
lean_closure_set(v___f_4318_, 1, v_handler_4011_);
lean_closure_set(v___f_4318_, 2, v___f_4317_);
v___x_4319_ = lean_box(v_final_4314_);
v___x_4320_ = lean_box(v_requiresData_4277_);
v___x_4321_ = lean_box(v_handlerDispatched_4279_);
v___x_4322_ = lean_box(v_x_4265_);
v___x_4323_ = lean_box(v_peerClosed_4284_);
v___x_4324_ = lean_box(v_requestEnded_4285_);
lean_inc_ref(v_requestStream_4271_);
v___f_4325_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 20, 18);
lean_closure_set(v___f_4325_, 0, v___x_4319_);
lean_closure_set(v___f_4325_, 1, v_st_4312_);
lean_closure_set(v___f_4325_, 2, v___x_4310_);
lean_closure_set(v___f_4325_, 3, v_requestStream_4271_);
lean_closure_set(v___f_4325_, 4, v_keepAliveTimeout_4272_);
lean_closure_set(v___f_4325_, 5, v_currentTimeout_4273_);
lean_closure_set(v___f_4325_, 6, v_headerTimeout_4274_);
lean_closure_set(v___f_4325_, 7, v_response_4275_);
lean_closure_set(v___f_4325_, 8, v_respStream_4276_);
lean_closure_set(v___f_4325_, 9, v___x_4320_);
lean_closure_set(v___f_4325_, 10, v_expectData_4278_);
lean_closure_set(v___f_4325_, 11, v___x_4321_);
lean_closure_set(v___f_4325_, 12, v_pendingHead_4280_);
lean_closure_set(v___f_4325_, 13, v___x_4322_);
lean_closure_set(v___f_4325_, 14, v_handlerTask_4282_);
lean_closure_set(v___f_4325_, 15, v_dateSecond_4283_);
lean_closure_set(v___f_4325_, 16, v___x_4323_);
lean_closure_set(v___f_4325_, 17, v___x_4324_);
v___x_4326_ = lean_unsigned_to_nat(0u);
v___x_4327_ = 0;
v___x_4328_ = l_Std_Http_Body_Stream_offer(v_requestStream_4271_, v_chunk_4316_, v_incomplete_4315_, v_final_4314_);
v___x_4329_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4326_, v___x_4327_, v___x_4328_, v___f_4325_);
v___x_4330_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4326_, v___x_4327_, v___x_4329_, v___f_4318_);
v___x_4331_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4326_, v___x_4327_, v___x_4330_, v___f_4306_);
return v___x_4331_;
}
else
{
lean_object* v___x_4332_; lean_object* v___x_4333_; 
lean_dec_ref(v___x_4310_);
lean_dec(v_snd_4294_);
lean_dec(v_dateSecond_4283_);
lean_dec(v_handlerTask_4282_);
lean_dec(v_pendingHead_4280_);
lean_dec(v_expectData_4278_);
lean_dec(v_respStream_4276_);
lean_dec_ref(v_response_4275_);
lean_dec(v_headerTimeout_4274_);
lean_dec(v_currentTimeout_4273_);
lean_dec(v_keepAliveTimeout_4272_);
lean_dec_ref(v_requestStream_4271_);
lean_dec(v_handler_4011_);
lean_dec_ref(v_inst_4009_);
v___x_4332_ = lean_box(0);
v___x_4333_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v___x_4332_, v_st_4312_);
return v___x_4333_;
}
}
}
}
v___jp_4336_:
{
if (lean_obj_tag(v_snd_4294_) == 0)
{
if (v___y_4337_ == 0)
{
if (lean_obj_tag(v_state_4303_) == 2)
{
v___y_4308_ = v_x_4265_;
goto v___jp_4307_;
}
else
{
v___y_4308_ = v___y_4337_;
goto v___jp_4307_;
}
}
else
{
uint8_t v___x_4338_; 
v___x_4338_ = 0;
v___y_4308_ = v___x_4338_;
goto v___jp_4307_;
}
}
else
{
uint8_t v___x_4339_; 
v___x_4339_ = 0;
v___y_4308_ = v___x_4339_;
goto v___jp_4307_;
}
}
}
}
}
}
case 3:
{
lean_object* v_x_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4428_; 
v_x_4350_ = lean_ctor_get(v_event_4013_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_event_4013_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4352_ = v_event_4013_;
v_isShared_4353_ = v_isSharedCheck_4428_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_x_4350_);
lean_dec(v_event_4013_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4428_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
if (lean_obj_tag(v_x_4350_) == 0)
{
lean_object* v_a_4354_; lean_object* v___f_4355_; lean_object* v___x_4356_; uint8_t v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
lean_del_object(v___x_4352_);
lean_dec_ref(v_config_4012_);
lean_dec_ref(v_inst_4010_);
v_a_4354_ = lean_ctor_get(v_x_4350_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v_x_4350_, 1);
v___f_4355_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 3, 1);
lean_closure_set(v___f_4355_, 0, v_state_4014_);
v___x_4356_ = lean_unsigned_to_nat(0u);
v___x_4357_ = 0;
v___x_4358_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_4009_, v_handler_4011_, v_a_4354_);
v___x_4359_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4356_, v___x_4357_, v___x_4358_, v___f_4355_);
return v___x_4359_;
}
else
{
lean_object* v_machine_4360_; lean_object* v_reader_4361_; lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4427_; 
v_machine_4360_ = lean_ctor_get(v_state_4014_, 0);
lean_inc_ref(v_machine_4360_);
v_reader_4361_ = lean_ctor_get(v_machine_4360_, 0);
v_a_4362_ = lean_ctor_get(v_x_4350_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_x_4350_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4364_ = v_x_4350_;
v_isShared_4365_ = v_isSharedCheck_4427_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v_x_4350_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4427_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v_requestStream_4366_; lean_object* v_keepAliveTimeout_4367_; lean_object* v_currentTimeout_4368_; lean_object* v_headerTimeout_4369_; lean_object* v_response_4370_; lean_object* v_respStream_4371_; uint8_t v_requiresData_4372_; lean_object* v_expectData_4373_; uint8_t v_handlerDispatched_4374_; lean_object* v_pendingHead_4375_; uint8_t v_requestFinalOffered_4376_; lean_object* v_dateSecond_4377_; uint8_t v_peerClosed_4378_; uint8_t v_requestEnded_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4424_; 
v_requestStream_4366_ = lean_ctor_get(v_state_4014_, 1);
v_keepAliveTimeout_4367_ = lean_ctor_get(v_state_4014_, 2);
v_currentTimeout_4368_ = lean_ctor_get(v_state_4014_, 3);
v_headerTimeout_4369_ = lean_ctor_get(v_state_4014_, 4);
v_response_4370_ = lean_ctor_get(v_state_4014_, 5);
v_respStream_4371_ = lean_ctor_get(v_state_4014_, 6);
v_requiresData_4372_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11);
v_expectData_4373_ = lean_ctor_get(v_state_4014_, 7);
v_handlerDispatched_4374_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 1);
v_pendingHead_4375_ = lean_ctor_get(v_state_4014_, 8);
v_requestFinalOffered_4376_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 2);
v_dateSecond_4377_ = lean_ctor_get(v_state_4014_, 10);
v_peerClosed_4378_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 3);
v_requestEnded_4379_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 4);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_state_4014_);
if (v_isSharedCheck_4424_ == 0)
{
lean_object* v_unused_4425_; lean_object* v_unused_4426_; 
v_unused_4425_ = lean_ctor_get(v_state_4014_, 9);
lean_dec(v_unused_4425_);
v_unused_4426_ = lean_ctor_get(v_state_4014_, 0);
lean_dec(v_unused_4426_);
v___x_4381_ = v_state_4014_;
v_isShared_4382_ = v_isSharedCheck_4424_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_dateSecond_4377_);
lean_inc(v_pendingHead_4375_);
lean_inc(v_expectData_4373_);
lean_inc(v_respStream_4371_);
lean_inc(v_response_4370_);
lean_inc(v_headerTimeout_4369_);
lean_inc(v_currentTimeout_4368_);
lean_inc(v_keepAliveTimeout_4367_);
lean_inc(v_requestStream_4366_);
lean_dec(v_state_4014_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4424_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v_state_4383_; lean_object* v___x_4384_; 
v_state_4383_ = lean_ctor_get(v_reader_4361_, 0);
v___x_4384_ = lean_box(0);
if (lean_obj_tag(v_state_4383_) == 7)
{
lean_object* v_close_4385_; lean_object* v_isClosed_4386_; lean_object* v_body_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___f_4392_; lean_object* v___f_4393_; lean_object* v___f_4394_; lean_object* v___x_4395_; uint8_t v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
lean_del_object(v___x_4381_);
lean_del_object(v___x_4364_);
lean_del_object(v___x_4352_);
lean_dec_ref(v_config_4012_);
lean_dec(v_handler_4011_);
lean_dec_ref(v_inst_4009_);
v_close_4385_ = lean_ctor_get(v_inst_4010_, 1);
lean_inc_ref(v_close_4385_);
v_isClosed_4386_ = lean_ctor_get(v_inst_4010_, 2);
lean_inc_ref(v_isClosed_4386_);
lean_dec_ref(v_inst_4010_);
v_body_4387_ = lean_ctor_get(v_a_4362_, 1);
lean_inc_n(v_body_4387_, 2);
lean_dec(v_a_4362_);
v___x_4388_ = lean_box(v_requiresData_4372_);
v___x_4389_ = lean_box(v_requestFinalOffered_4376_);
v___x_4390_ = lean_box(v_peerClosed_4378_);
v___x_4391_ = lean_box(v_requestEnded_4379_);
v___f_4392_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 17, 15);
lean_closure_set(v___f_4392_, 0, v_machine_4360_);
lean_closure_set(v___f_4392_, 1, v_requestStream_4366_);
lean_closure_set(v___f_4392_, 2, v_keepAliveTimeout_4367_);
lean_closure_set(v___f_4392_, 3, v_currentTimeout_4368_);
lean_closure_set(v___f_4392_, 4, v_headerTimeout_4369_);
lean_closure_set(v___f_4392_, 5, v_response_4370_);
lean_closure_set(v___f_4392_, 6, v_respStream_4371_);
lean_closure_set(v___f_4392_, 7, v___x_4388_);
lean_closure_set(v___f_4392_, 8, v_expectData_4373_);
lean_closure_set(v___f_4392_, 9, v_pendingHead_4375_);
lean_closure_set(v___f_4392_, 10, v___x_4389_);
lean_closure_set(v___f_4392_, 11, v___x_4384_);
lean_closure_set(v___f_4392_, 12, v_dateSecond_4377_);
lean_closure_set(v___f_4392_, 13, v___x_4390_);
lean_closure_set(v___f_4392_, 14, v___x_4391_);
lean_inc_ref(v___f_4392_);
v___f_4393_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4393_, 0, v___f_4392_);
v___f_4394_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_4394_, 0, v_close_4385_);
lean_closure_set(v___f_4394_, 1, v_body_4387_);
lean_closure_set(v___f_4394_, 2, v___f_4393_);
lean_closure_set(v___f_4394_, 3, v___f_4392_);
v___x_4395_ = lean_unsigned_to_nat(0u);
v___x_4396_ = 0;
v___x_4397_ = lean_apply_2(v_isClosed_4386_, v_body_4387_, lean_box(0));
v___x_4398_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4395_, v___x_4396_, v___x_4397_, v___f_4394_);
return v___x_4398_;
}
else
{
lean_object* v_state_4400_; 
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 9, v___x_4384_);
v_state_4400_ = v___x_4381_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_machine_4360_);
lean_ctor_set(v_reuseFailAlloc_4423_, 1, v_requestStream_4366_);
lean_ctor_set(v_reuseFailAlloc_4423_, 2, v_keepAliveTimeout_4367_);
lean_ctor_set(v_reuseFailAlloc_4423_, 3, v_currentTimeout_4368_);
lean_ctor_set(v_reuseFailAlloc_4423_, 4, v_headerTimeout_4369_);
lean_ctor_set(v_reuseFailAlloc_4423_, 5, v_response_4370_);
lean_ctor_set(v_reuseFailAlloc_4423_, 6, v_respStream_4371_);
lean_ctor_set(v_reuseFailAlloc_4423_, 7, v_expectData_4373_);
lean_ctor_set(v_reuseFailAlloc_4423_, 8, v_pendingHead_4375_);
lean_ctor_set(v_reuseFailAlloc_4423_, 9, v___x_4384_);
lean_ctor_set(v_reuseFailAlloc_4423_, 10, v_dateSecond_4377_);
lean_ctor_set_uint8(v_reuseFailAlloc_4423_, sizeof(void*)*11, v_requiresData_4372_);
lean_ctor_set_uint8(v_reuseFailAlloc_4423_, sizeof(void*)*11 + 1, v_handlerDispatched_4374_);
lean_ctor_set_uint8(v_reuseFailAlloc_4423_, sizeof(void*)*11 + 2, v_requestFinalOffered_4376_);
lean_ctor_set_uint8(v_reuseFailAlloc_4423_, sizeof(void*)*11 + 3, v_peerClosed_4378_);
lean_ctor_set_uint8(v_reuseFailAlloc_4423_, sizeof(void*)*11 + 4, v_requestEnded_4379_);
v_state_4400_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
uint8_t v___x_4401_; lean_object* v___f_4402_; uint8_t v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___f_4406_; lean_object* v___x_4407_; lean_object* v_val_4409_; lean_object* v___x_4414_; 
v___x_4401_ = 0;
v___f_4402_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2));
v___x_4403_ = 1;
v___x_4404_ = lean_box(v___x_4401_);
v___x_4405_ = lean_box(v___x_4403_);
v___f_4406_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19___boxed), 9, 7);
lean_closure_set(v___f_4406_, 0, v___x_4404_);
lean_closure_set(v___f_4406_, 1, v___x_4405_);
lean_closure_set(v___f_4406_, 2, v_inst_4009_);
lean_closure_set(v___f_4406_, 3, v_handler_4011_);
lean_closure_set(v___f_4406_, 4, v_inst_4010_);
lean_closure_set(v___f_4406_, 5, v___f_4402_);
lean_closure_set(v___f_4406_, 6, v_a_4362_);
v___x_4407_ = lean_unsigned_to_nat(0u);
v___x_4414_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(v_config_4012_, v_state_4400_);
lean_dec_ref(v_config_4012_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; lean_object* v___x_4417_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_a_4415_);
lean_dec_ref_known(v___x_4414_, 1);
if (v_isShared_4365_ == 0)
{
lean_ctor_set(v___x_4364_, 0, v_a_4415_);
v___x_4417_ = v___x_4364_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4415_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
v_val_4409_ = v___x_4417_;
goto v___jp_4408_;
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; 
v_a_4419_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_a_4419_);
lean_dec_ref_known(v___x_4414_, 1);
if (v_isShared_4365_ == 0)
{
lean_ctor_set_tag(v___x_4364_, 0);
lean_ctor_set(v___x_4364_, 0, v_a_4419_);
v___x_4421_ = v___x_4364_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4419_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
v_val_4409_ = v___x_4421_;
goto v___jp_4408_;
}
}
v___jp_4408_:
{
lean_object* v___x_4411_; 
if (v_isShared_4353_ == 0)
{
lean_ctor_set_tag(v___x_4352_, 0);
lean_ctor_set(v___x_4352_, 0, v_val_4409_);
v___x_4411_ = v___x_4352_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_val_4409_);
v___x_4411_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
lean_object* v___x_4412_; 
v___x_4412_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4407_, v___x_4401_, v___x_4411_, v___f_4406_);
return v___x_4412_;
}
}
}
}
}
}
}
}
}
case 4:
{
lean_object* v___f_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; uint8_t v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
lean_dec_ref(v_config_4012_);
lean_dec_ref(v_inst_4010_);
v___f_4429_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20___boxed), 3, 1);
lean_closure_set(v___f_4429_, 0, v_state_4014_);
v___x_4430_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__4, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__4_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__4);
v___x_4431_ = lean_unsigned_to_nat(0u);
v___x_4432_ = 0;
v___x_4433_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_4009_, v_handler_4011_, v___x_4430_);
v___x_4434_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4431_, v___x_4432_, v___x_4433_, v___f_4429_);
return v___x_4434_;
}
case 6:
{
lean_object* v_machine_4435_; lean_object* v_requestStream_4436_; lean_object* v_keepAliveTimeout_4437_; lean_object* v_currentTimeout_4438_; lean_object* v_headerTimeout_4439_; lean_object* v_response_4440_; lean_object* v_respStream_4441_; uint8_t v_requiresData_4442_; lean_object* v_expectData_4443_; lean_object* v_pendingHead_4444_; uint8_t v_requestFinalOffered_4445_; lean_object* v_handlerTask_4446_; lean_object* v_dateSecond_4447_; uint8_t v_peerClosed_4448_; uint8_t v_requestEnded_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4463_; 
lean_dec_ref(v_config_4012_);
lean_dec(v_handler_4011_);
lean_dec_ref(v_inst_4010_);
lean_dec_ref(v_inst_4009_);
v_machine_4435_ = lean_ctor_get(v_state_4014_, 0);
v_requestStream_4436_ = lean_ctor_get(v_state_4014_, 1);
v_keepAliveTimeout_4437_ = lean_ctor_get(v_state_4014_, 2);
v_currentTimeout_4438_ = lean_ctor_get(v_state_4014_, 3);
v_headerTimeout_4439_ = lean_ctor_get(v_state_4014_, 4);
v_response_4440_ = lean_ctor_get(v_state_4014_, 5);
v_respStream_4441_ = lean_ctor_get(v_state_4014_, 6);
v_requiresData_4442_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11);
v_expectData_4443_ = lean_ctor_get(v_state_4014_, 7);
v_pendingHead_4444_ = lean_ctor_get(v_state_4014_, 8);
v_requestFinalOffered_4445_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 2);
v_handlerTask_4446_ = lean_ctor_get(v_state_4014_, 9);
v_dateSecond_4447_ = lean_ctor_get(v_state_4014_, 10);
v_peerClosed_4448_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 3);
v_requestEnded_4449_ = lean_ctor_get_uint8(v_state_4014_, sizeof(void*)*11 + 4);
v_isSharedCheck_4463_ = !lean_is_exclusive(v_state_4014_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4451_ = v_state_4014_;
v_isShared_4452_ = v_isSharedCheck_4463_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_dateSecond_4447_);
lean_inc(v_handlerTask_4446_);
lean_inc(v_pendingHead_4444_);
lean_inc(v_expectData_4443_);
lean_inc(v_respStream_4441_);
lean_inc(v_response_4440_);
lean_inc(v_headerTimeout_4439_);
lean_inc(v_currentTimeout_4438_);
lean_inc(v_keepAliveTimeout_4437_);
lean_inc(v_requestStream_4436_);
lean_inc(v_machine_4435_);
lean_dec(v_state_4014_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4463_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; uint8_t v___x_4455_; lean_object* v___x_4457_; 
v___x_4453_ = lean_box(55);
v___x_4454_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_4435_, v___x_4453_);
v___x_4455_ = 0;
if (v_isShared_4452_ == 0)
{
lean_ctor_set(v___x_4451_, 0, v___x_4454_);
v___x_4457_ = v___x_4451_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v___x_4454_);
lean_ctor_set(v_reuseFailAlloc_4462_, 1, v_requestStream_4436_);
lean_ctor_set(v_reuseFailAlloc_4462_, 2, v_keepAliveTimeout_4437_);
lean_ctor_set(v_reuseFailAlloc_4462_, 3, v_currentTimeout_4438_);
lean_ctor_set(v_reuseFailAlloc_4462_, 4, v_headerTimeout_4439_);
lean_ctor_set(v_reuseFailAlloc_4462_, 5, v_response_4440_);
lean_ctor_set(v_reuseFailAlloc_4462_, 6, v_respStream_4441_);
lean_ctor_set(v_reuseFailAlloc_4462_, 7, v_expectData_4443_);
lean_ctor_set(v_reuseFailAlloc_4462_, 8, v_pendingHead_4444_);
lean_ctor_set(v_reuseFailAlloc_4462_, 9, v_handlerTask_4446_);
lean_ctor_set(v_reuseFailAlloc_4462_, 10, v_dateSecond_4447_);
lean_ctor_set_uint8(v_reuseFailAlloc_4462_, sizeof(void*)*11, v_requiresData_4442_);
lean_ctor_set_uint8(v_reuseFailAlloc_4462_, sizeof(void*)*11 + 2, v_requestFinalOffered_4445_);
lean_ctor_set_uint8(v_reuseFailAlloc_4462_, sizeof(void*)*11 + 3, v_peerClosed_4448_);
lean_ctor_set_uint8(v_reuseFailAlloc_4462_, sizeof(void*)*11 + 4, v_requestEnded_4449_);
v___x_4457_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
lean_ctor_set_uint8(v___x_4457_, sizeof(void*)*11 + 1, v___x_4455_);
v___x_4458_ = lean_box(v___x_4455_);
v___x_4459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4457_);
lean_ctor_set(v___x_4459_, 1, v___x_4458_);
v___x_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4459_);
v___x_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
return v___x_4461_;
}
}
}
default: 
{
lean_dec(v_event_4013_);
lean_dec_ref(v_config_4012_);
lean_dec(v_handler_4011_);
lean_dec_ref(v_inst_4010_);
lean_dec_ref(v_inst_4009_);
goto v___jp_4016_;
}
}
v___jp_4016_:
{
uint8_t v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4017_ = 1;
v___x_4018_ = lean_box(v___x_4017_);
v___x_4019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4019_, 0, v_state_4014_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
v___x_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4019_);
v___x_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4020_);
return v___x_4021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_4464_, lean_object* v_inst_4465_, lean_object* v_handler_4466_, lean_object* v_config_4467_, lean_object* v_event_4468_, lean_object* v_state_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_4464_, v_inst_4465_, v_handler_4466_, v_config_4467_, v_event_4468_, v_state_4469_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03c3_4472_, lean_object* v_00_u03b2_4473_, lean_object* v_inst_4474_, lean_object* v_inst_4475_, lean_object* v_handler_4476_, lean_object* v_config_4477_, lean_object* v_event_4478_, lean_object* v_state_4479_){
_start:
{
lean_object* v___x_4481_; 
v___x_4481_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_4474_, v_inst_4475_, v_handler_4476_, v_config_4477_, v_event_4478_, v_state_4479_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03c3_4482_, lean_object* v_00_u03b2_4483_, lean_object* v_inst_4484_, lean_object* v_inst_4485_, lean_object* v_handler_4486_, lean_object* v_config_4487_, lean_object* v_event_4488_, lean_object* v_state_4489_, lean_object* v_a_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03c3_4482_, v_00_u03b2_4483_, v_inst_4484_, v_inst_4485_, v_handler_4486_, v_config_4487_, v_event_4488_, v_state_4489_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_connectionContext_4492_, uint8_t v_handlerDispatched_4493_, lean_object* v_respStream_4494_, lean_object* v_headerTimeout_4495_, lean_object* v_keepAliveTimeout_4496_, lean_object* v_currentTimeout_4497_, lean_object* v_expectData_4498_, lean_object* v_response_4499_, lean_object* v_socket_4500_, lean_object* v_reader_4501_, lean_object* v_inputLimit_4502_, uint8_t v_needsInput_4503_, uint8_t v_requiresData_4504_, uint8_t v_sentMessage_4505_, lean_object* v_state_4506_, uint8_t v_requestBodyInterested_4507_, lean_object* v_requestBody_4508_){
_start:
{
lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; uint8_t v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; uint8_t v___y_4523_; lean_object* v___y_4524_; uint8_t v___y_4528_; uint8_t v___y_4531_; uint8_t v___y_4534_; 
if (v_requiresData_4504_ == 0)
{
if (v_handlerDispatched_4493_ == 0)
{
uint8_t v___x_4542_; 
v___x_4542_ = 1;
v___y_4534_ = v___x_4542_;
goto v___jp_4533_;
}
else
{
if (lean_obj_tag(v_respStream_4494_) == 0)
{
if (v_sentMessage_4505_ == 0)
{
switch(lean_obj_tag(v_state_4506_))
{
case 6:
{
lean_dec(v_socket_4500_);
v___y_4531_ = v_sentMessage_4505_;
goto v___jp_4530_;
}
case 7:
{
lean_dec(v_socket_4500_);
v___y_4531_ = v_sentMessage_4505_;
goto v___jp_4530_;
}
default: 
{
lean_object* v_state_4543_; 
v_state_4543_ = lean_ctor_get(v_reader_4501_, 0);
if (lean_obj_tag(v_state_4543_) == 2)
{
if (v_requestBodyInterested_4507_ == 0)
{
lean_dec(v_socket_4500_);
v___y_4531_ = v_requestBodyInterested_4507_;
goto v___jp_4530_;
}
else
{
v___y_4534_ = v_requestBodyInterested_4507_;
goto v___jp_4533_;
}
}
else
{
lean_dec(v_socket_4500_);
v___y_4531_ = v_sentMessage_4505_;
goto v___jp_4530_;
}
}
}
}
else
{
v___y_4534_ = v_sentMessage_4505_;
goto v___jp_4533_;
}
}
else
{
v___y_4534_ = v_handlerDispatched_4493_;
goto v___jp_4533_;
}
}
}
else
{
v___y_4534_ = v_requiresData_4504_;
goto v___jp_4533_;
}
v___jp_4510_:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; 
v___x_4519_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_4519_, 0, v___y_4512_);
lean_ctor_set(v___x_4519_, 1, v___y_4517_);
lean_ctor_set(v___x_4519_, 2, v___y_4518_);
lean_ctor_set(v___x_4519_, 3, v___y_4511_);
lean_ctor_set(v___x_4519_, 4, v_requestBody_4508_);
lean_ctor_set(v___x_4519_, 5, v___y_4516_);
lean_ctor_set(v___x_4519_, 6, v___y_4515_);
lean_ctor_set(v___x_4519_, 7, v___y_4513_);
lean_ctor_set(v___x_4519_, 8, v_connectionContext_4492_);
lean_ctor_set_uint8(v___x_4519_, sizeof(void*)*9, v___y_4514_);
v___x_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4520_, 0, v___x_4519_);
v___x_4521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4520_);
return v___x_4521_;
}
v___jp_4522_:
{
if (v_handlerDispatched_4493_ == 0)
{
lean_object* v___x_4525_; 
lean_dec_ref(v_response_4499_);
v___x_4525_ = lean_box(0);
v___y_4511_ = v_respStream_4494_;
v___y_4512_ = v___y_4524_;
v___y_4513_ = v_headerTimeout_4495_;
v___y_4514_ = v___y_4523_;
v___y_4515_ = v_keepAliveTimeout_4496_;
v___y_4516_ = v_currentTimeout_4497_;
v___y_4517_ = v_expectData_4498_;
v___y_4518_ = v___x_4525_;
goto v___jp_4510_;
}
else
{
lean_object* v___x_4526_; 
v___x_4526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4526_, 0, v_response_4499_);
v___y_4511_ = v_respStream_4494_;
v___y_4512_ = v___y_4524_;
v___y_4513_ = v_headerTimeout_4495_;
v___y_4514_ = v___y_4523_;
v___y_4515_ = v_keepAliveTimeout_4496_;
v___y_4516_ = v_currentTimeout_4497_;
v___y_4517_ = v_expectData_4498_;
v___y_4518_ = v___x_4526_;
goto v___jp_4510_;
}
}
v___jp_4527_:
{
lean_object* v___x_4529_; 
v___x_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4529_, 0, v_socket_4500_);
v___y_4523_ = v___y_4528_;
v___y_4524_ = v___x_4529_;
goto v___jp_4522_;
}
v___jp_4530_:
{
lean_object* v___x_4532_; 
v___x_4532_ = lean_box(0);
v___y_4523_ = v___y_4531_;
v___y_4524_ = v___x_4532_;
goto v___jp_4522_;
}
v___jp_4533_:
{
uint8_t v_noMoreInput_4535_; 
v_noMoreInput_4535_ = lean_ctor_get_uint8(v_reader_4501_, sizeof(void*)*6);
if (v_noMoreInput_4535_ == 0)
{
lean_object* v_input_4536_; lean_object* v_array_4537_; lean_object* v_idx_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; 
v_input_4536_ = lean_ctor_get(v_reader_4501_, 1);
v_array_4537_ = lean_ctor_get(v_input_4536_, 0);
v_idx_4538_ = lean_ctor_get(v_input_4536_, 1);
v___x_4539_ = lean_byte_array_size(v_array_4537_);
v___x_4540_ = lean_nat_sub(v___x_4539_, v_idx_4538_);
v___x_4541_ = lean_nat_dec_le(v_inputLimit_4502_, v___x_4540_);
lean_dec(v___x_4540_);
if (v___x_4541_ == 0)
{
v___y_4528_ = v___y_4534_;
goto v___jp_4527_;
}
else
{
if (v_needsInput_4503_ == 0)
{
lean_dec(v_socket_4500_);
v___y_4531_ = v___y_4534_;
goto v___jp_4530_;
}
else
{
v___y_4528_ = v___y_4534_;
goto v___jp_4527_;
}
}
}
else
{
lean_dec(v_socket_4500_);
v___y_4531_ = v___y_4534_;
goto v___jp_4530_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_connectionContext_4544_ = _args[0];
lean_object* v_handlerDispatched_4545_ = _args[1];
lean_object* v_respStream_4546_ = _args[2];
lean_object* v_headerTimeout_4547_ = _args[3];
lean_object* v_keepAliveTimeout_4548_ = _args[4];
lean_object* v_currentTimeout_4549_ = _args[5];
lean_object* v_expectData_4550_ = _args[6];
lean_object* v_response_4551_ = _args[7];
lean_object* v_socket_4552_ = _args[8];
lean_object* v_reader_4553_ = _args[9];
lean_object* v_inputLimit_4554_ = _args[10];
lean_object* v_needsInput_4555_ = _args[11];
lean_object* v_requiresData_4556_ = _args[12];
lean_object* v_sentMessage_4557_ = _args[13];
lean_object* v_state_4558_ = _args[14];
lean_object* v_requestBodyInterested_4559_ = _args[15];
lean_object* v_requestBody_4560_ = _args[16];
lean_object* v___y_4561_ = _args[17];
_start:
{
uint8_t v_handlerDispatched_boxed_4562_; uint8_t v_needsInput_boxed_4563_; uint8_t v_requiresData_boxed_4564_; uint8_t v_sentMessage_boxed_4565_; uint8_t v_requestBodyInterested_boxed_4566_; lean_object* v_res_4567_; 
v_handlerDispatched_boxed_4562_ = lean_unbox(v_handlerDispatched_4545_);
v_needsInput_boxed_4563_ = lean_unbox(v_needsInput_4555_);
v_requiresData_boxed_4564_ = lean_unbox(v_requiresData_4556_);
v_sentMessage_boxed_4565_ = lean_unbox(v_sentMessage_4557_);
v_requestBodyInterested_boxed_4566_ = lean_unbox(v_requestBodyInterested_4559_);
v_res_4567_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_connectionContext_4544_, v_handlerDispatched_boxed_4562_, v_respStream_4546_, v_headerTimeout_4547_, v_keepAliveTimeout_4548_, v_currentTimeout_4549_, v_expectData_4550_, v_response_4551_, v_socket_4552_, v_reader_4553_, v_inputLimit_4554_, v_needsInput_boxed_4563_, v_requiresData_boxed_4564_, v_sentMessage_boxed_4565_, v_state_4558_, v_requestBodyInterested_boxed_4566_, v_requestBody_4560_);
lean_dec(v_state_4558_);
lean_dec(v_inputLimit_4554_);
lean_dec_ref(v_reader_4553_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_4568_, lean_object* v_x_4569_){
_start:
{
if (lean_obj_tag(v_x_4569_) == 0)
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4579_; 
lean_dec_ref(v___f_4568_);
v_a_4571_ = lean_ctor_get(v_x_4569_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v_x_4569_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4573_ = v_x_4569_;
v_isShared_4574_ = v_isSharedCheck_4579_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v_x_4569_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4579_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
lean_object* v___x_4577_; 
v___x_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4576_);
return v___x_4577_;
}
}
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4581_; 
v_a_4580_ = lean_ctor_get(v_x_4569_, 0);
lean_inc(v_a_4580_);
lean_dec_ref_known(v_x_4569_, 1);
v___x_4581_ = lean_apply_2(v___f_4568_, v_a_4580_, lean_box(0));
return v___x_4581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_4582_, lean_object* v_x_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_4582_, v_x_4583_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_connectionContext_4590_, uint8_t v_handlerDispatched_4591_, lean_object* v_respStream_4592_, lean_object* v_headerTimeout_4593_, lean_object* v_keepAliveTimeout_4594_, lean_object* v_currentTimeout_4595_, lean_object* v_expectData_4596_, lean_object* v_response_4597_, lean_object* v_socket_4598_, lean_object* v_reader_4599_, lean_object* v_inputLimit_4600_, uint8_t v_needsInput_4601_, uint8_t v_requiresData_4602_, uint8_t v_sentMessage_4603_, lean_object* v_state_4604_, uint8_t v_pullBodyStalled_4605_, uint8_t v_requestBodyOpen_4606_, lean_object* v_requestStream_4607_, uint8_t v_requestBodyInterested_4608_){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___f_4615_; lean_object* v___f_4616_; uint8_t v___y_4618_; 
v___x_4610_ = lean_box(v_handlerDispatched_4591_);
v___x_4611_ = lean_box(v_needsInput_4601_);
v___x_4612_ = lean_box(v_requiresData_4602_);
v___x_4613_ = lean_box(v_sentMessage_4603_);
v___x_4614_ = lean_box(v_requestBodyInterested_4608_);
lean_inc(v_state_4604_);
lean_inc_ref(v_reader_4599_);
v___f_4615_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 18, 16);
lean_closure_set(v___f_4615_, 0, v_connectionContext_4590_);
lean_closure_set(v___f_4615_, 1, v___x_4610_);
lean_closure_set(v___f_4615_, 2, v_respStream_4592_);
lean_closure_set(v___f_4615_, 3, v_headerTimeout_4593_);
lean_closure_set(v___f_4615_, 4, v_keepAliveTimeout_4594_);
lean_closure_set(v___f_4615_, 5, v_currentTimeout_4595_);
lean_closure_set(v___f_4615_, 6, v_expectData_4596_);
lean_closure_set(v___f_4615_, 7, v_response_4597_);
lean_closure_set(v___f_4615_, 8, v_socket_4598_);
lean_closure_set(v___f_4615_, 9, v_reader_4599_);
lean_closure_set(v___f_4615_, 10, v_inputLimit_4600_);
lean_closure_set(v___f_4615_, 11, v___x_4611_);
lean_closure_set(v___f_4615_, 12, v___x_4612_);
lean_closure_set(v___f_4615_, 13, v___x_4613_);
lean_closure_set(v___f_4615_, 14, v_state_4604_);
lean_closure_set(v___f_4615_, 15, v___x_4614_);
v___f_4616_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4616_, 0, v___f_4615_);
switch(lean_obj_tag(v_state_4604_))
{
case 6:
{
uint8_t v___x_4622_; 
lean_dec_ref(v_requestStream_4607_);
lean_dec_ref(v_reader_4599_);
v___x_4622_ = 0;
v___y_4618_ = v___x_4622_;
goto v___jp_4617_;
}
case 7:
{
uint8_t v___x_4623_; 
lean_dec_ref(v_requestStream_4607_);
lean_dec_ref(v_reader_4599_);
v___x_4623_ = 0;
v___y_4618_ = v___x_4623_;
goto v___jp_4617_;
}
default: 
{
uint8_t v___y_4632_; 
lean_dec(v_state_4604_);
if (v_sentMessage_4603_ == 0)
{
v___y_4632_ = v_sentMessage_4603_;
goto v___jp_4631_;
}
else
{
lean_object* v_state_4634_; 
v_state_4634_ = lean_ctor_get(v_reader_4599_, 0);
if (lean_obj_tag(v_state_4634_) == 2)
{
lean_object* v_a_4635_; 
v_a_4635_ = lean_ctor_get(v_state_4634_, 0);
if (lean_obj_tag(v_a_4635_) == 0)
{
lean_object* v_remaining_4636_; lean_object* v___x_4637_; uint8_t v___x_4638_; 
v_remaining_4636_ = lean_ctor_get(v_a_4635_, 0);
v___x_4637_ = lean_unsigned_to_nat(0u);
v___x_4638_ = lean_nat_dec_eq(v_remaining_4636_, v___x_4637_);
if (v___x_4638_ == 0)
{
v___y_4632_ = v___x_4638_;
goto v___jp_4631_;
}
else
{
uint8_t v___x_4639_; 
lean_dec_ref(v_requestStream_4607_);
lean_dec_ref(v_reader_4599_);
v___x_4639_ = 0;
v___y_4618_ = v___x_4639_;
goto v___jp_4617_;
}
}
else
{
uint8_t v___x_4640_; 
v___x_4640_ = 0;
v___y_4632_ = v___x_4640_;
goto v___jp_4631_;
}
}
else
{
uint8_t v___x_4641_; 
v___x_4641_ = 0;
v___y_4632_ = v___x_4641_;
goto v___jp_4631_;
}
}
v___jp_4624_:
{
if (v_pullBodyStalled_4605_ == 0)
{
if (v_requestBodyOpen_4606_ == 0)
{
lean_dec_ref(v_requestStream_4607_);
v___y_4618_ = v_requestBodyOpen_4606_;
goto v___jp_4617_;
}
else
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
v___x_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4625_, 0, v_requestStream_4607_);
v___x_4626_ = lean_unsigned_to_nat(0u);
v___x_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4627_, 0, v___x_4625_);
v___x_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4628_, 0, v___x_4627_);
v___x_4629_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4626_, v_pullBodyStalled_4605_, v___x_4628_, v___f_4616_);
return v___x_4629_;
}
}
else
{
uint8_t v___x_4630_; 
lean_dec_ref(v_requestStream_4607_);
v___x_4630_ = 0;
v___y_4618_ = v___x_4630_;
goto v___jp_4617_;
}
}
v___jp_4631_:
{
lean_object* v_state_4633_; 
v_state_4633_ = lean_ctor_get(v_reader_4599_, 0);
lean_inc(v_state_4633_);
lean_dec_ref(v_reader_4599_);
if (lean_obj_tag(v_state_4633_) == 2)
{
lean_dec_ref_known(v_state_4633_, 1);
goto v___jp_4624_;
}
else
{
lean_dec(v_state_4633_);
if (v___y_4632_ == 0)
{
lean_dec_ref(v_requestStream_4607_);
v___y_4618_ = v___y_4632_;
goto v___jp_4617_;
}
else
{
goto v___jp_4624_;
}
}
}
}
}
v___jp_4617_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4619_ = lean_unsigned_to_nat(0u);
v___x_4620_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_4621_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4619_, v___y_4618_, v___x_4620_, v___f_4616_);
return v___x_4621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_connectionContext_4642_ = _args[0];
lean_object* v_handlerDispatched_4643_ = _args[1];
lean_object* v_respStream_4644_ = _args[2];
lean_object* v_headerTimeout_4645_ = _args[3];
lean_object* v_keepAliveTimeout_4646_ = _args[4];
lean_object* v_currentTimeout_4647_ = _args[5];
lean_object* v_expectData_4648_ = _args[6];
lean_object* v_response_4649_ = _args[7];
lean_object* v_socket_4650_ = _args[8];
lean_object* v_reader_4651_ = _args[9];
lean_object* v_inputLimit_4652_ = _args[10];
lean_object* v_needsInput_4653_ = _args[11];
lean_object* v_requiresData_4654_ = _args[12];
lean_object* v_sentMessage_4655_ = _args[13];
lean_object* v_state_4656_ = _args[14];
lean_object* v_pullBodyStalled_4657_ = _args[15];
lean_object* v_requestBodyOpen_4658_ = _args[16];
lean_object* v_requestStream_4659_ = _args[17];
lean_object* v_requestBodyInterested_4660_ = _args[18];
lean_object* v___y_4661_ = _args[19];
_start:
{
uint8_t v_handlerDispatched_boxed_4662_; uint8_t v_needsInput_boxed_4663_; uint8_t v_requiresData_boxed_4664_; uint8_t v_sentMessage_boxed_4665_; uint8_t v_pullBodyStalled_boxed_4666_; uint8_t v_requestBodyOpen_boxed_4667_; uint8_t v_requestBodyInterested_boxed_4668_; lean_object* v_res_4669_; 
v_handlerDispatched_boxed_4662_ = lean_unbox(v_handlerDispatched_4643_);
v_needsInput_boxed_4663_ = lean_unbox(v_needsInput_4653_);
v_requiresData_boxed_4664_ = lean_unbox(v_requiresData_4654_);
v_sentMessage_boxed_4665_ = lean_unbox(v_sentMessage_4655_);
v_pullBodyStalled_boxed_4666_ = lean_unbox(v_pullBodyStalled_4657_);
v_requestBodyOpen_boxed_4667_ = lean_unbox(v_requestBodyOpen_4658_);
v_requestBodyInterested_boxed_4668_ = lean_unbox(v_requestBodyInterested_4660_);
v_res_4669_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_connectionContext_4642_, v_handlerDispatched_boxed_4662_, v_respStream_4644_, v_headerTimeout_4645_, v_keepAliveTimeout_4646_, v_currentTimeout_4647_, v_expectData_4648_, v_response_4649_, v_socket_4650_, v_reader_4651_, v_inputLimit_4652_, v_needsInput_boxed_4663_, v_requiresData_boxed_4664_, v_sentMessage_boxed_4665_, v_state_4656_, v_pullBodyStalled_boxed_4666_, v_requestBodyOpen_boxed_4667_, v_requestStream_4659_, v_requestBodyInterested_boxed_4668_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_4670_, lean_object* v_x_4671_){
_start:
{
if (lean_obj_tag(v_x_4671_) == 0)
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4681_; 
lean_dec_ref(v___f_4670_);
v_a_4673_ = lean_ctor_get(v_x_4671_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v_x_4671_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4675_ = v_x_4671_;
v_isShared_4676_ = v_isSharedCheck_4681_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v_x_4671_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4681_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
lean_object* v___x_4679_; 
v___x_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
return v___x_4679_;
}
}
}
else
{
lean_object* v_a_4682_; lean_object* v___x_4683_; 
v_a_4682_ = lean_ctor_get(v_x_4671_, 0);
lean_inc(v_a_4682_);
lean_dec_ref_known(v_x_4671_, 1);
v___x_4683_ = lean_apply_2(v___f_4670_, v_a_4682_, lean_box(0));
return v___x_4683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_4684_, lean_object* v_x_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_4684_, v_x_4685_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_connectionContext_4688_, uint8_t v_handlerDispatched_4689_, lean_object* v_respStream_4690_, lean_object* v_headerTimeout_4691_, lean_object* v_keepAliveTimeout_4692_, lean_object* v_currentTimeout_4693_, lean_object* v_expectData_4694_, lean_object* v_response_4695_, lean_object* v_socket_4696_, lean_object* v_reader_4697_, lean_object* v_inputLimit_4698_, uint8_t v_needsInput_4699_, uint8_t v_requiresData_4700_, uint8_t v_sentMessage_4701_, lean_object* v_state_4702_, uint8_t v_pullBodyStalled_4703_, lean_object* v_requestStream_4704_, uint8_t v_requestBodyOpen_4705_){
_start:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___f_4713_; lean_object* v___f_4714_; uint8_t v___y_4716_; 
v___x_4707_ = lean_box(v_handlerDispatched_4689_);
v___x_4708_ = lean_box(v_needsInput_4699_);
v___x_4709_ = lean_box(v_requiresData_4700_);
v___x_4710_ = lean_box(v_sentMessage_4701_);
v___x_4711_ = lean_box(v_pullBodyStalled_4703_);
v___x_4712_ = lean_box(v_requestBodyOpen_4705_);
lean_inc_ref(v_requestStream_4704_);
lean_inc(v_state_4702_);
lean_inc_ref(v_reader_4697_);
v___f_4713_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 20, 18);
lean_closure_set(v___f_4713_, 0, v_connectionContext_4688_);
lean_closure_set(v___f_4713_, 1, v___x_4707_);
lean_closure_set(v___f_4713_, 2, v_respStream_4690_);
lean_closure_set(v___f_4713_, 3, v_headerTimeout_4691_);
lean_closure_set(v___f_4713_, 4, v_keepAliveTimeout_4692_);
lean_closure_set(v___f_4713_, 5, v_currentTimeout_4693_);
lean_closure_set(v___f_4713_, 6, v_expectData_4694_);
lean_closure_set(v___f_4713_, 7, v_response_4695_);
lean_closure_set(v___f_4713_, 8, v_socket_4696_);
lean_closure_set(v___f_4713_, 9, v_reader_4697_);
lean_closure_set(v___f_4713_, 10, v_inputLimit_4698_);
lean_closure_set(v___f_4713_, 11, v___x_4708_);
lean_closure_set(v___f_4713_, 12, v___x_4709_);
lean_closure_set(v___f_4713_, 13, v___x_4710_);
lean_closure_set(v___f_4713_, 14, v_state_4702_);
lean_closure_set(v___f_4713_, 15, v___x_4711_);
lean_closure_set(v___f_4713_, 16, v___x_4712_);
lean_closure_set(v___f_4713_, 17, v_requestStream_4704_);
v___f_4714_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4714_, 0, v___f_4713_);
switch(lean_obj_tag(v_state_4702_))
{
case 6:
{
uint8_t v___x_4722_; 
lean_dec_ref(v_requestStream_4704_);
lean_dec_ref(v_reader_4697_);
v___x_4722_ = 0;
v___y_4716_ = v___x_4722_;
goto v___jp_4715_;
}
case 7:
{
uint8_t v___x_4723_; 
lean_dec_ref(v_requestStream_4704_);
lean_dec_ref(v_reader_4697_);
v___x_4723_ = 0;
v___y_4716_ = v___x_4723_;
goto v___jp_4715_;
}
default: 
{
uint8_t v___y_4730_; 
lean_dec(v_state_4702_);
if (v_sentMessage_4701_ == 0)
{
v___y_4730_ = v_sentMessage_4701_;
goto v___jp_4729_;
}
else
{
lean_object* v_state_4732_; 
v_state_4732_ = lean_ctor_get(v_reader_4697_, 0);
if (lean_obj_tag(v_state_4732_) == 2)
{
lean_object* v_a_4733_; 
v_a_4733_ = lean_ctor_get(v_state_4732_, 0);
if (lean_obj_tag(v_a_4733_) == 0)
{
lean_object* v_remaining_4734_; lean_object* v___x_4735_; uint8_t v___x_4736_; 
v_remaining_4734_ = lean_ctor_get(v_a_4733_, 0);
v___x_4735_ = lean_unsigned_to_nat(0u);
v___x_4736_ = lean_nat_dec_eq(v_remaining_4734_, v___x_4735_);
if (v___x_4736_ == 0)
{
v___y_4730_ = v___x_4736_;
goto v___jp_4729_;
}
else
{
uint8_t v___x_4737_; 
lean_dec_ref(v_requestStream_4704_);
lean_dec_ref(v_reader_4697_);
v___x_4737_ = 0;
v___y_4716_ = v___x_4737_;
goto v___jp_4715_;
}
}
else
{
uint8_t v___x_4738_; 
v___x_4738_ = 0;
v___y_4730_ = v___x_4738_;
goto v___jp_4729_;
}
}
else
{
uint8_t v___x_4739_; 
v___x_4739_ = 0;
v___y_4730_ = v___x_4739_;
goto v___jp_4729_;
}
}
v___jp_4724_:
{
if (v_requestBodyOpen_4705_ == 0)
{
lean_dec_ref(v_requestStream_4704_);
v___y_4716_ = v_requestBodyOpen_4705_;
goto v___jp_4715_;
}
else
{
lean_object* v___x_4725_; uint8_t v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4725_ = lean_unsigned_to_nat(0u);
v___x_4726_ = 0;
v___x_4727_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_4704_);
v___x_4728_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4725_, v___x_4726_, v___x_4727_, v___f_4714_);
return v___x_4728_;
}
}
v___jp_4729_:
{
lean_object* v_state_4731_; 
v_state_4731_ = lean_ctor_get(v_reader_4697_, 0);
lean_inc(v_state_4731_);
lean_dec_ref(v_reader_4697_);
if (lean_obj_tag(v_state_4731_) == 2)
{
lean_dec_ref_known(v_state_4731_, 1);
goto v___jp_4724_;
}
else
{
lean_dec(v_state_4731_);
if (v___y_4730_ == 0)
{
lean_dec_ref(v_requestStream_4704_);
v___y_4716_ = v___y_4730_;
goto v___jp_4715_;
}
else
{
goto v___jp_4724_;
}
}
}
}
}
v___jp_4715_:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4717_ = lean_unsigned_to_nat(0u);
v___x_4718_ = lean_box(v___y_4716_);
v___x_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4718_);
v___x_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4719_);
v___x_4721_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4717_, v___y_4716_, v___x_4720_, v___f_4714_);
return v___x_4721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_connectionContext_4740_ = _args[0];
lean_object* v_handlerDispatched_4741_ = _args[1];
lean_object* v_respStream_4742_ = _args[2];
lean_object* v_headerTimeout_4743_ = _args[3];
lean_object* v_keepAliveTimeout_4744_ = _args[4];
lean_object* v_currentTimeout_4745_ = _args[5];
lean_object* v_expectData_4746_ = _args[6];
lean_object* v_response_4747_ = _args[7];
lean_object* v_socket_4748_ = _args[8];
lean_object* v_reader_4749_ = _args[9];
lean_object* v_inputLimit_4750_ = _args[10];
lean_object* v_needsInput_4751_ = _args[11];
lean_object* v_requiresData_4752_ = _args[12];
lean_object* v_sentMessage_4753_ = _args[13];
lean_object* v_state_4754_ = _args[14];
lean_object* v_pullBodyStalled_4755_ = _args[15];
lean_object* v_requestStream_4756_ = _args[16];
lean_object* v_requestBodyOpen_4757_ = _args[17];
lean_object* v___y_4758_ = _args[18];
_start:
{
uint8_t v_handlerDispatched_boxed_4759_; uint8_t v_needsInput_boxed_4760_; uint8_t v_requiresData_boxed_4761_; uint8_t v_sentMessage_boxed_4762_; uint8_t v_pullBodyStalled_boxed_4763_; uint8_t v_requestBodyOpen_boxed_4764_; lean_object* v_res_4765_; 
v_handlerDispatched_boxed_4759_ = lean_unbox(v_handlerDispatched_4741_);
v_needsInput_boxed_4760_ = lean_unbox(v_needsInput_4751_);
v_requiresData_boxed_4761_ = lean_unbox(v_requiresData_4752_);
v_sentMessage_boxed_4762_ = lean_unbox(v_sentMessage_4753_);
v_pullBodyStalled_boxed_4763_ = lean_unbox(v_pullBodyStalled_4755_);
v_requestBodyOpen_boxed_4764_ = lean_unbox(v_requestBodyOpen_4757_);
v_res_4765_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_connectionContext_4740_, v_handlerDispatched_boxed_4759_, v_respStream_4742_, v_headerTimeout_4743_, v_keepAliveTimeout_4744_, v_currentTimeout_4745_, v_expectData_4746_, v_response_4747_, v_socket_4748_, v_reader_4749_, v_inputLimit_4750_, v_needsInput_boxed_4760_, v_requiresData_boxed_4761_, v_sentMessage_boxed_4762_, v_state_4754_, v_pullBodyStalled_boxed_4763_, v_requestStream_4756_, v_requestBodyOpen_boxed_4764_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7(lean_object* v_____do__lift_4766_, lean_object* v___y_4767_){
_start:
{
uint8_t v_closed_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v_closed_4769_ = lean_ctor_get_uint8(v_____do__lift_4766_, sizeof(void*)*6);
v___x_4770_ = lean_box(v_closed_4769_);
v___x_4771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4770_);
v___x_4772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
return v___x_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7___boxed(lean_object* v_____do__lift_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7(v_____do__lift_4773_, v___y_4774_);
lean_dec(v___y_4774_);
lean_dec_ref(v_____do__lift_4773_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4(lean_object* v___f_4777_, uint8_t v___y_4778_, lean_object* v_x_4779_){
_start:
{
uint8_t v___y_4782_; 
if (lean_obj_tag(v_x_4779_) == 0)
{
lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4797_; 
lean_dec_ref(v___f_4777_);
v_a_4789_ = lean_ctor_get(v_x_4779_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v_x_4779_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4791_ = v_x_4779_;
v_isShared_4792_ = v_isSharedCheck_4797_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v_x_4779_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4797_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4794_; 
if (v_isShared_4792_ == 0)
{
v___x_4794_ = v___x_4791_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4789_);
v___x_4794_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
lean_object* v___x_4795_; 
v___x_4795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4794_);
return v___x_4795_;
}
}
}
else
{
lean_object* v_a_4798_; uint8_t v___x_4799_; 
v_a_4798_ = lean_ctor_get(v_x_4779_, 0);
lean_inc(v_a_4798_);
lean_dec_ref_known(v_x_4779_, 1);
v___x_4799_ = lean_unbox(v_a_4798_);
lean_dec(v_a_4798_);
if (v___x_4799_ == 0)
{
v___y_4782_ = v___y_4778_;
goto v___jp_4781_;
}
else
{
uint8_t v___x_4800_; 
v___x_4800_ = 0;
v___y_4782_ = v___x_4800_;
goto v___jp_4781_;
}
}
v___jp_4781_:
{
lean_object* v___x_4783_; uint8_t v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4783_ = lean_unsigned_to_nat(0u);
v___x_4784_ = 0;
v___x_4785_ = lean_box(v___y_4782_);
v___x_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4785_);
v___x_4787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4786_);
v___x_4788_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4783_, v___x_4784_, v___x_4787_, v___f_4777_);
return v___x_4788_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4___boxed(lean_object* v___f_4801_, lean_object* v___y_4802_, lean_object* v_x_4803_, lean_object* v___y_4804_){
_start:
{
uint8_t v___y_3390__boxed_4805_; lean_object* v_res_4806_; 
v___y_3390__boxed_4805_ = lean_unbox(v___y_4802_);
v_res_4806_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4(v___f_4801_, v___y_3390__boxed_4805_, v_x_4803_);
return v_res_4806_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4(void){
_start:
{
lean_object* v___x_4815_; lean_object* v___f_4816_; lean_object* v___f_4817_; 
v___x_4815_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__1);
v___f_4816_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3));
v___f_4817_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_4817_, 0, v___f_4816_);
lean_closure_set(v___f_4817_, 1, v___x_4815_);
return v___f_4817_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__5(void){
_start:
{
lean_object* v___f_4818_; lean_object* v___x_4819_; 
v___f_4818_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4);
v___x_4819_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_4819_, 0, lean_box(0));
lean_closure_set(v___x_4819_, 1, lean_box(0));
lean_closure_set(v___x_4819_, 2, lean_box(0));
lean_closure_set(v___x_4819_, 3, v___f_4818_);
return v___x_4819_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__6(void){
_start:
{
lean_object* v___f_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___f_4820_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0));
v___x_4821_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__5);
v___x_4822_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0);
v___x_4823_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_4823_, 0, lean_box(0));
lean_closure_set(v___x_4823_, 1, lean_box(0));
lean_closure_set(v___x_4823_, 2, v___x_4822_);
lean_closure_set(v___x_4823_, 3, lean_box(0));
lean_closure_set(v___x_4823_, 4, lean_box(0));
lean_closure_set(v___x_4823_, 5, v___x_4821_);
lean_closure_set(v___x_4823_, 6, v___f_4820_);
return v___x_4823_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_4824_, lean_object* v_connectionContext_4825_, lean_object* v_state_4826_, uint8_t v_needsInput_4827_, lean_object* v_inputLimit_4828_){
_start:
{
lean_object* v_machine_4830_; lean_object* v_writer_4831_; lean_object* v_requestStream_4832_; lean_object* v_keepAliveTimeout_4833_; lean_object* v_currentTimeout_4834_; lean_object* v_headerTimeout_4835_; lean_object* v_response_4836_; lean_object* v_respStream_4837_; uint8_t v_requiresData_4838_; lean_object* v_expectData_4839_; uint8_t v_handlerDispatched_4840_; lean_object* v_reader_4841_; uint8_t v_pullBodyStalled_4842_; lean_object* v_state_4843_; uint8_t v_sentMessage_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___f_4850_; lean_object* v___f_4851_; uint8_t v___y_4853_; 
v_machine_4830_ = lean_ctor_get(v_state_4826_, 0);
lean_inc_ref(v_machine_4830_);
v_writer_4831_ = lean_ctor_get(v_machine_4830_, 1);
lean_inc_ref(v_writer_4831_);
v_requestStream_4832_ = lean_ctor_get(v_state_4826_, 1);
lean_inc_ref_n(v_requestStream_4832_, 2);
v_keepAliveTimeout_4833_ = lean_ctor_get(v_state_4826_, 2);
lean_inc(v_keepAliveTimeout_4833_);
v_currentTimeout_4834_ = lean_ctor_get(v_state_4826_, 3);
lean_inc(v_currentTimeout_4834_);
v_headerTimeout_4835_ = lean_ctor_get(v_state_4826_, 4);
lean_inc(v_headerTimeout_4835_);
v_response_4836_ = lean_ctor_get(v_state_4826_, 5);
lean_inc_ref(v_response_4836_);
v_respStream_4837_ = lean_ctor_get(v_state_4826_, 6);
lean_inc(v_respStream_4837_);
v_requiresData_4838_ = lean_ctor_get_uint8(v_state_4826_, sizeof(void*)*11);
v_expectData_4839_ = lean_ctor_get(v_state_4826_, 7);
lean_inc(v_expectData_4839_);
v_handlerDispatched_4840_ = lean_ctor_get_uint8(v_state_4826_, sizeof(void*)*11 + 1);
lean_dec_ref(v_state_4826_);
v_reader_4841_ = lean_ctor_get(v_machine_4830_, 0);
lean_inc_ref_n(v_reader_4841_, 2);
v_pullBodyStalled_4842_ = lean_ctor_get_uint8(v_machine_4830_, sizeof(void*)*6 + 1);
lean_dec_ref(v_machine_4830_);
v_state_4843_ = lean_ctor_get(v_writer_4831_, 2);
lean_inc_n(v_state_4843_, 2);
v_sentMessage_4844_ = lean_ctor_get_uint8(v_writer_4831_, sizeof(void*)*6);
lean_dec_ref(v_writer_4831_);
v___x_4845_ = lean_box(v_handlerDispatched_4840_);
v___x_4846_ = lean_box(v_needsInput_4827_);
v___x_4847_ = lean_box(v_requiresData_4838_);
v___x_4848_ = lean_box(v_sentMessage_4844_);
v___x_4849_ = lean_box(v_pullBodyStalled_4842_);
v___f_4850_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 19, 17);
lean_closure_set(v___f_4850_, 0, v_connectionContext_4825_);
lean_closure_set(v___f_4850_, 1, v___x_4845_);
lean_closure_set(v___f_4850_, 2, v_respStream_4837_);
lean_closure_set(v___f_4850_, 3, v_headerTimeout_4835_);
lean_closure_set(v___f_4850_, 4, v_keepAliveTimeout_4833_);
lean_closure_set(v___f_4850_, 5, v_currentTimeout_4834_);
lean_closure_set(v___f_4850_, 6, v_expectData_4839_);
lean_closure_set(v___f_4850_, 7, v_response_4836_);
lean_closure_set(v___f_4850_, 8, v_socket_4824_);
lean_closure_set(v___f_4850_, 9, v_reader_4841_);
lean_closure_set(v___f_4850_, 10, v_inputLimit_4828_);
lean_closure_set(v___f_4850_, 11, v___x_4846_);
lean_closure_set(v___f_4850_, 12, v___x_4847_);
lean_closure_set(v___f_4850_, 13, v___x_4848_);
lean_closure_set(v___f_4850_, 14, v_state_4843_);
lean_closure_set(v___f_4850_, 15, v___x_4849_);
lean_closure_set(v___f_4850_, 16, v_requestStream_4832_);
v___f_4851_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4851_, 0, v___f_4850_);
switch(lean_obj_tag(v_state_4843_))
{
case 6:
{
uint8_t v___x_4859_; 
lean_dec_ref(v_reader_4841_);
lean_dec_ref(v_requestStream_4832_);
v___x_4859_ = 0;
v___y_4853_ = v___x_4859_;
goto v___jp_4852_;
}
case 7:
{
uint8_t v___x_4860_; 
lean_dec_ref(v_reader_4841_);
lean_dec_ref(v_requestStream_4832_);
v___x_4860_ = 0;
v___y_4853_ = v___x_4860_;
goto v___jp_4852_;
}
default: 
{
uint8_t v___y_4862_; uint8_t v___y_4875_; 
lean_dec(v_state_4843_);
if (v_sentMessage_4844_ == 0)
{
v___y_4875_ = v_sentMessage_4844_;
goto v___jp_4874_;
}
else
{
lean_object* v_state_4878_; 
v_state_4878_ = lean_ctor_get(v_reader_4841_, 0);
if (lean_obj_tag(v_state_4878_) == 2)
{
lean_object* v_a_4879_; 
v_a_4879_ = lean_ctor_get(v_state_4878_, 0);
if (lean_obj_tag(v_a_4879_) == 0)
{
lean_object* v_remaining_4880_; lean_object* v___x_4881_; uint8_t v___x_4882_; 
v_remaining_4880_ = lean_ctor_get(v_a_4879_, 0);
v___x_4881_ = lean_unsigned_to_nat(0u);
v___x_4882_ = lean_nat_dec_eq(v_remaining_4880_, v___x_4881_);
if (v___x_4882_ == 0)
{
v___y_4875_ = v___x_4882_;
goto v___jp_4874_;
}
else
{
uint8_t v___x_4883_; 
lean_dec_ref(v_reader_4841_);
lean_dec_ref(v_requestStream_4832_);
v___x_4883_ = 0;
v___y_4853_ = v___x_4883_;
goto v___jp_4852_;
}
}
else
{
uint8_t v___x_4884_; 
v___x_4884_ = 0;
v___y_4875_ = v___x_4884_;
goto v___jp_4874_;
}
}
else
{
uint8_t v___x_4885_; 
v___x_4885_ = 0;
v___y_4875_ = v___x_4885_;
goto v___jp_4874_;
}
}
v___jp_4861_:
{
lean_object* v___x_4863_; lean_object* v___f_4864_; lean_object* v___x_4865_; uint8_t v___x_4866_; lean_object* v___x_4867_; lean_object* v___f_4868_; lean_object* v___f_4869_; lean_object* v___x_4870_; lean_object* v___x_2889__overap_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4863_ = lean_box(v___y_4862_);
v___f_4864_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_4864_, 0, v___f_4851_);
lean_closure_set(v___f_4864_, 1, v___x_4863_);
v___x_4865_ = lean_unsigned_to_nat(0u);
v___x_4866_ = 0;
v___x_4867_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__0);
v___f_4868_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__5);
v___f_4869_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___closed__6));
v___x_4870_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__6, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__6_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__6);
v___x_2889__overap_4871_ = l_Std_Mutex_atomically___redArg(v___x_4867_, v___f_4868_, v___f_4869_, v_requestStream_4832_, v___x_4870_);
v___x_4872_ = lean_apply_1(v___x_2889__overap_4871_, lean_box(0));
v___x_4873_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4865_, v___x_4866_, v___x_4872_, v___f_4864_);
return v___x_4873_;
}
v___jp_4874_:
{
lean_object* v_state_4876_; 
v_state_4876_ = lean_ctor_get(v_reader_4841_, 0);
lean_inc(v_state_4876_);
lean_dec_ref(v_reader_4841_);
if (lean_obj_tag(v_state_4876_) == 2)
{
uint8_t v___x_4877_; 
lean_dec_ref_known(v_state_4876_, 1);
v___x_4877_ = 1;
v___y_4862_ = v___x_4877_;
goto v___jp_4861_;
}
else
{
lean_dec(v_state_4876_);
if (v___y_4875_ == 0)
{
lean_dec_ref(v_requestStream_4832_);
v___y_4853_ = v___y_4875_;
goto v___jp_4852_;
}
else
{
v___y_4862_ = v___y_4875_;
goto v___jp_4861_;
}
}
}
}
}
v___jp_4852_:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4854_ = lean_unsigned_to_nat(0u);
v___x_4855_ = lean_box(v___y_4853_);
v___x_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
v___x_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4857_, 0, v___x_4856_);
v___x_4858_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4854_, v___y_4853_, v___x_4857_, v___f_4851_);
return v___x_4858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_4886_, lean_object* v_connectionContext_4887_, lean_object* v_state_4888_, lean_object* v_needsInput_4889_, lean_object* v_inputLimit_4890_, lean_object* v_a_4891_){
_start:
{
uint8_t v_needsInput_boxed_4892_; lean_object* v_res_4893_; 
v_needsInput_boxed_4892_ = lean_unbox(v_needsInput_4889_);
v_res_4893_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4886_, v_connectionContext_4887_, v_state_4888_, v_needsInput_boxed_4892_, v_inputLimit_4890_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_4894_, lean_object* v_00_u03b2_4895_, lean_object* v_inst_4896_, lean_object* v_socket_4897_, lean_object* v_connectionContext_4898_, lean_object* v_state_4899_, uint8_t v_needsInput_4900_, lean_object* v_inputLimit_4901_){
_start:
{
lean_object* v___x_4903_; 
v___x_4903_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_4897_, v_connectionContext_4898_, v_state_4899_, v_needsInput_4900_, v_inputLimit_4901_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_4904_, lean_object* v_00_u03b2_4905_, lean_object* v_inst_4906_, lean_object* v_socket_4907_, lean_object* v_connectionContext_4908_, lean_object* v_state_4909_, lean_object* v_needsInput_4910_, lean_object* v_inputLimit_4911_, lean_object* v_a_4912_){
_start:
{
uint8_t v_needsInput_boxed_4913_; lean_object* v_res_4914_; 
v_needsInput_boxed_4913_ = lean_unbox(v_needsInput_4910_);
v_res_4914_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_4904_, v_00_u03b2_4905_, v_inst_4906_, v_socket_4907_, v_connectionContext_4908_, v_state_4909_, v_needsInput_boxed_4913_, v_inputLimit_4911_);
lean_dec_ref(v_inst_4906_);
return v_res_4914_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput(lean_object* v_x_4915_){
_start:
{
switch(lean_obj_tag(v_x_4915_))
{
case 0:
{
lean_object* v_head_4916_; uint8_t v_method_4917_; uint8_t v___x_4918_; 
v_head_4916_ = lean_ctor_get(v_x_4915_, 0);
v_method_4917_ = lean_ctor_get_uint8(v_head_4916_, sizeof(void*)*2);
v___x_4918_ = l_Std_Http_Method_isSafe(v_method_4917_);
if (v___x_4918_ == 0)
{
uint8_t v___x_4919_; 
v___x_4919_ = 1;
return v___x_4919_;
}
else
{
uint8_t v___x_4920_; 
v___x_4920_ = 0;
return v___x_4920_;
}
}
case 7:
{
uint8_t v___x_4921_; 
v___x_4921_ = 1;
return v___x_4921_;
}
default: 
{
uint8_t v___x_4922_; 
v___x_4922_ = 0;
return v___x_4922_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput___boxed(lean_object* v_x_4923_){
_start:
{
uint8_t v_res_4924_; lean_object* v_r_4925_; 
v_res_4924_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput(v_x_4923_);
lean_dec(v_x_4923_);
v_r_4925_ = lean_box(v_res_4924_);
return v_r_4925_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0(lean_object* v_inst_4926_, lean_object* v_handler_4927_, lean_object* v_x_4928_){
_start:
{
if (lean_obj_tag(v_x_4928_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4938_; 
lean_dec(v_handler_4927_);
lean_dec_ref(v_inst_4926_);
v_a_4930_ = lean_ctor_get(v_x_4928_, 0);
v_isSharedCheck_4938_ = !lean_is_exclusive(v_x_4928_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4932_ = v_x_4928_;
v_isShared_4933_ = v_isSharedCheck_4938_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v_x_4928_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4938_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4930_);
v___x_4935_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4936_; 
v___x_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4935_);
return v___x_4936_;
}
}
}
else
{
lean_object* v_a_4939_; 
v_a_4939_ = lean_ctor_get(v_x_4928_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v_x_4928_, 1);
if (lean_obj_tag(v_a_4939_) == 1)
{
lean_object* v_val_4940_; lean_object* v___x_4941_; 
v_val_4940_ = lean_ctor_get(v_a_4939_, 0);
lean_inc(v_val_4940_);
lean_dec_ref_known(v_a_4939_, 1);
v___x_4941_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_4926_, v_handler_4927_, v_val_4940_);
return v___x_4941_;
}
else
{
lean_object* v___x_4942_; 
lean_dec(v_a_4939_);
lean_dec(v_handler_4927_);
lean_dec_ref(v_inst_4926_);
v___x_4942_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_4942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0___boxed(lean_object* v_inst_4943_, lean_object* v_handler_4944_, lean_object* v_x_4945_, lean_object* v___y_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0(v_inst_4943_, v_handler_4944_, v_x_4945_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(lean_object* v_inst_4948_, lean_object* v_handler_4949_, lean_object* v_outbox_4950_){
_start:
{
lean_object* v___f_4952_; lean_object* v___x_4953_; uint8_t v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___f_4952_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4952_, 0, v_inst_4948_);
lean_closure_set(v___f_4952_, 1, v_handler_4949_);
v___x_4953_ = lean_unsigned_to_nat(0u);
v___x_4954_ = 0;
v___x_4955_ = l_Std_Http_Internal_Outbox_takeError_x3f___redArg(v_outbox_4950_);
v___x_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4955_);
v___x_4957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4957_, 0, v___x_4956_);
v___x_4958_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4953_, v___x_4954_, v___x_4957_, v___f_4952_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___boxed(lean_object* v_inst_4959_, lean_object* v_handler_4960_, lean_object* v_outbox_4961_, lean_object* v_a_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_inst_4959_, v_handler_4960_, v_outbox_4961_);
lean_dec_ref(v_outbox_4961_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure(lean_object* v_00_u03c3_4964_, lean_object* v_00_u03b1_4965_, lean_object* v_inst_4966_, lean_object* v_handler_4967_, lean_object* v_outbox_4968_){
_start:
{
lean_object* v___x_4970_; 
v___x_4970_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_inst_4966_, v_handler_4967_, v_outbox_4968_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___boxed(lean_object* v_00_u03c3_4971_, lean_object* v_00_u03b1_4972_, lean_object* v_inst_4973_, lean_object* v_handler_4974_, lean_object* v_outbox_4975_, lean_object* v_a_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure(v_00_u03c3_4971_, v_00_u03b1_4972_, v_inst_4973_, v_handler_4974_, v_outbox_4975_);
lean_dec_ref(v_outbox_4975_);
return v_res_4977_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(lean_object* v_state_4978_){
_start:
{
uint8_t v_peerClosed_4979_; 
v_peerClosed_4979_ = lean_ctor_get_uint8(v_state_4978_, sizeof(void*)*11 + 3);
if (v_peerClosed_4979_ == 0)
{
lean_object* v_machine_4980_; uint8_t v_requestEnded_4981_; uint8_t v___x_4982_; 
v_machine_4980_ = lean_ctor_get(v_state_4978_, 0);
v_requestEnded_4981_ = lean_ctor_get_uint8(v_state_4978_, sizeof(void*)*11 + 4);
v___x_4982_ = 1;
if (v_requestEnded_4981_ == 0)
{
return v___x_4982_;
}
else
{
lean_object* v_reader_4983_; uint8_t v_noMoreInput_4984_; 
v_reader_4983_ = lean_ctor_get(v_machine_4980_, 0);
v_noMoreInput_4984_ = lean_ctor_get_uint8(v_reader_4983_, sizeof(void*)*6);
if (v_noMoreInput_4984_ == 0)
{
lean_object* v_state_4985_; 
v_state_4985_ = lean_ctor_get(v_reader_4983_, 0);
if (lean_obj_tag(v_state_4985_) == 7)
{
return v___x_4982_;
}
else
{
lean_object* v_input_4986_; lean_object* v_array_4987_; lean_object* v_idx_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; uint8_t v___x_4992_; 
v_input_4986_ = lean_ctor_get(v_reader_4983_, 1);
v_array_4987_ = lean_ctor_get(v_input_4986_, 0);
v_idx_4988_ = lean_ctor_get(v_input_4986_, 1);
v___x_4989_ = lean_unsigned_to_nat(0u);
v___x_4990_ = lean_byte_array_size(v_array_4987_);
v___x_4991_ = lean_nat_sub(v___x_4990_, v_idx_4988_);
v___x_4992_ = lean_nat_dec_lt(v___x_4989_, v___x_4991_);
lean_dec(v___x_4991_);
if (v___x_4992_ == 0)
{
if (lean_obj_tag(v_state_4985_) == 2)
{
return v___x_4982_;
}
else
{
return v___x_4992_;
}
}
else
{
return v___x_4992_;
}
}
}
else
{
return v_peerClosed_4979_;
}
}
}
else
{
uint8_t v___x_4993_; 
v___x_4993_ = 0;
return v___x_4993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg___boxed(lean_object* v_state_4994_){
_start:
{
uint8_t v_res_4995_; lean_object* v_r_4996_; 
v_res_4995_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(v_state_4994_);
lean_dec_ref(v_state_4994_);
v_r_4996_ = lean_box(v_res_4995_);
return v_r_4996_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend(lean_object* v_00_u03b2_4997_, lean_object* v_state_4998_){
_start:
{
uint8_t v___x_4999_; 
v___x_4999_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(v_state_4998_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___boxed(lean_object* v_00_u03b2_5000_, lean_object* v_state_5001_){
_start:
{
uint8_t v_res_5002_; lean_object* v_r_5003_; 
v_res_5002_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend(v_00_u03b2_5000_, v_state_5001_);
lean_dec_ref(v_state_5001_);
v_r_5003_ = lean_box(v_res_5002_);
return v_r_5003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__0(lean_object* v_x_5004_){
_start:
{
if (lean_obj_tag(v_x_5004_) == 0)
{
lean_object* v___x_5006_; 
v___x_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5006_, 0, v_x_5004_);
return v___x_5006_;
}
else
{
lean_object* v___x_5007_; 
lean_dec_ref_known(v_x_5004_, 1);
v___x_5007_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_5007_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__0___boxed(lean_object* v_x_5008_, lean_object* v___y_5009_){
_start:
{
lean_object* v_res_5010_; 
v_res_5010_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__0(v_x_5008_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__1(lean_object* v___x_5011_, lean_object* v_x_5012_){
_start:
{
if (lean_obj_tag(v_x_5012_) == 0)
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5022_; 
v_a_5014_ = lean_ctor_get(v_x_5012_, 0);
v_isSharedCheck_5022_ = !lean_is_exclusive(v_x_5012_);
if (v_isSharedCheck_5022_ == 0)
{
v___x_5016_ = v_x_5012_;
v_isShared_5017_ = v_isSharedCheck_5022_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v_x_5012_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5022_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
lean_object* v___x_5020_; 
v___x_5020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5020_, 0, v___x_5019_);
return v___x_5020_;
}
}
}
else
{
lean_object* v_a_5023_; lean_object* v___x_5025_; uint8_t v_isShared_5026_; uint8_t v_isSharedCheck_5038_; 
v_a_5023_ = lean_ctor_get(v_x_5012_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v_x_5012_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5025_ = v_x_5012_;
v_isShared_5026_ = v_isSharedCheck_5038_;
goto v_resetjp_5024_;
}
else
{
lean_inc(v_a_5023_);
lean_dec(v_x_5012_);
v___x_5025_ = lean_box(0);
v_isShared_5026_ = v_isSharedCheck_5038_;
goto v_resetjp_5024_;
}
v_resetjp_5024_:
{
uint8_t v___x_5027_; 
v___x_5027_ = lean_unbox(v_a_5023_);
lean_dec(v_a_5023_);
if (v___x_5027_ == 0)
{
lean_object* v___x_5028_; lean_object* v___x_5030_; 
v___x_5028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5028_, 0, v___x_5011_);
if (v_isShared_5026_ == 0)
{
lean_ctor_set(v___x_5025_, 0, v___x_5028_);
v___x_5030_ = v___x_5025_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v___x_5028_);
v___x_5030_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
lean_object* v___x_5031_; 
v___x_5031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5030_);
return v___x_5031_;
}
}
else
{
lean_object* v___x_5033_; lean_object* v___x_5035_; 
v___x_5033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5033_, 0, v___x_5011_);
if (v_isShared_5026_ == 0)
{
lean_ctor_set(v___x_5025_, 0, v___x_5033_);
v___x_5035_ = v___x_5025_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5033_);
v___x_5035_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
lean_object* v___x_5036_; 
v___x_5036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5035_);
return v___x_5036_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__1___boxed(lean_object* v___x_5039_, lean_object* v_x_5040_, lean_object* v___y_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__1(v___x_5039_, v_x_5040_);
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2(uint8_t v___x_5043_, lean_object* v_x_5044_){
_start:
{
if (lean_obj_tag(v_x_5044_) == 0)
{
lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5054_; 
v_isSharedCheck_5054_ = !lean_is_exclusive(v_x_5044_);
if (v_isSharedCheck_5054_ == 0)
{
lean_object* v_unused_5055_; 
v_unused_5055_ = lean_ctor_get(v_x_5044_, 0);
lean_dec(v_unused_5055_);
v___x_5047_ = v_x_5044_;
v_isShared_5048_ = v_isSharedCheck_5054_;
goto v_resetjp_5046_;
}
else
{
lean_dec(v_x_5044_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5054_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5049_; lean_object* v___x_5051_; 
v___x_5049_ = lean_box(v___x_5043_);
if (v_isShared_5048_ == 0)
{
lean_ctor_set_tag(v___x_5047_, 1);
lean_ctor_set(v___x_5047_, 0, v___x_5049_);
v___x_5051_ = v___x_5047_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v___x_5049_);
v___x_5051_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
lean_object* v___x_5052_; 
v___x_5052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5051_);
return v___x_5052_;
}
}
}
else
{
lean_object* v___x_5056_; 
v___x_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5056_, 0, v_x_5044_);
return v___x_5056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2___boxed(lean_object* v___x_5057_, lean_object* v_x_5058_, lean_object* v___y_5059_){
_start:
{
uint8_t v___x_2477__boxed_5060_; lean_object* v_res_5061_; 
v___x_2477__boxed_5060_ = lean_unbox(v___x_5057_);
v_res_5061_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2(v___x_2477__boxed_5060_, v_x_5058_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3(uint8_t v___x_5062_, uint8_t v_a_5063_, lean_object* v_data_5064_){
_start:
{
uint8_t v___y_5067_; 
if (lean_obj_tag(v_data_5064_) == 0)
{
v___y_5067_ = v___x_5062_;
goto v___jp_5066_;
}
else
{
v___y_5067_ = v_a_5063_;
goto v___jp_5066_;
}
v___jp_5066_:
{
lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5068_ = lean_box(v___y_5067_);
v___x_5069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5068_);
v___x_5070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5070_, 0, v___x_5069_);
return v___x_5070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3___boxed(lean_object* v___x_5071_, lean_object* v_a_5072_, lean_object* v_data_5073_, lean_object* v___y_5074_){
_start:
{
uint8_t v___x_2510__boxed_5075_; uint8_t v_a_2511__boxed_5076_; lean_object* v_res_5077_; 
v___x_2510__boxed_5075_ = lean_unbox(v___x_5071_);
v_a_2511__boxed_5076_ = lean_unbox(v_a_5072_);
v_res_5077_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3(v___x_2510__boxed_5075_, v_a_2511__boxed_5076_, v_data_5073_);
lean_dec(v_data_5073_);
return v_res_5077_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5(lean_object* v_connectionContext_5078_, lean_object* v_recvSelector_5079_, lean_object* v_socket_5080_, uint64_t v_readSize_5081_, lean_object* v___f_5082_, lean_object* v___f_5083_, lean_object* v_x_5084_){
_start:
{
if (lean_obj_tag(v_x_5084_) == 0)
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5094_; 
lean_dec_ref(v___f_5083_);
lean_dec_ref(v___f_5082_);
lean_dec(v_socket_5080_);
lean_dec_ref(v_recvSelector_5079_);
lean_dec_ref(v_connectionContext_5078_);
v_a_5086_ = lean_ctor_get(v_x_5084_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v_x_5084_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5088_ = v_x_5084_;
v_isShared_5089_ = v_isSharedCheck_5094_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v_x_5084_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5094_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
lean_object* v___x_5092_; 
v___x_5092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5092_, 0, v___x_5091_);
return v___x_5092_;
}
}
}
else
{
lean_object* v_a_5095_; lean_object* v_token_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v_a_5095_ = lean_ctor_get(v_x_5084_, 0);
lean_inc(v_a_5095_);
lean_dec_ref_known(v_x_5084_, 1);
v_token_5096_ = lean_ctor_get(v_connectionContext_5078_, 1);
lean_inc_ref(v_token_5096_);
lean_dec_ref(v_connectionContext_5078_);
v___x_5097_ = lean_box_uint64(v_readSize_5081_);
v___x_5098_ = lean_apply_2(v_recvSelector_5079_, v_socket_5080_, v___x_5097_);
v___x_5099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5098_);
lean_ctor_set(v___x_5099_, 1, v___f_5082_);
v___x_5100_ = l_Std_CancellationToken_selector(v_token_5096_);
lean_inc_ref(v___f_5083_);
v___x_5101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5100_);
lean_ctor_set(v___x_5101_, 1, v___f_5083_);
v___x_5102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5102_, 0, v_a_5095_);
lean_ctor_set(v___x_5102_, 1, v___f_5083_);
v___x_5103_ = lean_unsigned_to_nat(3u);
v___x_5104_ = lean_mk_empty_array_with_capacity(v___x_5103_);
v___x_5105_ = lean_array_push(v___x_5104_, v___x_5099_);
v___x_5106_ = lean_array_push(v___x_5105_, v___x_5101_);
v___x_5107_ = lean_array_push(v___x_5106_, v___x_5102_);
v___x_5108_ = l_Std_Async_Selectable_one___redArg(v___x_5107_);
return v___x_5108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5___boxed(lean_object* v_connectionContext_5109_, lean_object* v_recvSelector_5110_, lean_object* v_socket_5111_, lean_object* v_readSize_5112_, lean_object* v___f_5113_, lean_object* v___f_5114_, lean_object* v_x_5115_, lean_object* v___y_5116_){
_start:
{
uint64_t v_readSize_boxed_5117_; lean_object* v_res_5118_; 
v_readSize_boxed_5117_ = lean_unbox_uint64(v_readSize_5112_);
lean_dec_ref(v_readSize_5112_);
v_res_5118_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5(v_connectionContext_5109_, v_recvSelector_5110_, v_socket_5111_, v_readSize_boxed_5117_, v___f_5113_, v___f_5114_, v_x_5115_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4(lean_object* v___x_5119_, uint8_t v_a_5120_, lean_object* v_connectionContext_5121_, lean_object* v_recvSelector_5122_, lean_object* v_socket_5123_, uint64_t v_readSize_5124_, lean_object* v___f_5125_, lean_object* v___x_5126_, lean_object* v_x_5127_){
_start:
{
if (lean_obj_tag(v_x_5127_) == 0)
{
lean_object* v_a_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5137_; 
lean_dec_ref(v___f_5125_);
lean_dec(v_socket_5123_);
lean_dec_ref(v_recvSelector_5122_);
lean_dec_ref(v_connectionContext_5121_);
v_a_5129_ = lean_ctor_get(v_x_5127_, 0);
v_isSharedCheck_5137_ = !lean_is_exclusive(v_x_5127_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5131_ = v_x_5127_;
v_isShared_5132_ = v_isSharedCheck_5137_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_a_5129_);
lean_dec(v_x_5127_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5137_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5134_; 
if (v_isShared_5132_ == 0)
{
v___x_5134_ = v___x_5131_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_a_5129_);
v___x_5134_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
lean_object* v___x_5135_; 
v___x_5135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5135_, 0, v___x_5134_);
return v___x_5135_;
}
}
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5164_; 
v_a_5138_ = lean_ctor_get(v_x_5127_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v_x_5127_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5140_ = v_x_5127_;
v_isShared_5141_ = v_isSharedCheck_5164_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v_x_5127_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5164_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
uint8_t v___x_5142_; 
v___x_5142_ = lean_nat_dec_le(v___x_5119_, v_a_5138_);
if (v___x_5142_ == 0)
{
lean_object* v___x_5143_; lean_object* v___f_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___f_5147_; lean_object* v___x_5148_; lean_object* v___f_5149_; lean_object* v___x_5150_; lean_object* v___f_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; 
lean_del_object(v___x_5140_);
v___x_5143_ = lean_box(v___x_5142_);
v___f_5144_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5144_, 0, v___x_5143_);
v___x_5145_ = lean_box(v___x_5142_);
v___x_5146_ = lean_box(v_a_5120_);
v___f_5147_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_5147_, 0, v___x_5145_);
lean_closure_set(v___f_5147_, 1, v___x_5146_);
v___x_5148_ = lean_box(v___x_5142_);
v___f_5149_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_5149_, 0, v___x_5148_);
v___x_5150_ = lean_box_uint64(v_readSize_5124_);
v___f_5151_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_5151_, 0, v_connectionContext_5121_);
lean_closure_set(v___f_5151_, 1, v_recvSelector_5122_);
lean_closure_set(v___f_5151_, 2, v_socket_5123_);
lean_closure_set(v___f_5151_, 3, v___x_5150_);
lean_closure_set(v___f_5151_, 4, v___f_5147_);
lean_closure_set(v___f_5151_, 5, v___f_5149_);
v___x_5152_ = lean_nat_sub(v___x_5119_, v_a_5138_);
lean_dec(v_a_5138_);
v___x_5153_ = lean_nat_to_int(v___x_5152_);
v___x_5154_ = lean_unsigned_to_nat(0u);
v___x_5155_ = l_Std_Async_Selector_sleep(v___x_5153_);
lean_dec(v___x_5153_);
v___x_5156_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5154_, v___x_5142_, v___x_5155_, v___f_5151_);
v___x_5157_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5154_, v___x_5142_, v___x_5156_, v___f_5144_);
v___x_5158_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5154_, v___x_5142_, v___x_5157_, v___f_5125_);
return v___x_5158_;
}
else
{
lean_object* v___x_5159_; lean_object* v___x_5161_; 
lean_dec(v_a_5138_);
lean_dec_ref(v___f_5125_);
lean_dec(v_socket_5123_);
lean_dec_ref(v_recvSelector_5122_);
lean_dec_ref(v_connectionContext_5121_);
v___x_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5159_, 0, v___x_5126_);
if (v_isShared_5141_ == 0)
{
lean_ctor_set(v___x_5140_, 0, v___x_5159_);
v___x_5161_ = v___x_5140_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v___x_5159_);
v___x_5161_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
lean_object* v___x_5162_; 
v___x_5162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5161_);
return v___x_5162_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4___boxed(lean_object* v___x_5165_, lean_object* v_a_5166_, lean_object* v_connectionContext_5167_, lean_object* v_recvSelector_5168_, lean_object* v_socket_5169_, lean_object* v_readSize_5170_, lean_object* v___f_5171_, lean_object* v___x_5172_, lean_object* v_x_5173_, lean_object* v___y_5174_){
_start:
{
uint8_t v_a_2587__boxed_5175_; uint64_t v_readSize_boxed_5176_; lean_object* v_res_5177_; 
v_a_2587__boxed_5175_ = lean_unbox(v_a_5166_);
v_readSize_boxed_5176_ = lean_unbox_uint64(v_readSize_5170_);
lean_dec_ref(v_readSize_5170_);
v_res_5177_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4(v___x_5165_, v_a_2587__boxed_5175_, v_connectionContext_5167_, v_recvSelector_5168_, v_socket_5169_, v_readSize_boxed_5176_, v___f_5171_, v___x_5172_, v_x_5173_);
lean_dec(v___x_5165_);
return v_res_5177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6(lean_object* v___f_5178_, lean_object* v_x_5179_, lean_object* v_____s_5180_){
_start:
{
lean_object* v___x_5182_; uint8_t v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; 
v___x_5182_ = lean_unsigned_to_nat(0u);
v___x_5183_ = 0;
v___x_5184_ = lean_io_mono_ms_now();
v___x_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5185_, 0, v___x_5184_);
v___x_5186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5185_);
v___x_5187_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5182_, v___x_5183_, v___x_5186_, v___f_5178_);
return v___x_5187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6___boxed(lean_object* v___f_5188_, lean_object* v_x_5189_, lean_object* v_____s_5190_, lean_object* v___y_5191_){
_start:
{
lean_object* v_res_5192_; 
v_res_5192_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6(v___f_5188_, v_x_5189_, v_____s_5190_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7(lean_object* v_a_5193_, lean_object* v_x_5194_){
_start:
{
if (lean_obj_tag(v_x_5194_) == 0)
{
lean_object* v___x_5196_; 
v___x_5196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5196_, 0, v_x_5194_);
return v___x_5196_;
}
else
{
lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5204_; 
v_isSharedCheck_5204_ = !lean_is_exclusive(v_x_5194_);
if (v_isSharedCheck_5204_ == 0)
{
lean_object* v_unused_5205_; 
v_unused_5205_ = lean_ctor_get(v_x_5194_, 0);
lean_dec(v_unused_5205_);
v___x_5198_ = v_x_5194_;
v_isShared_5199_ = v_isSharedCheck_5204_;
goto v_resetjp_5197_;
}
else
{
lean_dec(v_x_5194_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5204_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5200_; lean_object* v___x_5202_; 
v___x_5200_ = l_IO_Promise_result_x21___redArg(v_a_5193_);
if (v_isShared_5199_ == 0)
{
lean_ctor_set(v___x_5198_, 0, v___x_5200_);
v___x_5202_ = v___x_5198_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v___x_5200_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7___boxed(lean_object* v_a_5206_, lean_object* v_x_5207_, lean_object* v___y_5208_){
_start:
{
lean_object* v_res_5209_; 
v_res_5209_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7(v_a_5206_, v_x_5207_);
lean_dec(v_a_5206_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8(lean_object* v___f_5210_, lean_object* v___x_5211_, lean_object* v___x_5212_, uint8_t v___x_5213_, lean_object* v_x_5214_){
_start:
{
if (lean_obj_tag(v_x_5214_) == 0)
{
lean_object* v_a_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5224_; 
lean_dec(v___x_5211_);
lean_dec_ref(v___f_5210_);
v_a_5216_ = lean_ctor_get(v_x_5214_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v_x_5214_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5218_ = v_x_5214_;
v_isShared_5219_ = v_isSharedCheck_5224_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_a_5216_);
lean_dec(v_x_5214_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5224_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v___x_5221_; 
if (v_isShared_5219_ == 0)
{
v___x_5221_ = v___x_5218_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5216_);
v___x_5221_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
lean_object* v___x_5222_; 
v___x_5222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5221_);
return v___x_5222_;
}
}
}
else
{
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5236_; 
v_a_5225_ = lean_ctor_get(v_x_5214_, 0);
v_isSharedCheck_5236_ = !lean_is_exclusive(v_x_5214_);
if (v_isSharedCheck_5236_ == 0)
{
v___x_5227_ = v_x_5214_;
v_isShared_5228_ = v_isSharedCheck_5236_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v_x_5214_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5236_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___f_5229_; lean_object* v___x_5230_; lean_object* v___x_5232_; 
lean_inc(v_a_5225_);
v___f_5229_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_5229_, 0, v_a_5225_);
lean_inc(v___x_5211_);
v___x_5230_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_5210_, v___x_5211_, v_a_5225_, v___x_5212_);
if (v_isShared_5228_ == 0)
{
lean_ctor_set(v___x_5227_, 0, v___x_5230_);
v___x_5232_ = v___x_5227_;
goto v_reusejp_5231_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v___x_5230_);
v___x_5232_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5231_;
}
v_reusejp_5231_:
{
lean_object* v___x_5233_; lean_object* v___x_5234_; 
v___x_5233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5233_, 0, v___x_5232_);
v___x_5234_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5211_, v___x_5213_, v___x_5233_, v___f_5229_);
return v___x_5234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8___boxed(lean_object* v___f_5237_, lean_object* v___x_5238_, lean_object* v___x_5239_, lean_object* v___x_5240_, lean_object* v_x_5241_, lean_object* v___y_5242_){
_start:
{
uint8_t v___x_2734__boxed_5243_; lean_object* v_res_5244_; 
v___x_2734__boxed_5243_ = lean_unbox(v___x_5240_);
v_res_5244_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8(v___f_5237_, v___x_5238_, v___x_5239_, v___x_2734__boxed_5243_, v_x_5241_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9(lean_object* v_timeout_5247_, uint8_t v_a_5248_, lean_object* v_connectionContext_5249_, lean_object* v_recvSelector_5250_, lean_object* v_socket_5251_, uint64_t v_readSize_5252_, lean_object* v___f_5253_, lean_object* v_x_5254_){
_start:
{
if (lean_obj_tag(v_x_5254_) == 0)
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5264_; 
lean_dec_ref(v___f_5253_);
lean_dec(v_socket_5251_);
lean_dec_ref(v_recvSelector_5250_);
lean_dec_ref(v_connectionContext_5249_);
v_a_5256_ = lean_ctor_get(v_x_5254_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v_x_5254_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5258_ = v_x_5254_;
v_isShared_5259_ = v_isSharedCheck_5264_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v_x_5254_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5264_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5261_; 
if (v_isShared_5259_ == 0)
{
v___x_5261_ = v___x_5258_;
goto v_reusejp_5260_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_a_5256_);
v___x_5261_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5260_;
}
v_reusejp_5260_:
{
lean_object* v___x_5262_; 
v___x_5262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5262_, 0, v___x_5261_);
return v___x_5262_;
}
}
}
else
{
lean_object* v_a_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5288_; 
v_a_5265_ = lean_ctor_get(v_x_5254_, 0);
v_isSharedCheck_5288_ = !lean_is_exclusive(v_x_5254_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5267_ = v_x_5254_;
v_isShared_5268_ = v_isSharedCheck_5288_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_a_5265_);
lean_dec(v_x_5254_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5288_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___f_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___f_5275_; lean_object* v___f_5276_; lean_object* v___x_5277_; uint8_t v___x_5278_; lean_object* v___x_5279_; lean_object* v___f_5280_; lean_object* v___x_5281_; lean_object* v___x_5283_; 
v___x_5269_ = l_Int_toNat(v_timeout_5247_);
v___x_5270_ = lean_nat_add(v_a_5265_, v___x_5269_);
lean_dec(v___x_5269_);
lean_dec(v_a_5265_);
v___x_5271_ = lean_box(0);
v___f_5272_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___closed__0));
v___x_5273_ = lean_box(v_a_5248_);
v___x_5274_ = lean_box_uint64(v_readSize_5252_);
v___f_5275_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_5275_, 0, v___x_5270_);
lean_closure_set(v___f_5275_, 1, v___x_5273_);
lean_closure_set(v___f_5275_, 2, v_connectionContext_5249_);
lean_closure_set(v___f_5275_, 3, v_recvSelector_5250_);
lean_closure_set(v___f_5275_, 4, v_socket_5251_);
lean_closure_set(v___f_5275_, 5, v___x_5274_);
lean_closure_set(v___f_5275_, 6, v___f_5272_);
lean_closure_set(v___f_5275_, 7, v___x_5271_);
v___f_5276_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6___boxed), 4, 1);
lean_closure_set(v___f_5276_, 0, v___f_5275_);
v___x_5277_ = lean_unsigned_to_nat(0u);
v___x_5278_ = 0;
v___x_5279_ = lean_box(v___x_5278_);
v___f_5280_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_5280_, 0, v___f_5276_);
lean_closure_set(v___f_5280_, 1, v___x_5277_);
lean_closure_set(v___f_5280_, 2, v___x_5271_);
lean_closure_set(v___f_5280_, 3, v___x_5279_);
v___x_5281_ = lean_io_promise_new();
if (v_isShared_5268_ == 0)
{
lean_ctor_set(v___x_5267_, 0, v___x_5281_);
v___x_5283_ = v___x_5267_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v___x_5281_);
v___x_5283_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; 
v___x_5284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5284_, 0, v___x_5283_);
v___x_5285_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5277_, v___x_5278_, v___x_5284_, v___f_5280_);
v___x_5286_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5277_, v___x_5278_, v___x_5285_, v___f_5253_);
return v___x_5286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___boxed(lean_object* v_timeout_5289_, lean_object* v_a_5290_, lean_object* v_connectionContext_5291_, lean_object* v_recvSelector_5292_, lean_object* v_socket_5293_, lean_object* v_readSize_5294_, lean_object* v___f_5295_, lean_object* v_x_5296_, lean_object* v___y_5297_){
_start:
{
uint8_t v_a_2795__boxed_5298_; uint64_t v_readSize_boxed_5299_; lean_object* v_res_5300_; 
v_a_2795__boxed_5298_ = lean_unbox(v_a_5290_);
v_readSize_boxed_5299_ = lean_unbox_uint64(v_readSize_5294_);
lean_dec_ref(v_readSize_5294_);
v_res_5300_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9(v_timeout_5289_, v_a_2795__boxed_5298_, v_connectionContext_5291_, v_recvSelector_5292_, v_socket_5293_, v_readSize_boxed_5299_, v___f_5295_, v_x_5296_);
lean_dec(v_timeout_5289_);
return v_res_5300_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10(lean_object* v_timeout_5301_, lean_object* v_connectionContext_5302_, lean_object* v_recvSelector_5303_, lean_object* v_socket_5304_, uint64_t v_readSize_5305_, lean_object* v___f_5306_, lean_object* v_x_5307_){
_start:
{
if (lean_obj_tag(v_x_5307_) == 0)
{
lean_object* v_a_5309_; lean_object* v___x_5311_; uint8_t v_isShared_5312_; uint8_t v_isSharedCheck_5317_; 
lean_dec_ref(v___f_5306_);
lean_dec(v_socket_5304_);
lean_dec_ref(v_recvSelector_5303_);
lean_dec_ref(v_connectionContext_5302_);
lean_dec(v_timeout_5301_);
v_a_5309_ = lean_ctor_get(v_x_5307_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v_x_5307_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5311_ = v_x_5307_;
v_isShared_5312_ = v_isSharedCheck_5317_;
goto v_resetjp_5310_;
}
else
{
lean_inc(v_a_5309_);
lean_dec(v_x_5307_);
v___x_5311_ = lean_box(0);
v_isShared_5312_ = v_isSharedCheck_5317_;
goto v_resetjp_5310_;
}
v_resetjp_5310_:
{
lean_object* v___x_5314_; 
if (v_isShared_5312_ == 0)
{
v___x_5314_ = v___x_5311_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5309_);
v___x_5314_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
lean_object* v___x_5315_; 
v___x_5315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5315_, 0, v___x_5314_);
return v___x_5315_;
}
}
}
else
{
lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5334_; 
v_a_5318_ = lean_ctor_get(v_x_5307_, 0);
v_isSharedCheck_5334_ = !lean_is_exclusive(v_x_5307_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5320_ = v_x_5307_;
v_isShared_5321_ = v_isSharedCheck_5334_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v_x_5307_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5334_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
uint8_t v___x_5322_; 
v___x_5322_ = lean_unbox(v_a_5318_);
if (v___x_5322_ == 0)
{
lean_object* v___x_5323_; 
lean_del_object(v___x_5320_);
lean_dec(v_a_5318_);
lean_dec_ref(v___f_5306_);
lean_dec(v_socket_5304_);
lean_dec_ref(v_recvSelector_5303_);
lean_dec_ref(v_connectionContext_5302_);
lean_dec(v_timeout_5301_);
v___x_5323_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_5323_;
}
else
{
lean_object* v___x_5324_; lean_object* v___f_5325_; lean_object* v___x_5326_; uint8_t v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5330_; 
v___x_5324_ = lean_box_uint64(v_readSize_5305_);
v___f_5325_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___boxed), 9, 7);
lean_closure_set(v___f_5325_, 0, v_timeout_5301_);
lean_closure_set(v___f_5325_, 1, v_a_5318_);
lean_closure_set(v___f_5325_, 2, v_connectionContext_5302_);
lean_closure_set(v___f_5325_, 3, v_recvSelector_5303_);
lean_closure_set(v___f_5325_, 4, v_socket_5304_);
lean_closure_set(v___f_5325_, 5, v___x_5324_);
lean_closure_set(v___f_5325_, 6, v___f_5306_);
v___x_5326_ = lean_unsigned_to_nat(0u);
v___x_5327_ = 0;
v___x_5328_ = lean_io_mono_ms_now();
if (v_isShared_5321_ == 0)
{
lean_ctor_set(v___x_5320_, 0, v___x_5328_);
v___x_5330_ = v___x_5320_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v___x_5328_);
v___x_5330_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
lean_object* v___x_5331_; lean_object* v___x_5332_; 
v___x_5331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5331_, 0, v___x_5330_);
v___x_5332_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5326_, v___x_5327_, v___x_5331_, v___f_5325_);
return v___x_5332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10___boxed(lean_object* v_timeout_5335_, lean_object* v_connectionContext_5336_, lean_object* v_recvSelector_5337_, lean_object* v_socket_5338_, lean_object* v_readSize_5339_, lean_object* v___f_5340_, lean_object* v_x_5341_, lean_object* v___y_5342_){
_start:
{
uint64_t v_readSize_boxed_5343_; lean_object* v_res_5344_; 
v_readSize_boxed_5343_ = lean_unbox_uint64(v_readSize_5339_);
lean_dec_ref(v_readSize_5339_);
v_res_5344_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10(v_timeout_5335_, v_connectionContext_5336_, v_recvSelector_5337_, v_socket_5338_, v_readSize_boxed_5343_, v___f_5340_, v_x_5341_);
return v_res_5344_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11(lean_object* v_x_5350_){
_start:
{
if (lean_obj_tag(v_x_5350_) == 0)
{
lean_object* v___x_5352_; 
lean_dec_ref_known(v_x_5350_, 1);
v___x_5352_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___closed__1));
return v___x_5352_;
}
else
{
lean_object* v___x_5353_; 
v___x_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5353_, 0, v_x_5350_);
return v___x_5353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___boxed(lean_object* v_x_5354_, lean_object* v___y_5355_){
_start:
{
lean_object* v_res_5356_; 
v_res_5356_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11(v_x_5354_);
return v_res_5356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(lean_object* v_inst_5359_, lean_object* v_socket_5360_, lean_object* v_timeout_5361_, uint64_t v_readSize_5362_, lean_object* v_connectionContext_5363_){
_start:
{
lean_object* v_recvSelector_5365_; lean_object* v_shutdown_5366_; lean_object* v___f_5367_; lean_object* v___x_5368_; lean_object* v___f_5369_; lean_object* v___f_5370_; lean_object* v___x_5371_; uint8_t v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; 
v_recvSelector_5365_ = lean_ctor_get(v_inst_5359_, 2);
lean_inc_ref(v_recvSelector_5365_);
v_shutdown_5366_ = lean_ctor_get(v_inst_5359_, 4);
lean_inc_ref(v_shutdown_5366_);
lean_dec_ref(v_inst_5359_);
v___f_5367_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___closed__0));
v___x_5368_ = lean_box_uint64(v_readSize_5362_);
lean_inc(v_socket_5360_);
v___f_5369_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_5369_, 0, v_timeout_5361_);
lean_closure_set(v___f_5369_, 1, v_connectionContext_5363_);
lean_closure_set(v___f_5369_, 2, v_recvSelector_5365_);
lean_closure_set(v___f_5369_, 3, v_socket_5360_);
lean_closure_set(v___f_5369_, 4, v___x_5368_);
lean_closure_set(v___f_5369_, 5, v___f_5367_);
v___f_5370_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___closed__1));
v___x_5371_ = lean_unsigned_to_nat(0u);
v___x_5372_ = 0;
v___x_5373_ = lean_apply_2(v_shutdown_5366_, v_socket_5360_, lean_box(0));
v___x_5374_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5371_, v___x_5372_, v___x_5373_, v___f_5370_);
v___x_5375_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5371_, v___x_5372_, v___x_5374_, v___f_5369_);
return v___x_5375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___boxed(lean_object* v_inst_5376_, lean_object* v_socket_5377_, lean_object* v_timeout_5378_, lean_object* v_readSize_5379_, lean_object* v_connectionContext_5380_, lean_object* v_a_5381_){
_start:
{
uint64_t v_readSize_boxed_5382_; lean_object* v_res_5383_; 
v_readSize_boxed_5382_ = lean_unbox_uint64(v_readSize_5379_);
lean_dec_ref(v_readSize_5379_);
v_res_5383_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(v_inst_5376_, v_socket_5377_, v_timeout_5378_, v_readSize_boxed_5382_, v_connectionContext_5380_);
return v_res_5383_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger(lean_object* v_00_u03b1_5384_, lean_object* v_inst_5385_, lean_object* v_socket_5386_, lean_object* v_timeout_5387_, uint64_t v_readSize_5388_, lean_object* v_connectionContext_5389_){
_start:
{
lean_object* v___x_5391_; 
v___x_5391_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(v_inst_5385_, v_socket_5386_, v_timeout_5387_, v_readSize_5388_, v_connectionContext_5389_);
return v___x_5391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___boxed(lean_object* v_00_u03b1_5392_, lean_object* v_inst_5393_, lean_object* v_socket_5394_, lean_object* v_timeout_5395_, lean_object* v_readSize_5396_, lean_object* v_connectionContext_5397_, lean_object* v_a_5398_){
_start:
{
uint64_t v_readSize_boxed_5399_; lean_object* v_res_5400_; 
v_readSize_boxed_5399_ = lean_unbox_uint64(v_readSize_5396_);
lean_dec_ref(v_readSize_5396_);
v_res_5400_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger(v_00_u03b1_5392_, v_inst_5393_, v_socket_5394_, v_timeout_5395_, v_readSize_boxed_5399_, v_connectionContext_5397_);
return v_res_5400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_x_5401_){
_start:
{
lean_object* v_fst_5402_; 
v_fst_5402_ = lean_ctor_get(v_x_5401_, 0);
lean_inc(v_fst_5402_);
return v_fst_5402_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_x_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_x_5403_);
lean_dec_ref(v_x_5403_);
return v_res_5404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_x_5405_){
_start:
{
if (lean_obj_tag(v_x_5405_) == 0)
{
lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5415_; 
v_a_5407_ = lean_ctor_get(v_x_5405_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v_x_5405_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5409_ = v_x_5405_;
v_isShared_5410_ = v_isSharedCheck_5415_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v_x_5405_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5415_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5412_; 
if (v_isShared_5410_ == 0)
{
v___x_5412_ = v___x_5409_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5407_);
v___x_5412_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
lean_object* v___x_5413_; 
v___x_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5413_, 0, v___x_5412_);
return v___x_5413_;
}
}
}
else
{
lean_object* v_a_5416_; lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5434_; 
v_a_5416_ = lean_ctor_get(v_x_5405_, 0);
v_isSharedCheck_5434_ = !lean_is_exclusive(v_x_5405_);
if (v_isSharedCheck_5434_ == 0)
{
v___x_5418_ = v_x_5405_;
v_isShared_5419_ = v_isSharedCheck_5434_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_a_5416_);
lean_dec(v_x_5405_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5434_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v_snd_5420_; uint8_t v___x_5421_; 
v_snd_5420_ = lean_ctor_get(v_a_5416_, 1);
v___x_5421_ = lean_unbox(v_snd_5420_);
if (v___x_5421_ == 0)
{
lean_object* v_fst_5422_; lean_object* v___x_5423_; lean_object* v___x_5425_; 
v_fst_5422_ = lean_ctor_get(v_a_5416_, 0);
lean_inc(v_fst_5422_);
lean_dec(v_a_5416_);
v___x_5423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5423_, 0, v_fst_5422_);
if (v_isShared_5419_ == 0)
{
lean_ctor_set(v___x_5418_, 0, v___x_5423_);
v___x_5425_ = v___x_5418_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v___x_5423_);
v___x_5425_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
lean_object* v___x_5426_; 
v___x_5426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5426_, 0, v___x_5425_);
return v___x_5426_;
}
}
else
{
lean_object* v_fst_5428_; lean_object* v___x_5429_; lean_object* v___x_5431_; 
v_fst_5428_ = lean_ctor_get(v_a_5416_, 0);
lean_inc(v_fst_5428_);
lean_dec(v_a_5416_);
v___x_5429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5429_, 0, v_fst_5428_);
if (v_isShared_5419_ == 0)
{
lean_ctor_set(v___x_5418_, 0, v___x_5429_);
v___x_5431_ = v___x_5418_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v___x_5429_);
v___x_5431_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
lean_object* v___x_5432_; 
v___x_5432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5431_);
return v___x_5432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_x_5435_, lean_object* v___y_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_x_5435_);
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_responseBodyInstance_5438_, lean_object* v_____do__lift_5439_){
_start:
{
if (lean_obj_tag(v_____do__lift_5439_) == 1)
{
lean_object* v_a_5441_; lean_object* v_close_5442_; lean_object* v_body_5443_; lean_object* v___x_5444_; 
v_a_5441_ = lean_ctor_get(v_____do__lift_5439_, 0);
lean_inc(v_a_5441_);
lean_dec_ref_known(v_____do__lift_5439_, 1);
v_close_5442_ = lean_ctor_get(v_responseBodyInstance_5438_, 1);
lean_inc_ref(v_close_5442_);
lean_dec_ref(v_responseBodyInstance_5438_);
v_body_5443_ = lean_ctor_get(v_a_5441_, 1);
lean_inc(v_body_5443_);
lean_dec(v_a_5441_);
v___x_5444_ = lean_apply_2(v_close_5442_, v_body_5443_, lean_box(0));
return v___x_5444_;
}
else
{
lean_object* v___x_5445_; 
lean_dec_ref(v_____do__lift_5439_);
lean_dec_ref(v_responseBodyInstance_5438_);
v___x_5445_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_5445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_responseBodyInstance_5446_, lean_object* v_____do__lift_5447_, lean_object* v___y_5448_){
_start:
{
lean_object* v_res_5449_; 
v_res_5449_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_responseBodyInstance_5446_, v_____do__lift_5447_);
return v_res_5449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(lean_object* v_h_5450_, lean_object* v_responseBodyInstance_5451_, lean_object* v_handler_5452_, lean_object* v_config_5453_, lean_object* v_a_5454_, uint8_t v___x_5455_, lean_object* v___f_5456_, lean_object* v_____r_5457_, lean_object* v_state_5458_){
_start:
{
lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; 
v___x_5460_ = lean_unsigned_to_nat(0u);
v___x_5461_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_5450_, v_responseBodyInstance_5451_, v_handler_5452_, v_config_5453_, v_a_5454_, v_state_5458_);
v___x_5462_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5460_, v___x_5455_, v___x_5461_, v___f_5456_);
return v___x_5462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed(lean_object* v_h_5463_, lean_object* v_responseBodyInstance_5464_, lean_object* v_handler_5465_, lean_object* v_config_5466_, lean_object* v_a_5467_, lean_object* v___x_5468_, lean_object* v___f_5469_, lean_object* v_____r_5470_, lean_object* v_state_5471_, lean_object* v___y_5472_){
_start:
{
uint8_t v___x_8850__boxed_5473_; lean_object* v_res_5474_; 
v___x_8850__boxed_5473_ = lean_unbox(v___x_5468_);
v_res_5474_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_h_5463_, v_responseBodyInstance_5464_, v_handler_5465_, v_config_5466_, v_a_5467_, v___x_8850__boxed_5473_, v___f_5469_, v_____r_5470_, v_state_5471_);
return v_res_5474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(lean_object* v_a_5475_, uint8_t v___x_5476_, lean_object* v___f_5477_, lean_object* v_keepAliveTimeout_5478_, lean_object* v___f_5479_, lean_object* v___x_5480_, lean_object* v_machine_5481_, lean_object* v_requestStream_5482_, lean_object* v_keepAliveTimeout_5483_, lean_object* v_headerTimeout_5484_, lean_object* v_response_5485_, lean_object* v_respStream_5486_, lean_object* v_expectData_5487_, uint8_t v_handlerDispatched_5488_, lean_object* v_pendingHead_5489_, uint8_t v_requestFinalOffered_5490_, lean_object* v_handlerTask_5491_, lean_object* v_dateSecond_5492_, uint8_t v_peerClosed_5493_, uint8_t v_requestEnded_5494_, lean_object* v_x_5495_){
_start:
{
if (lean_obj_tag(v_x_5495_) == 0)
{
lean_object* v_a_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5505_; 
lean_dec(v_dateSecond_5492_);
lean_dec(v_handlerTask_5491_);
lean_dec(v_pendingHead_5489_);
lean_dec(v_expectData_5487_);
lean_dec(v_respStream_5486_);
lean_dec_ref(v_response_5485_);
lean_dec(v_headerTimeout_5484_);
lean_dec(v_keepAliveTimeout_5483_);
lean_dec_ref(v_requestStream_5482_);
lean_dec_ref(v_machine_5481_);
lean_dec_ref(v___x_5480_);
lean_dec_ref(v___f_5479_);
lean_dec_ref(v___f_5477_);
lean_dec_ref(v_a_5475_);
v_a_5497_ = lean_ctor_get(v_x_5495_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v_x_5495_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5499_ = v_x_5495_;
v_isShared_5500_ = v_isSharedCheck_5505_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_a_5497_);
lean_dec(v_x_5495_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5505_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v___x_5502_; 
if (v_isShared_5500_ == 0)
{
v___x_5502_ = v___x_5499_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_a_5497_);
v___x_5502_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
lean_object* v___x_5503_; 
v___x_5503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5503_, 0, v___x_5502_);
return v___x_5503_;
}
}
}
else
{
lean_object* v_a_5506_; lean_object* v___x_5508_; uint8_t v_isShared_5509_; uint8_t v_isSharedCheck_5532_; 
v_a_5506_ = lean_ctor_get(v_x_5495_, 0);
v_isSharedCheck_5532_ = !lean_is_exclusive(v_x_5495_);
if (v_isSharedCheck_5532_ == 0)
{
v___x_5508_ = v_x_5495_;
v_isShared_5509_ = v_isSharedCheck_5532_;
goto v_resetjp_5507_;
}
else
{
lean_inc(v_a_5506_);
lean_dec(v_x_5495_);
v___x_5508_ = lean_box(0);
v_isShared_5509_ = v_isSharedCheck_5532_;
goto v_resetjp_5507_;
}
v_resetjp_5507_:
{
if (lean_obj_tag(v_a_5506_) == 0)
{
lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; 
lean_del_object(v___x_5508_);
lean_dec(v_dateSecond_5492_);
lean_dec(v_handlerTask_5491_);
lean_dec(v_pendingHead_5489_);
lean_dec(v_expectData_5487_);
lean_dec(v_respStream_5486_);
lean_dec_ref(v_response_5485_);
lean_dec(v_headerTimeout_5484_);
lean_dec(v_keepAliveTimeout_5483_);
lean_dec_ref(v_requestStream_5482_);
lean_dec_ref(v_machine_5481_);
lean_dec_ref(v___x_5480_);
lean_dec_ref(v___f_5479_);
v___x_5510_ = lean_unsigned_to_nat(0u);
v___x_5511_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_a_5475_);
v___x_5512_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5510_, v___x_5476_, v___x_5511_, v___f_5477_);
return v___x_5512_;
}
else
{
lean_object* v_val_5513_; lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5531_; 
lean_dec_ref(v___f_5477_);
lean_dec_ref(v_a_5475_);
v_val_5513_ = lean_ctor_get(v_a_5506_, 0);
v_isSharedCheck_5531_ = !lean_is_exclusive(v_a_5506_);
if (v_isSharedCheck_5531_ == 0)
{
v___x_5515_ = v_a_5506_;
v_isShared_5516_ = v_isSharedCheck_5531_;
goto v_resetjp_5514_;
}
else
{
lean_inc(v_val_5513_);
lean_dec(v_a_5506_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5531_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; uint8_t v___x_5520_; 
v___x_5517_ = lean_nat_to_int(v_val_5513_);
v___x_5518_ = lean_int_sub(v_keepAliveTimeout_5478_, v___x_5517_);
lean_dec(v___x_5517_);
v___x_5519_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0);
v___x_5520_ = lean_int_dec_lt(v___x_5519_, v___x_5518_);
if (v___x_5520_ == 0)
{
lean_object* v___x_5521_; lean_object* v___x_5522_; 
lean_dec(v___x_5518_);
lean_del_object(v___x_5515_);
lean_del_object(v___x_5508_);
lean_dec(v_dateSecond_5492_);
lean_dec(v_handlerTask_5491_);
lean_dec(v_pendingHead_5489_);
lean_dec(v_expectData_5487_);
lean_dec(v_respStream_5486_);
lean_dec_ref(v_response_5485_);
lean_dec(v_headerTimeout_5484_);
lean_dec(v_keepAliveTimeout_5483_);
lean_dec_ref(v_requestStream_5482_);
lean_dec_ref(v_machine_5481_);
v___x_5521_ = lean_box(0);
v___x_5522_ = lean_apply_3(v___f_5479_, v___x_5521_, v___x_5480_, lean_box(0));
return v___x_5522_;
}
else
{
lean_object* v___x_5523_; lean_object* v___x_5525_; 
lean_dec_ref(v___x_5480_);
lean_dec_ref(v___f_5479_);
v___x_5523_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v___x_5523_, 0, v_machine_5481_);
lean_ctor_set(v___x_5523_, 1, v_requestStream_5482_);
lean_ctor_set(v___x_5523_, 2, v_keepAliveTimeout_5483_);
lean_ctor_set(v___x_5523_, 3, v___x_5518_);
lean_ctor_set(v___x_5523_, 4, v_headerTimeout_5484_);
lean_ctor_set(v___x_5523_, 5, v_response_5485_);
lean_ctor_set(v___x_5523_, 6, v_respStream_5486_);
lean_ctor_set(v___x_5523_, 7, v_expectData_5487_);
lean_ctor_set(v___x_5523_, 8, v_pendingHead_5489_);
lean_ctor_set(v___x_5523_, 9, v_handlerTask_5491_);
lean_ctor_set(v___x_5523_, 10, v_dateSecond_5492_);
lean_ctor_set_uint8(v___x_5523_, sizeof(void*)*11, v___x_5476_);
lean_ctor_set_uint8(v___x_5523_, sizeof(void*)*11 + 1, v_handlerDispatched_5488_);
lean_ctor_set_uint8(v___x_5523_, sizeof(void*)*11 + 2, v_requestFinalOffered_5490_);
lean_ctor_set_uint8(v___x_5523_, sizeof(void*)*11 + 3, v_peerClosed_5493_);
lean_ctor_set_uint8(v___x_5523_, sizeof(void*)*11 + 4, v_requestEnded_5494_);
if (v_isShared_5516_ == 0)
{
lean_ctor_set(v___x_5515_, 0, v___x_5523_);
v___x_5525_ = v___x_5515_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5523_);
v___x_5525_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
lean_object* v___x_5527_; 
if (v_isShared_5509_ == 0)
{
lean_ctor_set(v___x_5508_, 0, v___x_5525_);
v___x_5527_ = v___x_5508_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5525_);
v___x_5527_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
lean_object* v___x_5528_; 
v___x_5528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5528_, 0, v___x_5527_);
return v___x_5528_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_a_5533_ = _args[0];
lean_object* v___x_5534_ = _args[1];
lean_object* v___f_5535_ = _args[2];
lean_object* v_keepAliveTimeout_5536_ = _args[3];
lean_object* v___f_5537_ = _args[4];
lean_object* v___x_5538_ = _args[5];
lean_object* v_machine_5539_ = _args[6];
lean_object* v_requestStream_5540_ = _args[7];
lean_object* v_keepAliveTimeout_5541_ = _args[8];
lean_object* v_headerTimeout_5542_ = _args[9];
lean_object* v_response_5543_ = _args[10];
lean_object* v_respStream_5544_ = _args[11];
lean_object* v_expectData_5545_ = _args[12];
lean_object* v_handlerDispatched_5546_ = _args[13];
lean_object* v_pendingHead_5547_ = _args[14];
lean_object* v_requestFinalOffered_5548_ = _args[15];
lean_object* v_handlerTask_5549_ = _args[16];
lean_object* v_dateSecond_5550_ = _args[17];
lean_object* v_peerClosed_5551_ = _args[18];
lean_object* v_requestEnded_5552_ = _args[19];
lean_object* v_x_5553_ = _args[20];
lean_object* v___y_5554_ = _args[21];
_start:
{
uint8_t v___x_8873__boxed_5555_; uint8_t v_handlerDispatched_boxed_5556_; uint8_t v_requestFinalOffered_boxed_5557_; uint8_t v_peerClosed_boxed_5558_; uint8_t v_requestEnded_boxed_5559_; lean_object* v_res_5560_; 
v___x_8873__boxed_5555_ = lean_unbox(v___x_5534_);
v_handlerDispatched_boxed_5556_ = lean_unbox(v_handlerDispatched_5546_);
v_requestFinalOffered_boxed_5557_ = lean_unbox(v_requestFinalOffered_5548_);
v_peerClosed_boxed_5558_ = lean_unbox(v_peerClosed_5551_);
v_requestEnded_boxed_5559_ = lean_unbox(v_requestEnded_5552_);
v_res_5560_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3(v_a_5533_, v___x_8873__boxed_5555_, v___f_5535_, v_keepAliveTimeout_5536_, v___f_5537_, v___x_5538_, v_machine_5539_, v_requestStream_5540_, v_keepAliveTimeout_5541_, v_headerTimeout_5542_, v_response_5543_, v_respStream_5544_, v_expectData_5545_, v_handlerDispatched_boxed_5556_, v_pendingHead_5547_, v_requestFinalOffered_boxed_5557_, v_handlerTask_5549_, v_dateSecond_5550_, v_peerClosed_boxed_5558_, v_requestEnded_boxed_5559_, v_x_5553_);
lean_dec(v_keepAliveTimeout_5536_);
return v_res_5560_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(lean_object* v_h_5561_, lean_object* v_responseBodyInstance_5562_, lean_object* v_handler_5563_, lean_object* v_config_5564_, uint8_t v___x_5565_, lean_object* v___f_5566_, lean_object* v_a_5567_, lean_object* v___f_5568_, lean_object* v_keepAliveTimeout_5569_, lean_object* v___x_5570_, lean_object* v_machine_5571_, lean_object* v_requestStream_5572_, lean_object* v_keepAliveTimeout_5573_, lean_object* v_headerTimeout_5574_, lean_object* v_response_5575_, lean_object* v_respStream_5576_, lean_object* v_expectData_5577_, uint8_t v_handlerDispatched_5578_, lean_object* v_pendingHead_5579_, uint8_t v_requestFinalOffered_5580_, lean_object* v_handlerTask_5581_, lean_object* v_dateSecond_5582_, uint8_t v_peerClosed_5583_, uint8_t v_requestEnded_5584_, lean_object* v_x_5585_){
_start:
{
if (lean_obj_tag(v_x_5585_) == 0)
{
lean_object* v_a_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5595_; 
lean_dec(v_dateSecond_5582_);
lean_dec(v_handlerTask_5581_);
lean_dec(v_pendingHead_5579_);
lean_dec(v_expectData_5577_);
lean_dec(v_respStream_5576_);
lean_dec_ref(v_response_5575_);
lean_dec(v_headerTimeout_5574_);
lean_dec(v_keepAliveTimeout_5573_);
lean_dec_ref(v_requestStream_5572_);
lean_dec_ref(v_machine_5571_);
lean_dec_ref(v___x_5570_);
lean_dec(v_keepAliveTimeout_5569_);
lean_dec_ref(v___f_5568_);
lean_dec_ref(v_a_5567_);
lean_dec_ref(v___f_5566_);
lean_dec_ref(v_config_5564_);
lean_dec(v_handler_5563_);
lean_dec_ref(v_responseBodyInstance_5562_);
lean_dec_ref(v_h_5561_);
v_a_5587_ = lean_ctor_get(v_x_5585_, 0);
v_isSharedCheck_5595_ = !lean_is_exclusive(v_x_5585_);
if (v_isSharedCheck_5595_ == 0)
{
v___x_5589_ = v_x_5585_;
v_isShared_5590_ = v_isSharedCheck_5595_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_a_5587_);
lean_dec(v_x_5585_);
v___x_5589_ = lean_box(0);
v_isShared_5590_ = v_isSharedCheck_5595_;
goto v_resetjp_5588_;
}
v_resetjp_5588_:
{
lean_object* v___x_5592_; 
if (v_isShared_5590_ == 0)
{
v___x_5592_ = v___x_5589_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5587_);
v___x_5592_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
lean_object* v___x_5593_; 
v___x_5593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5593_, 0, v___x_5592_);
return v___x_5593_;
}
}
}
else
{
lean_object* v_a_5596_; lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5617_; 
v_a_5596_ = lean_ctor_get(v_x_5585_, 0);
v_isSharedCheck_5617_ = !lean_is_exclusive(v_x_5585_);
if (v_isSharedCheck_5617_ == 0)
{
v___x_5598_ = v_x_5585_;
v_isShared_5599_ = v_isSharedCheck_5617_;
goto v_resetjp_5597_;
}
else
{
lean_inc(v_a_5596_);
lean_dec(v_x_5585_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5617_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
lean_object* v___x_5600_; lean_object* v___f_5601_; 
v___x_5600_ = lean_box(v___x_5565_);
lean_inc_ref(v___f_5566_);
lean_inc(v_a_5596_);
lean_inc_ref(v_config_5564_);
lean_inc(v_handler_5563_);
lean_inc_ref(v_responseBodyInstance_5562_);
lean_inc_ref(v_h_5561_);
v___f_5601_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4___boxed), 10, 7);
lean_closure_set(v___f_5601_, 0, v_h_5561_);
lean_closure_set(v___f_5601_, 1, v_responseBodyInstance_5562_);
lean_closure_set(v___f_5601_, 2, v_handler_5563_);
lean_closure_set(v___f_5601_, 3, v_config_5564_);
lean_closure_set(v___f_5601_, 4, v_a_5596_);
lean_closure_set(v___f_5601_, 5, v___x_5600_);
lean_closure_set(v___f_5601_, 6, v___f_5566_);
if (lean_obj_tag(v_a_5596_) == 5)
{
lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___f_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5611_; 
lean_dec_ref(v___f_5566_);
lean_dec_ref(v_config_5564_);
lean_dec(v_handler_5563_);
lean_dec_ref(v_responseBodyInstance_5562_);
lean_dec_ref(v_h_5561_);
v___x_5602_ = lean_box(v___x_5565_);
v___x_5603_ = lean_box(v_handlerDispatched_5578_);
v___x_5604_ = lean_box(v_requestFinalOffered_5580_);
v___x_5605_ = lean_box(v_peerClosed_5583_);
v___x_5606_ = lean_box(v_requestEnded_5584_);
lean_inc_ref(v_a_5567_);
v___f_5607_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__3___boxed), 22, 20);
lean_closure_set(v___f_5607_, 0, v_a_5567_);
lean_closure_set(v___f_5607_, 1, v___x_5602_);
lean_closure_set(v___f_5607_, 2, v___f_5568_);
lean_closure_set(v___f_5607_, 3, v_keepAliveTimeout_5569_);
lean_closure_set(v___f_5607_, 4, v___f_5601_);
lean_closure_set(v___f_5607_, 5, v___x_5570_);
lean_closure_set(v___f_5607_, 6, v_machine_5571_);
lean_closure_set(v___f_5607_, 7, v_requestStream_5572_);
lean_closure_set(v___f_5607_, 8, v_keepAliveTimeout_5573_);
lean_closure_set(v___f_5607_, 9, v_headerTimeout_5574_);
lean_closure_set(v___f_5607_, 10, v_response_5575_);
lean_closure_set(v___f_5607_, 11, v_respStream_5576_);
lean_closure_set(v___f_5607_, 12, v_expectData_5577_);
lean_closure_set(v___f_5607_, 13, v___x_5603_);
lean_closure_set(v___f_5607_, 14, v_pendingHead_5579_);
lean_closure_set(v___f_5607_, 15, v___x_5604_);
lean_closure_set(v___f_5607_, 16, v_handlerTask_5581_);
lean_closure_set(v___f_5607_, 17, v_dateSecond_5582_);
lean_closure_set(v___f_5607_, 18, v___x_5605_);
lean_closure_set(v___f_5607_, 19, v___x_5606_);
v___x_5608_ = lean_unsigned_to_nat(0u);
v___x_5609_ = l_Std_Http_Internal_Outbox_idleFor_x3f___redArg(v_a_5567_);
lean_dec_ref(v_a_5567_);
if (v_isShared_5599_ == 0)
{
lean_ctor_set(v___x_5598_, 0, v___x_5609_);
v___x_5611_ = v___x_5598_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v___x_5609_);
v___x_5611_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
lean_object* v___x_5612_; lean_object* v___x_5613_; 
v___x_5612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5612_, 0, v___x_5611_);
v___x_5613_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5608_, v___x_5565_, v___x_5612_, v___f_5607_);
return v___x_5613_;
}
}
else
{
lean_object* v___x_5615_; lean_object* v___x_5616_; 
lean_dec_ref(v___f_5601_);
lean_del_object(v___x_5598_);
lean_dec(v_dateSecond_5582_);
lean_dec(v_handlerTask_5581_);
lean_dec(v_pendingHead_5579_);
lean_dec(v_expectData_5577_);
lean_dec(v_respStream_5576_);
lean_dec_ref(v_response_5575_);
lean_dec(v_headerTimeout_5574_);
lean_dec(v_keepAliveTimeout_5573_);
lean_dec_ref(v_requestStream_5572_);
lean_dec_ref(v_machine_5571_);
lean_dec(v_keepAliveTimeout_5569_);
lean_dec_ref(v___f_5568_);
lean_dec_ref(v_a_5567_);
v___x_5615_ = lean_box(0);
v___x_5616_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__4(v_h_5561_, v_responseBodyInstance_5562_, v_handler_5563_, v_config_5564_, v_a_5596_, v___x_5565_, v___f_5566_, v___x_5615_, v___x_5570_);
return v___x_5616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_h_5618_ = _args[0];
lean_object* v_responseBodyInstance_5619_ = _args[1];
lean_object* v_handler_5620_ = _args[2];
lean_object* v_config_5621_ = _args[3];
lean_object* v___x_5622_ = _args[4];
lean_object* v___f_5623_ = _args[5];
lean_object* v_a_5624_ = _args[6];
lean_object* v___f_5625_ = _args[7];
lean_object* v_keepAliveTimeout_5626_ = _args[8];
lean_object* v___x_5627_ = _args[9];
lean_object* v_machine_5628_ = _args[10];
lean_object* v_requestStream_5629_ = _args[11];
lean_object* v_keepAliveTimeout_5630_ = _args[12];
lean_object* v_headerTimeout_5631_ = _args[13];
lean_object* v_response_5632_ = _args[14];
lean_object* v_respStream_5633_ = _args[15];
lean_object* v_expectData_5634_ = _args[16];
lean_object* v_handlerDispatched_5635_ = _args[17];
lean_object* v_pendingHead_5636_ = _args[18];
lean_object* v_requestFinalOffered_5637_ = _args[19];
lean_object* v_handlerTask_5638_ = _args[20];
lean_object* v_dateSecond_5639_ = _args[21];
lean_object* v_peerClosed_5640_ = _args[22];
lean_object* v_requestEnded_5641_ = _args[23];
lean_object* v_x_5642_ = _args[24];
lean_object* v___y_5643_ = _args[25];
_start:
{
uint8_t v___x_8966__boxed_5644_; uint8_t v_handlerDispatched_boxed_5645_; uint8_t v_requestFinalOffered_boxed_5646_; uint8_t v_peerClosed_boxed_5647_; uint8_t v_requestEnded_boxed_5648_; lean_object* v_res_5649_; 
v___x_8966__boxed_5644_ = lean_unbox(v___x_5622_);
v_handlerDispatched_boxed_5645_ = lean_unbox(v_handlerDispatched_5635_);
v_requestFinalOffered_boxed_5646_ = lean_unbox(v_requestFinalOffered_5637_);
v_peerClosed_boxed_5647_ = lean_unbox(v_peerClosed_5640_);
v_requestEnded_boxed_5648_ = lean_unbox(v_requestEnded_5641_);
v_res_5649_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5(v_h_5618_, v_responseBodyInstance_5619_, v_handler_5620_, v_config_5621_, v___x_8966__boxed_5644_, v___f_5623_, v_a_5624_, v___f_5625_, v_keepAliveTimeout_5626_, v___x_5627_, v_machine_5628_, v_requestStream_5629_, v_keepAliveTimeout_5630_, v_headerTimeout_5631_, v_response_5632_, v_respStream_5633_, v_expectData_5634_, v_handlerDispatched_boxed_5645_, v_pendingHead_5636_, v_requestFinalOffered_boxed_5646_, v_handlerTask_5638_, v_dateSecond_5639_, v_peerClosed_boxed_5647_, v_requestEnded_boxed_5648_, v_x_5642_);
return v_res_5649_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(lean_object* v_inst_5650_, lean_object* v_h_5651_, lean_object* v_responseBodyInstance_5652_, lean_object* v_config_5653_, lean_object* v_handler_5654_, uint8_t v___x_5655_, lean_object* v___f_5656_, lean_object* v_x_5657_){
_start:
{
if (lean_obj_tag(v_x_5657_) == 0)
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5667_; 
lean_dec_ref(v___f_5656_);
lean_dec(v_handler_5654_);
lean_dec_ref(v_config_5653_);
lean_dec_ref(v_responseBodyInstance_5652_);
lean_dec_ref(v_h_5651_);
lean_dec_ref(v_inst_5650_);
v_a_5659_ = lean_ctor_get(v_x_5657_, 0);
v_isSharedCheck_5667_ = !lean_is_exclusive(v_x_5657_);
if (v_isSharedCheck_5667_ == 0)
{
v___x_5661_ = v_x_5657_;
v_isShared_5662_ = v_isSharedCheck_5667_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v_x_5657_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5667_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v___x_5664_; 
if (v_isShared_5662_ == 0)
{
v___x_5664_ = v___x_5661_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_a_5659_);
v___x_5664_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
lean_object* v___x_5665_; 
v___x_5665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5665_, 0, v___x_5664_);
return v___x_5665_;
}
}
}
else
{
lean_object* v_a_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; 
v_a_5668_ = lean_ctor_get(v_x_5657_, 0);
lean_inc(v_a_5668_);
lean_dec_ref_known(v_x_5657_, 1);
v___x_5669_ = lean_unsigned_to_nat(0u);
v___x_5670_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_5650_, v_h_5651_, v_responseBodyInstance_5652_, v_config_5653_, v_handler_5654_, v_a_5668_);
v___x_5671_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5669_, v___x_5655_, v___x_5670_, v___f_5656_);
return v___x_5671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed(lean_object* v_inst_5672_, lean_object* v_h_5673_, lean_object* v_responseBodyInstance_5674_, lean_object* v_config_5675_, lean_object* v_handler_5676_, lean_object* v___x_5677_, lean_object* v___f_5678_, lean_object* v_x_5679_, lean_object* v___y_5680_){
_start:
{
uint8_t v___x_9050__boxed_5681_; lean_object* v_res_5682_; 
v___x_9050__boxed_5681_ = lean_unbox(v___x_5677_);
v_res_5682_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6(v_inst_5672_, v_h_5673_, v_responseBodyInstance_5674_, v_config_5675_, v_handler_5676_, v___x_9050__boxed_5681_, v___f_5678_, v_x_5679_);
return v_res_5682_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(uint8_t v___x_5683_, lean_object* v_h_5684_, lean_object* v_responseBodyInstance_5685_, lean_object* v_handler_5686_, lean_object* v_config_5687_, lean_object* v___f_5688_, lean_object* v_a_5689_, lean_object* v_keepAliveTimeout_5690_, lean_object* v_inst_5691_, lean_object* v_socket_5692_, lean_object* v_connectionContext_5693_, lean_object* v_maximumRecvSize_5694_, lean_object* v_x_5695_){
_start:
{
if (lean_obj_tag(v_x_5695_) == 0)
{
lean_object* v_a_5697_; lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_5705_; 
lean_dec(v_maximumRecvSize_5694_);
lean_dec_ref(v_connectionContext_5693_);
lean_dec(v_socket_5692_);
lean_dec_ref(v_inst_5691_);
lean_dec(v_keepAliveTimeout_5690_);
lean_dec_ref(v_a_5689_);
lean_dec_ref(v___f_5688_);
lean_dec_ref(v_config_5687_);
lean_dec(v_handler_5686_);
lean_dec_ref(v_responseBodyInstance_5685_);
lean_dec_ref(v_h_5684_);
v_a_5697_ = lean_ctor_get(v_x_5695_, 0);
v_isSharedCheck_5705_ = !lean_is_exclusive(v_x_5695_);
if (v_isSharedCheck_5705_ == 0)
{
v___x_5699_ = v_x_5695_;
v_isShared_5700_ = v_isSharedCheck_5705_;
goto v_resetjp_5698_;
}
else
{
lean_inc(v_a_5697_);
lean_dec(v_x_5695_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_5705_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
lean_object* v___x_5702_; 
if (v_isShared_5700_ == 0)
{
v___x_5702_ = v___x_5699_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v_a_5697_);
v___x_5702_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
lean_object* v___x_5703_; 
v___x_5703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5703_, 0, v___x_5702_);
return v___x_5703_;
}
}
}
else
{
lean_object* v_a_5706_; lean_object* v___x_5708_; uint8_t v_isShared_5709_; uint8_t v_isSharedCheck_5758_; 
v_a_5706_ = lean_ctor_get(v_x_5695_, 0);
v_isSharedCheck_5758_ = !lean_is_exclusive(v_x_5695_);
if (v_isSharedCheck_5758_ == 0)
{
v___x_5708_ = v_x_5695_;
v_isShared_5709_ = v_isSharedCheck_5758_;
goto v_resetjp_5707_;
}
else
{
lean_inc(v_a_5706_);
lean_dec(v_x_5695_);
v___x_5708_ = lean_box(0);
v_isShared_5709_ = v_isSharedCheck_5758_;
goto v_resetjp_5707_;
}
v_resetjp_5707_:
{
lean_object* v_machine_5716_; lean_object* v_requestStream_5717_; lean_object* v_keepAliveTimeout_5718_; lean_object* v_currentTimeout_5719_; lean_object* v_headerTimeout_5720_; lean_object* v_response_5721_; lean_object* v_respStream_5722_; uint8_t v_requiresData_5723_; lean_object* v_expectData_5724_; uint8_t v_handlerDispatched_5725_; lean_object* v_pendingHead_5726_; uint8_t v_requestFinalOffered_5727_; lean_object* v_handlerTask_5728_; lean_object* v_dateSecond_5729_; uint8_t v_peerClosed_5730_; uint8_t v_requestEnded_5731_; 
v_machine_5716_ = lean_ctor_get(v_a_5706_, 0);
v_requestStream_5717_ = lean_ctor_get(v_a_5706_, 1);
v_keepAliveTimeout_5718_ = lean_ctor_get(v_a_5706_, 2);
v_currentTimeout_5719_ = lean_ctor_get(v_a_5706_, 3);
v_headerTimeout_5720_ = lean_ctor_get(v_a_5706_, 4);
v_response_5721_ = lean_ctor_get(v_a_5706_, 5);
v_respStream_5722_ = lean_ctor_get(v_a_5706_, 6);
v_requiresData_5723_ = lean_ctor_get_uint8(v_a_5706_, sizeof(void*)*11);
v_expectData_5724_ = lean_ctor_get(v_a_5706_, 7);
v_handlerDispatched_5725_ = lean_ctor_get_uint8(v_a_5706_, sizeof(void*)*11 + 1);
v_pendingHead_5726_ = lean_ctor_get(v_a_5706_, 8);
v_requestFinalOffered_5727_ = lean_ctor_get_uint8(v_a_5706_, sizeof(void*)*11 + 2);
v_handlerTask_5728_ = lean_ctor_get(v_a_5706_, 9);
v_dateSecond_5729_ = lean_ctor_get(v_a_5706_, 10);
v_peerClosed_5730_ = lean_ctor_get_uint8(v_a_5706_, sizeof(void*)*11 + 3);
v_requestEnded_5731_ = lean_ctor_get_uint8(v_a_5706_, sizeof(void*)*11 + 4);
if (v_requiresData_5723_ == 0)
{
if (v_handlerDispatched_5725_ == 0)
{
if (lean_obj_tag(v_respStream_5722_) == 0)
{
lean_object* v_reader_5746_; lean_object* v_writer_5747_; uint8_t v___y_5749_; lean_object* v_state_5751_; 
v_reader_5746_ = lean_ctor_get(v_machine_5716_, 0);
v_writer_5747_ = lean_ctor_get(v_machine_5716_, 1);
v_state_5751_ = lean_ctor_get(v_writer_5747_, 2);
switch(lean_obj_tag(v_state_5751_))
{
case 6:
{
lean_dec(v_maximumRecvSize_5694_);
lean_dec_ref(v_connectionContext_5693_);
lean_dec(v_socket_5692_);
lean_dec_ref(v_inst_5691_);
lean_dec(v_keepAliveTimeout_5690_);
lean_dec_ref(v_a_5689_);
lean_dec_ref(v___f_5688_);
lean_dec_ref(v_config_5687_);
lean_dec(v_handler_5686_);
lean_dec_ref(v_responseBodyInstance_5685_);
lean_dec_ref(v_h_5684_);
goto v___jp_5710_;
}
case 7:
{
lean_dec(v_maximumRecvSize_5694_);
lean_dec_ref(v_connectionContext_5693_);
lean_dec(v_socket_5692_);
lean_dec_ref(v_inst_5691_);
lean_dec(v_keepAliveTimeout_5690_);
lean_dec_ref(v_a_5689_);
lean_dec_ref(v___f_5688_);
lean_dec_ref(v_config_5687_);
lean_dec(v_handler_5686_);
lean_dec_ref(v_responseBodyInstance_5685_);
lean_dec_ref(v_h_5684_);
goto v___jp_5710_;
}
default: 
{
uint8_t v_sentMessage_5752_; 
v_sentMessage_5752_ = lean_ctor_get_uint8(v_writer_5747_, sizeof(void*)*6);
if (v_sentMessage_5752_ == 0)
{
v___y_5749_ = v_sentMessage_5752_;
goto v___jp_5748_;
}
else
{
lean_object* v_state_5753_; 
v_state_5753_ = lean_ctor_get(v_reader_5746_, 0);
if (lean_obj_tag(v_state_5753_) == 2)
{
lean_object* v_a_5754_; 
v_a_5754_ = lean_ctor_get(v_state_5753_, 0);
if (lean_obj_tag(v_a_5754_) == 0)
{
lean_object* v_remaining_5755_; lean_object* v___x_5756_; uint8_t v___x_5757_; 
v_remaining_5755_ = lean_ctor_get(v_a_5754_, 0);
v___x_5756_ = lean_unsigned_to_nat(0u);
v___x_5757_ = lean_nat_dec_eq(v_remaining_5755_, v___x_5756_);
if (v___x_5757_ == 0)
{
v___y_5749_ = v___x_5757_;
goto v___jp_5748_;
}
else
{
lean_dec(v_maximumRecvSize_5694_);
lean_dec_ref(v_connectionContext_5693_);
lean_dec(v_socket_5692_);
lean_dec_ref(v_inst_5691_);
lean_dec(v_keepAliveTimeout_5690_);
lean_dec_ref(v_a_5689_);
lean_dec_ref(v___f_5688_);
lean_dec_ref(v_config_5687_);
lean_dec(v_handler_5686_);
lean_dec_ref(v_responseBodyInstance_5685_);
lean_dec_ref(v_h_5684_);
goto v___jp_5710_;
}
}
else
{
v___y_5749_ = v_handlerDispatched_5725_;
goto v___jp_5748_;
}
}
else
{
v___y_5749_ = v_handlerDispatched_5725_;
goto v___jp_5748_;
}
}
}
}
v___jp_5748_:
{
lean_object* v_state_5750_; 
v_state_5750_ = lean_ctor_get(v_reader_5746_, 0);
if (lean_obj_tag(v_state_5750_) == 2)
{
lean_inc(v_respStream_5722_);
lean_inc(v_dateSecond_5729_);
lean_inc(v_handlerTask_5728_);
lean_inc(v_pendingHead_5726_);
lean_inc(v_expectData_5724_);
lean_inc_ref(v_response_5721_);
lean_inc(v_headerTimeout_5720_);
lean_inc(v_currentTimeout_5719_);
lean_inc(v_keepAliveTimeout_5718_);
lean_inc_ref(v_requestStream_5717_);
lean_inc_ref(v_machine_5716_);
lean_del_object(v___x_5708_);
lean_dec(v_a_5706_);
goto v___jp_5732_;
}
else
{
if (v___y_5749_ == 0)
{
lean_dec(v_maximumRecvSize_5694_);
lean_dec_ref(v_connectionContext_5693_);
lean_dec(v_socket_5692_);
lean_dec_ref(v_inst_5691_);
lean_dec(v_keepAliveTimeout_5690_);
lean_dec_ref(v_a_5689_);
lean_dec_ref(v___f_5688_);
lean_dec_ref(v_config_5687_);
lean_dec(v_handler_5686_);
lean_dec_ref(v_responseBodyInstance_5685_);
lean_dec_ref(v_h_5684_);
goto v___jp_5710_;
}
else
{
lean_inc(v_respStream_5722_);
lean_inc(v_dateSecond_5729_);
lean_inc(v_handlerTask_5728_);
lean_inc(v_pendingHead_5726_);
lean_inc(v_expectData_5724_);
lean_inc_ref(v_response_5721_);
lean_inc(v_headerTimeout_5720_);
lean_inc(v_currentTimeout_5719_);
lean_inc(v_keepAliveTimeout_5718_);
lean_inc_ref(v_requestStream_5717_);
lean_inc_ref(v_machine_5716_);
lean_del_object(v___x_5708_);
lean_dec(v_a_5706_);
goto v___jp_5732_;
}
}
}
}
else
{
lean_inc_ref(v_respStream_5722_);
lean_inc(v_dateSecond_5729_);
lean_inc(v_handlerTask_5728_);
lean_inc(v_pendingHead_5726_);
lean_inc(v_expectData_5724_);
lean_inc_ref(v_response_5721_);
lean_inc(v_headerTimeout_5720_);
lean_inc(v_currentTimeout_5719_);
lean_inc(v_keepAliveTimeout_5718_);
lean_inc_ref(v_requestStream_5717_);
lean_inc_ref(v_machine_5716_);
lean_del_object(v___x_5708_);
lean_dec(v_a_5706_);
goto v___jp_5732_;
}
}
else
{
lean_inc(v_dateSecond_5729_);
lean_inc(v_handlerTask_5728_);
lean_inc(v_pendingHead_5726_);
lean_inc(v_expectData_5724_);
lean_inc(v_respStream_5722_);
lean_inc_ref(v_response_5721_);
lean_inc(v_headerTimeout_5720_);
lean_inc(v_currentTimeout_5719_);
lean_inc(v_keepAliveTimeout_5718_);
lean_inc_ref(v_requestStream_5717_);
lean_inc_ref(v_machine_5716_);
lean_del_object(v___x_5708_);
lean_dec(v_a_5706_);
goto v___jp_5732_;
}
}
else
{
lean_inc(v_dateSecond_5729_);
lean_inc(v_handlerTask_5728_);
lean_inc(v_pendingHead_5726_);
lean_inc(v_expectData_5724_);
lean_inc(v_respStream_5722_);
lean_inc_ref(v_response_5721_);
lean_inc(v_headerTimeout_5720_);
lean_inc(v_currentTimeout_5719_);
lean_inc(v_keepAliveTimeout_5718_);
lean_inc_ref(v_requestStream_5717_);
lean_inc_ref(v_machine_5716_);
lean_del_object(v___x_5708_);
lean_dec(v_a_5706_);
goto v___jp_5732_;
}
v___jp_5710_:
{
lean_object* v___x_5711_; lean_object* v___x_5713_; 
v___x_5711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5711_, 0, v_a_5706_);
if (v_isShared_5709_ == 0)
{
lean_ctor_set(v___x_5708_, 0, v___x_5711_);
v___x_5713_ = v___x_5708_;
goto v_reusejp_5712_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v___x_5711_);
v___x_5713_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5712_;
}
v_reusejp_5712_:
{
lean_object* v___x_5714_; 
v___x_5714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5713_);
return v___x_5714_;
}
}
v___jp_5732_:
{
lean_object* v___x_5733_; lean_object* v___f_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___f_5740_; lean_object* v___x_5741_; lean_object* v___f_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
lean_inc(v_dateSecond_5729_);
lean_inc(v_handlerTask_5728_);
lean_inc(v_pendingHead_5726_);
lean_inc(v_expectData_5724_);
lean_inc(v_respStream_5722_);
lean_inc_ref(v_response_5721_);
lean_inc(v_headerTimeout_5720_);
lean_inc(v_keepAliveTimeout_5718_);
lean_inc_ref(v_requestStream_5717_);
lean_inc_ref(v_machine_5716_);
v___x_5733_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v___x_5733_, 0, v_machine_5716_);
lean_ctor_set(v___x_5733_, 1, v_requestStream_5717_);
lean_ctor_set(v___x_5733_, 2, v_keepAliveTimeout_5718_);
lean_ctor_set(v___x_5733_, 3, v_currentTimeout_5719_);
lean_ctor_set(v___x_5733_, 4, v_headerTimeout_5720_);
lean_ctor_set(v___x_5733_, 5, v_response_5721_);
lean_ctor_set(v___x_5733_, 6, v_respStream_5722_);
lean_ctor_set(v___x_5733_, 7, v_expectData_5724_);
lean_ctor_set(v___x_5733_, 8, v_pendingHead_5726_);
lean_ctor_set(v___x_5733_, 9, v_handlerTask_5728_);
lean_ctor_set(v___x_5733_, 10, v_dateSecond_5729_);
lean_ctor_set_uint8(v___x_5733_, sizeof(void*)*11, v___x_5683_);
lean_ctor_set_uint8(v___x_5733_, sizeof(void*)*11 + 1, v_handlerDispatched_5725_);
lean_ctor_set_uint8(v___x_5733_, sizeof(void*)*11 + 2, v_requestFinalOffered_5727_);
lean_ctor_set_uint8(v___x_5733_, sizeof(void*)*11 + 3, v_peerClosed_5730_);
lean_ctor_set_uint8(v___x_5733_, sizeof(void*)*11 + 4, v_requestEnded_5731_);
lean_inc_ref_n(v___x_5733_, 2);
v___f_5734_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5734_, 0, v___x_5733_);
v___x_5735_ = lean_box(v___x_5683_);
v___x_5736_ = lean_box(v_handlerDispatched_5725_);
v___x_5737_ = lean_box(v_requestFinalOffered_5727_);
v___x_5738_ = lean_box(v_peerClosed_5730_);
v___x_5739_ = lean_box(v_requestEnded_5731_);
lean_inc_ref(v_config_5687_);
lean_inc(v_handler_5686_);
lean_inc_ref(v_responseBodyInstance_5685_);
lean_inc_ref(v_h_5684_);
v___f_5740_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__5___boxed), 26, 24);
lean_closure_set(v___f_5740_, 0, v_h_5684_);
lean_closure_set(v___f_5740_, 1, v_responseBodyInstance_5685_);
lean_closure_set(v___f_5740_, 2, v_handler_5686_);
lean_closure_set(v___f_5740_, 3, v_config_5687_);
lean_closure_set(v___f_5740_, 4, v___x_5735_);
lean_closure_set(v___f_5740_, 5, v___f_5688_);
lean_closure_set(v___f_5740_, 6, v_a_5689_);
lean_closure_set(v___f_5740_, 7, v___f_5734_);
lean_closure_set(v___f_5740_, 8, v_keepAliveTimeout_5690_);
lean_closure_set(v___f_5740_, 9, v___x_5733_);
lean_closure_set(v___f_5740_, 10, v_machine_5716_);
lean_closure_set(v___f_5740_, 11, v_requestStream_5717_);
lean_closure_set(v___f_5740_, 12, v_keepAliveTimeout_5718_);
lean_closure_set(v___f_5740_, 13, v_headerTimeout_5720_);
lean_closure_set(v___f_5740_, 14, v_response_5721_);
lean_closure_set(v___f_5740_, 15, v_respStream_5722_);
lean_closure_set(v___f_5740_, 16, v_expectData_5724_);
lean_closure_set(v___f_5740_, 17, v___x_5736_);
lean_closure_set(v___f_5740_, 18, v_pendingHead_5726_);
lean_closure_set(v___f_5740_, 19, v___x_5737_);
lean_closure_set(v___f_5740_, 20, v_handlerTask_5728_);
lean_closure_set(v___f_5740_, 21, v_dateSecond_5729_);
lean_closure_set(v___f_5740_, 22, v___x_5738_);
lean_closure_set(v___f_5740_, 23, v___x_5739_);
v___x_5741_ = lean_box(v___x_5683_);
v___f_5742_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__6___boxed), 9, 7);
lean_closure_set(v___f_5742_, 0, v_inst_5691_);
lean_closure_set(v___f_5742_, 1, v_h_5684_);
lean_closure_set(v___f_5742_, 2, v_responseBodyInstance_5685_);
lean_closure_set(v___f_5742_, 3, v_config_5687_);
lean_closure_set(v___f_5742_, 4, v_handler_5686_);
lean_closure_set(v___f_5742_, 5, v___x_5741_);
lean_closure_set(v___f_5742_, 6, v___f_5740_);
v___x_5743_ = lean_unsigned_to_nat(0u);
v___x_5744_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_5692_, v_connectionContext_5693_, v___x_5733_, v_requiresData_5723_, v_maximumRecvSize_5694_);
v___x_5745_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5743_, v___x_5683_, v___x_5744_, v___f_5742_);
return v___x_5745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed(lean_object* v___x_5759_, lean_object* v_h_5760_, lean_object* v_responseBodyInstance_5761_, lean_object* v_handler_5762_, lean_object* v_config_5763_, lean_object* v___f_5764_, lean_object* v_a_5765_, lean_object* v_keepAliveTimeout_5766_, lean_object* v_inst_5767_, lean_object* v_socket_5768_, lean_object* v_connectionContext_5769_, lean_object* v_maximumRecvSize_5770_, lean_object* v_x_5771_, lean_object* v___y_5772_){
_start:
{
uint8_t v___x_9090__boxed_5773_; lean_object* v_res_5774_; 
v___x_9090__boxed_5773_ = lean_unbox(v___x_5759_);
v_res_5774_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7(v___x_9090__boxed_5773_, v_h_5760_, v_responseBodyInstance_5761_, v_handler_5762_, v_config_5763_, v___f_5764_, v_a_5765_, v_keepAliveTimeout_5766_, v_inst_5767_, v_socket_5768_, v_connectionContext_5769_, v_maximumRecvSize_5770_, v_x_5771_);
return v_res_5774_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(lean_object* v_h_5775_, lean_object* v_handler_5776_, lean_object* v_extensions_5777_, lean_object* v_connectionContext_5778_, uint8_t v___x_5779_, lean_object* v___f_5780_, lean_object* v_x_5781_){
_start:
{
if (lean_obj_tag(v_x_5781_) == 0)
{
lean_object* v_a_5783_; lean_object* v___x_5785_; uint8_t v_isShared_5786_; uint8_t v_isSharedCheck_5791_; 
lean_dec_ref(v___f_5780_);
lean_dec_ref(v_connectionContext_5778_);
lean_dec(v_extensions_5777_);
lean_dec(v_handler_5776_);
lean_dec_ref(v_h_5775_);
v_a_5783_ = lean_ctor_get(v_x_5781_, 0);
v_isSharedCheck_5791_ = !lean_is_exclusive(v_x_5781_);
if (v_isSharedCheck_5791_ == 0)
{
v___x_5785_ = v_x_5781_;
v_isShared_5786_ = v_isSharedCheck_5791_;
goto v_resetjp_5784_;
}
else
{
lean_inc(v_a_5783_);
lean_dec(v_x_5781_);
v___x_5785_ = lean_box(0);
v_isShared_5786_ = v_isSharedCheck_5791_;
goto v_resetjp_5784_;
}
v_resetjp_5784_:
{
lean_object* v___x_5788_; 
if (v_isShared_5786_ == 0)
{
v___x_5788_ = v___x_5785_;
goto v_reusejp_5787_;
}
else
{
lean_object* v_reuseFailAlloc_5790_; 
v_reuseFailAlloc_5790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5783_);
v___x_5788_ = v_reuseFailAlloc_5790_;
goto v_reusejp_5787_;
}
v_reusejp_5787_:
{
lean_object* v___x_5789_; 
v___x_5789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5789_, 0, v___x_5788_);
return v___x_5789_;
}
}
}
else
{
lean_object* v_a_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; 
v_a_5792_ = lean_ctor_get(v_x_5781_, 0);
lean_inc(v_a_5792_);
lean_dec_ref_known(v_x_5781_, 1);
v___x_5793_ = lean_unsigned_to_nat(0u);
v___x_5794_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_5775_, v_handler_5776_, v_extensions_5777_, v_connectionContext_5778_, v_a_5792_);
v___x_5795_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5793_, v___x_5779_, v___x_5794_, v___f_5780_);
return v___x_5795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed(lean_object* v_h_5796_, lean_object* v_handler_5797_, lean_object* v_extensions_5798_, lean_object* v_connectionContext_5799_, lean_object* v___x_5800_, lean_object* v___f_5801_, lean_object* v_x_5802_, lean_object* v___y_5803_){
_start:
{
uint8_t v___x_9190__boxed_5804_; lean_object* v_res_5805_; 
v___x_9190__boxed_5804_ = lean_unbox(v___x_5800_);
v_res_5805_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8(v_h_5796_, v_handler_5797_, v_extensions_5798_, v_connectionContext_5799_, v___x_9190__boxed_5804_, v___f_5801_, v_x_5802_);
return v_res_5805_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(lean_object* v___x_5806_, lean_object* v_x_5807_){
_start:
{
if (lean_obj_tag(v_x_5807_) == 0)
{
lean_object* v_a_5809_; lean_object* v___x_5811_; uint8_t v_isShared_5812_; uint8_t v_isSharedCheck_5817_; 
lean_dec_ref(v___x_5806_);
v_a_5809_ = lean_ctor_get(v_x_5807_, 0);
v_isSharedCheck_5817_ = !lean_is_exclusive(v_x_5807_);
if (v_isSharedCheck_5817_ == 0)
{
v___x_5811_ = v_x_5807_;
v_isShared_5812_ = v_isSharedCheck_5817_;
goto v_resetjp_5810_;
}
else
{
lean_inc(v_a_5809_);
lean_dec(v_x_5807_);
v___x_5811_ = lean_box(0);
v_isShared_5812_ = v_isSharedCheck_5817_;
goto v_resetjp_5810_;
}
v_resetjp_5810_:
{
lean_object* v___x_5814_; 
if (v_isShared_5812_ == 0)
{
v___x_5814_ = v___x_5811_;
goto v_reusejp_5813_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v_a_5809_);
v___x_5814_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5813_;
}
v_reusejp_5813_:
{
lean_object* v___x_5815_; 
v___x_5815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5815_, 0, v___x_5814_);
return v___x_5815_;
}
}
}
else
{
lean_object* v___x_5819_; uint8_t v_isShared_5820_; uint8_t v_isSharedCheck_5826_; 
v_isSharedCheck_5826_ = !lean_is_exclusive(v_x_5807_);
if (v_isSharedCheck_5826_ == 0)
{
lean_object* v_unused_5827_; 
v_unused_5827_ = lean_ctor_get(v_x_5807_, 0);
lean_dec(v_unused_5827_);
v___x_5819_ = v_x_5807_;
v_isShared_5820_ = v_isSharedCheck_5826_;
goto v_resetjp_5818_;
}
else
{
lean_dec(v_x_5807_);
v___x_5819_ = lean_box(0);
v_isShared_5820_ = v_isSharedCheck_5826_;
goto v_resetjp_5818_;
}
v_resetjp_5818_:
{
lean_object* v___x_5821_; lean_object* v___x_5823_; 
v___x_5821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5821_, 0, v___x_5806_);
if (v_isShared_5820_ == 0)
{
lean_ctor_set(v___x_5819_, 0, v___x_5821_);
v___x_5823_ = v___x_5819_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5825_; 
v_reuseFailAlloc_5825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5825_, 0, v___x_5821_);
v___x_5823_ = v_reuseFailAlloc_5825_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
lean_object* v___x_5824_; 
v___x_5824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5824_, 0, v___x_5823_);
return v___x_5824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed(lean_object* v___x_5828_, lean_object* v_x_5829_, lean_object* v___y_5830_){
_start:
{
lean_object* v_res_5831_; 
v_res_5831_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9(v___x_5828_, v_x_5829_);
return v_res_5831_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(lean_object* v_h_5832_, lean_object* v_responseBodyInstance_5833_, lean_object* v_handler_5834_, lean_object* v_config_5835_, lean_object* v_connectionContext_5836_, lean_object* v_events_5837_, lean_object* v___x_5838_, uint8_t v___x_5839_, lean_object* v___f_5840_, lean_object* v_____r_5841_){
_start:
{
lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; 
v___x_5843_ = lean_unsigned_to_nat(0u);
v___x_5844_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_5832_, v_responseBodyInstance_5833_, v_handler_5834_, v_config_5835_, v_connectionContext_5836_, v_events_5837_, v___x_5838_);
v___x_5845_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5843_, v___x_5839_, v___x_5844_, v___f_5840_);
return v___x_5845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed(lean_object* v_h_5846_, lean_object* v_responseBodyInstance_5847_, lean_object* v_handler_5848_, lean_object* v_config_5849_, lean_object* v_connectionContext_5850_, lean_object* v_events_5851_, lean_object* v___x_5852_, lean_object* v___x_5853_, lean_object* v___f_5854_, lean_object* v_____r_5855_, lean_object* v___y_5856_){
_start:
{
uint8_t v___x_9277__boxed_5857_; lean_object* v_res_5858_; 
v___x_9277__boxed_5857_ = lean_unbox(v___x_5853_);
v_res_5858_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10(v_h_5846_, v_responseBodyInstance_5847_, v_handler_5848_, v_config_5849_, v_connectionContext_5850_, v_events_5851_, v___x_5852_, v___x_9277__boxed_5857_, v___f_5854_, v_____r_5855_);
return v_res_5858_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(lean_object* v_h_5859_, lean_object* v_handler_5860_, lean_object* v_a_5861_, lean_object* v___f_5862_, lean_object* v___f_5863_, lean_object* v_x_5864_){
_start:
{
if (lean_obj_tag(v_x_5864_) == 0)
{
lean_object* v_a_5866_; lean_object* v___x_5868_; uint8_t v_isShared_5869_; uint8_t v_isSharedCheck_5874_; 
lean_dec_ref(v___f_5863_);
lean_dec_ref(v___f_5862_);
lean_dec(v_handler_5860_);
lean_dec_ref(v_h_5859_);
v_a_5866_ = lean_ctor_get(v_x_5864_, 0);
v_isSharedCheck_5874_ = !lean_is_exclusive(v_x_5864_);
if (v_isSharedCheck_5874_ == 0)
{
v___x_5868_ = v_x_5864_;
v_isShared_5869_ = v_isSharedCheck_5874_;
goto v_resetjp_5867_;
}
else
{
lean_inc(v_a_5866_);
lean_dec(v_x_5864_);
v___x_5868_ = lean_box(0);
v_isShared_5869_ = v_isSharedCheck_5874_;
goto v_resetjp_5867_;
}
v_resetjp_5867_:
{
lean_object* v___x_5871_; 
if (v_isShared_5869_ == 0)
{
v___x_5871_ = v___x_5868_;
goto v_reusejp_5870_;
}
else
{
lean_object* v_reuseFailAlloc_5873_; 
v_reuseFailAlloc_5873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5866_);
v___x_5871_ = v_reuseFailAlloc_5873_;
goto v_reusejp_5870_;
}
v_reusejp_5870_:
{
lean_object* v___x_5872_; 
v___x_5872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5872_, 0, v___x_5871_);
return v___x_5872_;
}
}
}
else
{
lean_object* v_a_5875_; uint8_t v___x_5876_; 
v_a_5875_ = lean_ctor_get(v_x_5864_, 0);
lean_inc(v_a_5875_);
lean_dec_ref_known(v_x_5864_, 1);
v___x_5876_ = lean_unbox(v_a_5875_);
if (v___x_5876_ == 0)
{
lean_object* v___x_5877_; lean_object* v___x_5878_; uint8_t v___x_5879_; lean_object* v___x_5880_; 
lean_dec_ref(v___f_5863_);
v___x_5877_ = lean_unsigned_to_nat(0u);
v___x_5878_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_h_5859_, v_handler_5860_, v_a_5861_);
v___x_5879_ = lean_unbox(v_a_5875_);
lean_dec(v_a_5875_);
v___x_5880_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5877_, v___x_5879_, v___x_5878_, v___f_5862_);
return v___x_5880_;
}
else
{
lean_object* v___x_5881_; lean_object* v___x_5882_; 
lean_dec(v_a_5875_);
lean_dec_ref(v___f_5862_);
lean_dec(v_handler_5860_);
lean_dec_ref(v_h_5859_);
v___x_5881_ = lean_box(0);
v___x_5882_ = lean_apply_2(v___f_5863_, v___x_5881_, lean_box(0));
return v___x_5882_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed(lean_object* v_h_5883_, lean_object* v_handler_5884_, lean_object* v_a_5885_, lean_object* v___f_5886_, lean_object* v___f_5887_, lean_object* v_x_5888_, lean_object* v___y_5889_){
_start:
{
lean_object* v_res_5890_; 
v_res_5890_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12(v_h_5883_, v_handler_5884_, v_a_5885_, v___f_5886_, v___f_5887_, v_x_5888_);
lean_dec_ref(v_a_5885_);
return v_res_5890_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(lean_object* v_h_5891_, lean_object* v_handler_5892_, lean_object* v_a_5893_, lean_object* v___f_5894_, lean_object* v___f_5895_, lean_object* v_events_5896_, lean_object* v___f_5897_, uint8_t v___x_5898_, lean_object* v___f_5899_, lean_object* v_x_5900_){
_start:
{
if (lean_obj_tag(v_x_5900_) == 0)
{
lean_object* v_a_5905_; lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5913_; 
lean_dec_ref(v___f_5899_);
lean_dec_ref(v___f_5897_);
lean_dec_ref(v_events_5896_);
lean_dec_ref(v___f_5895_);
lean_dec_ref(v___f_5894_);
lean_dec_ref(v_a_5893_);
lean_dec(v_handler_5892_);
lean_dec_ref(v_h_5891_);
v_a_5905_ = lean_ctor_get(v_x_5900_, 0);
v_isSharedCheck_5913_ = !lean_is_exclusive(v_x_5900_);
if (v_isSharedCheck_5913_ == 0)
{
v___x_5907_ = v_x_5900_;
v_isShared_5908_ = v_isSharedCheck_5913_;
goto v_resetjp_5906_;
}
else
{
lean_inc(v_a_5905_);
lean_dec(v_x_5900_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5913_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5910_; 
if (v_isShared_5908_ == 0)
{
v___x_5910_ = v___x_5907_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5912_; 
v_reuseFailAlloc_5912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5912_, 0, v_a_5905_);
v___x_5910_ = v_reuseFailAlloc_5912_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
lean_object* v___x_5911_; 
v___x_5911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5910_);
return v___x_5911_;
}
}
}
else
{
lean_object* v_a_5914_; uint8_t v___x_5915_; 
v_a_5914_ = lean_ctor_get(v_x_5900_, 0);
lean_inc(v_a_5914_);
lean_dec_ref_known(v_x_5900_, 1);
v___x_5915_ = lean_unbox(v_a_5914_);
if (v___x_5915_ == 0)
{
lean_object* v___x_5916_; lean_object* v___x_5917_; uint8_t v___x_5918_; lean_object* v___x_5919_; 
lean_dec_ref(v___f_5899_);
lean_dec_ref(v___f_5897_);
lean_dec_ref(v_events_5896_);
lean_dec_ref(v___f_5895_);
v___x_5916_ = lean_unsigned_to_nat(0u);
v___x_5917_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_h_5891_, v_handler_5892_, v_a_5893_);
lean_dec_ref(v_a_5893_);
v___x_5918_ = lean_unbox(v_a_5914_);
lean_dec(v_a_5914_);
v___x_5919_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5916_, v___x_5918_, v___x_5917_, v___f_5894_);
return v___x_5919_;
}
else
{
lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; uint8_t v___x_5923_; 
lean_dec(v_a_5914_);
lean_dec_ref(v___f_5894_);
lean_dec(v_handler_5892_);
lean_dec_ref(v_h_5891_);
v___x_5920_ = lean_unsigned_to_nat(0u);
v___x_5921_ = lean_array_get_size(v_events_5896_);
v___x_5922_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9));
v___x_5923_ = lean_nat_dec_lt(v___x_5920_, v___x_5921_);
if (v___x_5923_ == 0)
{
lean_dec_ref(v___f_5899_);
lean_dec_ref(v___f_5897_);
lean_dec_ref(v_events_5896_);
lean_dec_ref(v_a_5893_);
goto v___jp_5902_;
}
else
{
if (v___x_5923_ == 0)
{
lean_dec_ref(v___f_5899_);
lean_dec_ref(v___f_5897_);
lean_dec_ref(v_events_5896_);
lean_dec_ref(v_a_5893_);
goto v___jp_5902_;
}
else
{
size_t v___x_5924_; size_t v___x_5925_; lean_object* v___x_5926_; uint8_t v___x_5927_; 
v___x_5924_ = ((size_t)0ULL);
v___x_5925_ = lean_usize_of_nat(v___x_5921_);
v___x_5926_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_5922_, v___f_5897_, v_events_5896_, v___x_5924_, v___x_5925_);
v___x_5927_ = lean_unbox(v___x_5926_);
lean_dec(v___x_5926_);
if (v___x_5927_ == 0)
{
lean_dec_ref(v___f_5899_);
lean_dec_ref(v_a_5893_);
goto v___jp_5902_;
}
else
{
lean_object* v___x_5928_; lean_object* v___x_5929_; 
lean_dec_ref(v___f_5895_);
v___x_5928_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg(v_a_5893_);
v___x_5929_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5920_, v___x_5898_, v___x_5928_, v___f_5899_);
return v___x_5929_;
}
}
}
}
}
v___jp_5902_:
{
lean_object* v___x_5903_; lean_object* v___x_5904_; 
v___x_5903_ = lean_box(0);
v___x_5904_ = lean_apply_2(v___f_5895_, v___x_5903_, lean_box(0));
return v___x_5904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed(lean_object* v_h_5930_, lean_object* v_handler_5931_, lean_object* v_a_5932_, lean_object* v___f_5933_, lean_object* v___f_5934_, lean_object* v_events_5935_, lean_object* v___f_5936_, lean_object* v___x_5937_, lean_object* v___f_5938_, lean_object* v_x_5939_, lean_object* v___y_5940_){
_start:
{
uint8_t v___x_9369__boxed_5941_; lean_object* v_res_5942_; 
v___x_9369__boxed_5941_ = lean_unbox(v___x_5937_);
v_res_5942_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11(v_h_5930_, v_handler_5931_, v_a_5932_, v___f_5933_, v___f_5934_, v_events_5935_, v___f_5936_, v___x_9369__boxed_5941_, v___f_5938_, v_x_5939_);
return v_res_5942_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(uint8_t v___x_5943_, lean_object* v_h_5944_, lean_object* v_responseBodyInstance_5945_, lean_object* v_handler_5946_, lean_object* v_config_5947_, lean_object* v_connectionContext_5948_, uint8_t v___x_5949_, lean_object* v___f_5950_, lean_object* v_a_5951_, lean_object* v___f_5952_, lean_object* v_inst_5953_, lean_object* v_x_5954_){
_start:
{
if (lean_obj_tag(v_x_5954_) == 0)
{
lean_object* v_a_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_5964_; 
lean_dec_ref(v_inst_5953_);
lean_dec_ref(v___f_5952_);
lean_dec_ref(v_a_5951_);
lean_dec_ref(v___f_5950_);
lean_dec_ref(v_connectionContext_5948_);
lean_dec_ref(v_config_5947_);
lean_dec(v_handler_5946_);
lean_dec_ref(v_responseBodyInstance_5945_);
lean_dec_ref(v_h_5944_);
v_a_5956_ = lean_ctor_get(v_x_5954_, 0);
v_isSharedCheck_5964_ = !lean_is_exclusive(v_x_5954_);
if (v_isSharedCheck_5964_ == 0)
{
v___x_5958_ = v_x_5954_;
v_isShared_5959_ = v_isSharedCheck_5964_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_a_5956_);
lean_dec(v_x_5954_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_5964_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v___x_5961_; 
if (v_isShared_5959_ == 0)
{
v___x_5961_ = v___x_5958_;
goto v_reusejp_5960_;
}
else
{
lean_object* v_reuseFailAlloc_5963_; 
v_reuseFailAlloc_5963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5963_, 0, v_a_5956_);
v___x_5961_ = v_reuseFailAlloc_5963_;
goto v_reusejp_5960_;
}
v_reusejp_5960_:
{
lean_object* v___x_5962_; 
v___x_5962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5962_, 0, v___x_5961_);
return v___x_5962_;
}
}
}
else
{
lean_object* v_a_5965_; lean_object* v_machine_5966_; lean_object* v_requestStream_5967_; lean_object* v_keepAliveTimeout_5968_; lean_object* v_currentTimeout_5969_; lean_object* v_headerTimeout_5970_; lean_object* v_response_5971_; lean_object* v_respStream_5972_; uint8_t v_requiresData_5973_; lean_object* v_expectData_5974_; uint8_t v_handlerDispatched_5975_; lean_object* v_pendingHead_5976_; uint8_t v_requestFinalOffered_5977_; lean_object* v_handlerTask_5978_; lean_object* v_dateSecond_5979_; uint8_t v_peerClosed_5980_; uint8_t v_requestEnded_5981_; lean_object* v___x_5983_; uint8_t v_isShared_5984_; uint8_t v_isSharedCheck_6003_; 
v_a_5965_ = lean_ctor_get(v_x_5954_, 0);
lean_inc(v_a_5965_);
lean_dec_ref_known(v_x_5954_, 1);
v_machine_5966_ = lean_ctor_get(v_a_5965_, 0);
v_requestStream_5967_ = lean_ctor_get(v_a_5965_, 1);
v_keepAliveTimeout_5968_ = lean_ctor_get(v_a_5965_, 2);
v_currentTimeout_5969_ = lean_ctor_get(v_a_5965_, 3);
v_headerTimeout_5970_ = lean_ctor_get(v_a_5965_, 4);
v_response_5971_ = lean_ctor_get(v_a_5965_, 5);
v_respStream_5972_ = lean_ctor_get(v_a_5965_, 6);
v_requiresData_5973_ = lean_ctor_get_uint8(v_a_5965_, sizeof(void*)*11);
v_expectData_5974_ = lean_ctor_get(v_a_5965_, 7);
v_handlerDispatched_5975_ = lean_ctor_get_uint8(v_a_5965_, sizeof(void*)*11 + 1);
v_pendingHead_5976_ = lean_ctor_get(v_a_5965_, 8);
v_requestFinalOffered_5977_ = lean_ctor_get_uint8(v_a_5965_, sizeof(void*)*11 + 2);
v_handlerTask_5978_ = lean_ctor_get(v_a_5965_, 9);
v_dateSecond_5979_ = lean_ctor_get(v_a_5965_, 10);
v_peerClosed_5980_ = lean_ctor_get_uint8(v_a_5965_, sizeof(void*)*11 + 3);
v_requestEnded_5981_ = lean_ctor_get_uint8(v_a_5965_, sizeof(void*)*11 + 4);
v_isSharedCheck_6003_ = !lean_is_exclusive(v_a_5965_);
if (v_isSharedCheck_6003_ == 0)
{
v___x_5983_ = v_a_5965_;
v_isShared_5984_ = v_isSharedCheck_6003_;
goto v_resetjp_5982_;
}
else
{
lean_inc(v_dateSecond_5979_);
lean_inc(v_handlerTask_5978_);
lean_inc(v_pendingHead_5976_);
lean_inc(v_expectData_5974_);
lean_inc(v_respStream_5972_);
lean_inc(v_response_5971_);
lean_inc(v_headerTimeout_5970_);
lean_inc(v_currentTimeout_5969_);
lean_inc(v_keepAliveTimeout_5968_);
lean_inc(v_requestStream_5967_);
lean_inc(v_machine_5966_);
lean_dec(v_a_5965_);
v___x_5983_ = lean_box(0);
v_isShared_5984_ = v_isSharedCheck_6003_;
goto v_resetjp_5982_;
}
v_resetjp_5982_:
{
lean_object* v___x_5985_; lean_object* v_snd_5986_; lean_object* v_fst_5987_; lean_object* v_events_5988_; lean_object* v_output_5989_; lean_object* v___x_5991_; 
v___x_5985_ = l_Std_Http_Protocol_H1_Machine_step(v___x_5943_, v_machine_5966_);
v_snd_5986_ = lean_ctor_get(v___x_5985_, 1);
lean_inc(v_snd_5986_);
v_fst_5987_ = lean_ctor_get(v___x_5985_, 0);
lean_inc(v_fst_5987_);
lean_dec_ref(v___x_5985_);
v_events_5988_ = lean_ctor_get(v_snd_5986_, 0);
lean_inc_ref(v_events_5988_);
v_output_5989_ = lean_ctor_get(v_snd_5986_, 1);
lean_inc_ref(v_output_5989_);
lean_dec(v_snd_5986_);
if (v_isShared_5984_ == 0)
{
lean_ctor_set(v___x_5983_, 0, v_fst_5987_);
v___x_5991_ = v___x_5983_;
goto v_reusejp_5990_;
}
else
{
lean_object* v_reuseFailAlloc_6002_; 
v_reuseFailAlloc_6002_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v_reuseFailAlloc_6002_, 0, v_fst_5987_);
lean_ctor_set(v_reuseFailAlloc_6002_, 1, v_requestStream_5967_);
lean_ctor_set(v_reuseFailAlloc_6002_, 2, v_keepAliveTimeout_5968_);
lean_ctor_set(v_reuseFailAlloc_6002_, 3, v_currentTimeout_5969_);
lean_ctor_set(v_reuseFailAlloc_6002_, 4, v_headerTimeout_5970_);
lean_ctor_set(v_reuseFailAlloc_6002_, 5, v_response_5971_);
lean_ctor_set(v_reuseFailAlloc_6002_, 6, v_respStream_5972_);
lean_ctor_set(v_reuseFailAlloc_6002_, 7, v_expectData_5974_);
lean_ctor_set(v_reuseFailAlloc_6002_, 8, v_pendingHead_5976_);
lean_ctor_set(v_reuseFailAlloc_6002_, 9, v_handlerTask_5978_);
lean_ctor_set(v_reuseFailAlloc_6002_, 10, v_dateSecond_5979_);
lean_ctor_set_uint8(v_reuseFailAlloc_6002_, sizeof(void*)*11, v_requiresData_5973_);
lean_ctor_set_uint8(v_reuseFailAlloc_6002_, sizeof(void*)*11 + 1, v_handlerDispatched_5975_);
lean_ctor_set_uint8(v_reuseFailAlloc_6002_, sizeof(void*)*11 + 2, v_requestFinalOffered_5977_);
lean_ctor_set_uint8(v_reuseFailAlloc_6002_, sizeof(void*)*11 + 3, v_peerClosed_5980_);
lean_ctor_set_uint8(v_reuseFailAlloc_6002_, sizeof(void*)*11 + 4, v_requestEnded_5981_);
v___x_5991_ = v_reuseFailAlloc_6002_;
goto v_reusejp_5990_;
}
v_reusejp_5990_:
{
lean_object* v___f_5992_; lean_object* v___x_5993_; lean_object* v___f_5994_; lean_object* v___f_5995_; lean_object* v___x_5996_; lean_object* v___f_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; 
lean_inc_ref(v___x_5991_);
v___f_5992_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_5992_, 0, v___x_5991_);
v___x_5993_ = lean_box(v___x_5949_);
lean_inc_ref(v_events_5988_);
lean_inc_n(v_handler_5946_, 2);
lean_inc_ref_n(v_h_5944_, 2);
v___f_5994_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__10___boxed), 11, 9);
lean_closure_set(v___f_5994_, 0, v_h_5944_);
lean_closure_set(v___f_5994_, 1, v_responseBodyInstance_5945_);
lean_closure_set(v___f_5994_, 2, v_handler_5946_);
lean_closure_set(v___f_5994_, 3, v_config_5947_);
lean_closure_set(v___f_5994_, 4, v_connectionContext_5948_);
lean_closure_set(v___f_5994_, 5, v_events_5988_);
lean_closure_set(v___f_5994_, 6, v___x_5991_);
lean_closure_set(v___f_5994_, 7, v___x_5993_);
lean_closure_set(v___f_5994_, 8, v___f_5950_);
lean_inc_ref(v___f_5994_);
lean_inc_ref(v___f_5992_);
lean_inc_ref_n(v_a_5951_, 2);
v___f_5995_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__12___boxed), 7, 5);
lean_closure_set(v___f_5995_, 0, v_h_5944_);
lean_closure_set(v___f_5995_, 1, v_handler_5946_);
lean_closure_set(v___f_5995_, 2, v_a_5951_);
lean_closure_set(v___f_5995_, 3, v___f_5992_);
lean_closure_set(v___f_5995_, 4, v___f_5994_);
v___x_5996_ = lean_box(v___x_5949_);
v___f_5997_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__11___boxed), 11, 9);
lean_closure_set(v___f_5997_, 0, v_h_5944_);
lean_closure_set(v___f_5997_, 1, v_handler_5946_);
lean_closure_set(v___f_5997_, 2, v_a_5951_);
lean_closure_set(v___f_5997_, 3, v___f_5992_);
lean_closure_set(v___f_5997_, 4, v___f_5994_);
lean_closure_set(v___f_5997_, 5, v_events_5988_);
lean_closure_set(v___f_5997_, 6, v___f_5952_);
lean_closure_set(v___f_5997_, 7, v___x_5996_);
lean_closure_set(v___f_5997_, 8, v___f_5995_);
v___x_5998_ = lean_unsigned_to_nat(65536u);
v___x_5999_ = lean_unsigned_to_nat(0u);
v___x_6000_ = l_Std_Http_Internal_Outbox_push___redArg(v_inst_5953_, v_a_5951_, v_output_5989_, v___x_5998_);
v___x_6001_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5999_, v___x_5949_, v___x_6000_, v___f_5997_);
return v___x_6001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed(lean_object* v___x_6004_, lean_object* v_h_6005_, lean_object* v_responseBodyInstance_6006_, lean_object* v_handler_6007_, lean_object* v_config_6008_, lean_object* v_connectionContext_6009_, lean_object* v___x_6010_, lean_object* v___f_6011_, lean_object* v_a_6012_, lean_object* v___f_6013_, lean_object* v_inst_6014_, lean_object* v_x_6015_, lean_object* v___y_6016_){
_start:
{
uint8_t v___x_9454__boxed_6017_; uint8_t v___x_9455__boxed_6018_; lean_object* v_res_6019_; 
v___x_9454__boxed_6017_ = lean_unbox(v___x_6004_);
v___x_9455__boxed_6018_ = lean_unbox(v___x_6010_);
v_res_6019_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13(v___x_9454__boxed_6017_, v_h_6005_, v_responseBodyInstance_6006_, v_handler_6007_, v_config_6008_, v_connectionContext_6009_, v___x_9455__boxed_6018_, v___f_6011_, v_a_6012_, v___f_6013_, v_inst_6014_, v_x_6015_);
return v_res_6019_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(lean_object* v_h_6020_, lean_object* v_responseBodyInstance_6021_, lean_object* v_handler_6022_, lean_object* v_config_6023_, lean_object* v_connectionContext_6024_, uint8_t v___x_6025_, lean_object* v___f_6026_, lean_object* v_a_6027_, lean_object* v___f_6028_, lean_object* v_inst_6029_, lean_object* v_x_6030_, lean_object* v_____s_6031_){
_start:
{
lean_object* v_machine_6033_; lean_object* v_reader_6034_; lean_object* v_writer_6035_; lean_object* v_state_6036_; uint8_t v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___f_6040_; lean_object* v___y_6042_; lean_object* v_val_6043_; 
v_machine_6033_ = lean_ctor_get(v_____s_6031_, 0);
v_reader_6034_ = lean_ctor_get(v_machine_6033_, 0);
v_writer_6035_ = lean_ctor_get(v_machine_6033_, 1);
v_state_6036_ = lean_ctor_get(v_reader_6034_, 0);
v___x_6037_ = 0;
v___x_6038_ = lean_box(v___x_6037_);
v___x_6039_ = lean_box(v___x_6025_);
lean_inc_ref(v_config_6023_);
v___f_6040_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__13___boxed), 13, 11);
lean_closure_set(v___f_6040_, 0, v___x_6038_);
lean_closure_set(v___f_6040_, 1, v_h_6020_);
lean_closure_set(v___f_6040_, 2, v_responseBodyInstance_6021_);
lean_closure_set(v___f_6040_, 3, v_handler_6022_);
lean_closure_set(v___f_6040_, 4, v_config_6023_);
lean_closure_set(v___f_6040_, 5, v_connectionContext_6024_);
lean_closure_set(v___f_6040_, 6, v___x_6039_);
lean_closure_set(v___f_6040_, 7, v___f_6026_);
lean_closure_set(v___f_6040_, 8, v_a_6027_);
lean_closure_set(v___f_6040_, 9, v___f_6028_);
lean_closure_set(v___f_6040_, 10, v_inst_6029_);
if (lean_obj_tag(v_state_6036_) == 6)
{
lean_object* v_state_6065_; 
v_state_6065_ = lean_ctor_get(v_writer_6035_, 2);
if (lean_obj_tag(v_state_6065_) == 7)
{
lean_object* v_outputData_6066_; lean_object* v_size_6067_; lean_object* v___x_6068_; uint8_t v___x_6069_; 
v_outputData_6066_ = lean_ctor_get(v_writer_6035_, 1);
v_size_6067_ = lean_ctor_get(v_outputData_6066_, 1);
v___x_6068_ = lean_unsigned_to_nat(0u);
v___x_6069_ = lean_nat_dec_eq(v_size_6067_, v___x_6068_);
if (v___x_6069_ == 0)
{
goto v___jp_6046_;
}
else
{
lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; 
lean_dec_ref(v___f_6040_);
lean_dec_ref(v_config_6023_);
v___x_6070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6070_, 0, v_____s_6031_);
v___x_6071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6070_);
v___x_6072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6071_);
return v___x_6072_;
}
}
else
{
goto v___jp_6046_;
}
}
else
{
goto v___jp_6046_;
}
v___jp_6041_:
{
lean_object* v___x_6044_; lean_object* v___x_6045_; 
v___x_6044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6044_, 0, v_val_6043_);
v___x_6045_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_6042_, v___x_6025_, v___x_6044_, v___f_6040_);
return v___x_6045_;
}
v___jp_6046_:
{
lean_object* v___x_6047_; lean_object* v___x_6048_; 
v___x_6047_ = lean_unsigned_to_nat(0u);
v___x_6048_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(v_config_6023_, v_____s_6031_);
lean_dec_ref(v_config_6023_);
if (lean_obj_tag(v___x_6048_) == 0)
{
lean_object* v_a_6049_; lean_object* v___x_6051_; uint8_t v_isShared_6052_; uint8_t v_isSharedCheck_6056_; 
v_a_6049_ = lean_ctor_get(v___x_6048_, 0);
v_isSharedCheck_6056_ = !lean_is_exclusive(v___x_6048_);
if (v_isSharedCheck_6056_ == 0)
{
v___x_6051_ = v___x_6048_;
v_isShared_6052_ = v_isSharedCheck_6056_;
goto v_resetjp_6050_;
}
else
{
lean_inc(v_a_6049_);
lean_dec(v___x_6048_);
v___x_6051_ = lean_box(0);
v_isShared_6052_ = v_isSharedCheck_6056_;
goto v_resetjp_6050_;
}
v_resetjp_6050_:
{
lean_object* v___x_6054_; 
if (v_isShared_6052_ == 0)
{
lean_ctor_set_tag(v___x_6051_, 1);
v___x_6054_ = v___x_6051_;
goto v_reusejp_6053_;
}
else
{
lean_object* v_reuseFailAlloc_6055_; 
v_reuseFailAlloc_6055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6055_, 0, v_a_6049_);
v___x_6054_ = v_reuseFailAlloc_6055_;
goto v_reusejp_6053_;
}
v_reusejp_6053_:
{
v___y_6042_ = v___x_6047_;
v_val_6043_ = v___x_6054_;
goto v___jp_6041_;
}
}
}
else
{
lean_object* v_a_6057_; lean_object* v___x_6059_; uint8_t v_isShared_6060_; uint8_t v_isSharedCheck_6064_; 
v_a_6057_ = lean_ctor_get(v___x_6048_, 0);
v_isSharedCheck_6064_ = !lean_is_exclusive(v___x_6048_);
if (v_isSharedCheck_6064_ == 0)
{
v___x_6059_ = v___x_6048_;
v_isShared_6060_ = v_isSharedCheck_6064_;
goto v_resetjp_6058_;
}
else
{
lean_inc(v_a_6057_);
lean_dec(v___x_6048_);
v___x_6059_ = lean_box(0);
v_isShared_6060_ = v_isSharedCheck_6064_;
goto v_resetjp_6058_;
}
v_resetjp_6058_:
{
lean_object* v___x_6062_; 
if (v_isShared_6060_ == 0)
{
lean_ctor_set_tag(v___x_6059_, 0);
v___x_6062_ = v___x_6059_;
goto v_reusejp_6061_;
}
else
{
lean_object* v_reuseFailAlloc_6063_; 
v_reuseFailAlloc_6063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6063_, 0, v_a_6057_);
v___x_6062_ = v_reuseFailAlloc_6063_;
goto v_reusejp_6061_;
}
v_reusejp_6061_:
{
v___y_6042_ = v___x_6047_;
v_val_6043_ = v___x_6062_;
goto v___jp_6041_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed(lean_object* v_h_6073_, lean_object* v_responseBodyInstance_6074_, lean_object* v_handler_6075_, lean_object* v_config_6076_, lean_object* v_connectionContext_6077_, lean_object* v___x_6078_, lean_object* v___f_6079_, lean_object* v_a_6080_, lean_object* v___f_6081_, lean_object* v_inst_6082_, lean_object* v_x_6083_, lean_object* v_____s_6084_, lean_object* v___y_6085_){
_start:
{
uint8_t v___x_9538__boxed_6086_; lean_object* v_res_6087_; 
v___x_9538__boxed_6086_ = lean_unbox(v___x_6078_);
v_res_6087_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14(v_h_6073_, v_responseBodyInstance_6074_, v_handler_6075_, v_config_6076_, v_connectionContext_6077_, v___x_9538__boxed_6086_, v___f_6079_, v_a_6080_, v___f_6081_, v_inst_6082_, v_x_6083_, v_____s_6084_);
return v_res_6087_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(lean_object* v_a_6088_, lean_object* v_maximumRecvSize_6089_, lean_object* v_inst_6090_, lean_object* v_socket_6091_, lean_object* v_lingeringTimeout_6092_, lean_object* v_connectionContext_6093_, lean_object* v_x_6094_){
_start:
{
if (lean_obj_tag(v_x_6094_) == 0)
{
lean_object* v_a_6098_; lean_object* v___x_6100_; uint8_t v_isShared_6101_; uint8_t v_isSharedCheck_6106_; 
lean_dec_ref(v_connectionContext_6093_);
lean_dec(v_lingeringTimeout_6092_);
lean_dec(v_socket_6091_);
lean_dec_ref(v_inst_6090_);
v_a_6098_ = lean_ctor_get(v_x_6094_, 0);
v_isSharedCheck_6106_ = !lean_is_exclusive(v_x_6094_);
if (v_isSharedCheck_6106_ == 0)
{
v___x_6100_ = v_x_6094_;
v_isShared_6101_ = v_isSharedCheck_6106_;
goto v_resetjp_6099_;
}
else
{
lean_inc(v_a_6098_);
lean_dec(v_x_6094_);
v___x_6100_ = lean_box(0);
v_isShared_6101_ = v_isSharedCheck_6106_;
goto v_resetjp_6099_;
}
v_resetjp_6099_:
{
lean_object* v___x_6103_; 
if (v_isShared_6101_ == 0)
{
v___x_6103_ = v___x_6100_;
goto v_reusejp_6102_;
}
else
{
lean_object* v_reuseFailAlloc_6105_; 
v_reuseFailAlloc_6105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6105_, 0, v_a_6098_);
v___x_6103_ = v_reuseFailAlloc_6105_;
goto v_reusejp_6102_;
}
v_reusejp_6102_:
{
lean_object* v___x_6104_; 
v___x_6104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6103_);
return v___x_6104_;
}
}
}
else
{
lean_object* v_a_6107_; uint8_t v___x_6108_; 
v_a_6107_ = lean_ctor_get(v_x_6094_, 0);
lean_inc(v_a_6107_);
lean_dec_ref_known(v_x_6094_, 1);
v___x_6108_ = lean_unbox(v_a_6107_);
lean_dec(v_a_6107_);
if (v___x_6108_ == 0)
{
uint8_t v___x_6109_; 
v___x_6109_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(v_a_6088_);
if (v___x_6109_ == 0)
{
lean_dec_ref(v_connectionContext_6093_);
lean_dec(v_lingeringTimeout_6092_);
lean_dec(v_socket_6091_);
lean_dec_ref(v_inst_6090_);
goto v___jp_6096_;
}
else
{
uint64_t v___x_6110_; lean_object* v___x_6111_; 
v___x_6110_ = lean_uint64_of_nat(v_maximumRecvSize_6089_);
v___x_6111_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(v_inst_6090_, v_socket_6091_, v_lingeringTimeout_6092_, v___x_6110_, v_connectionContext_6093_);
return v___x_6111_;
}
}
else
{
lean_dec_ref(v_connectionContext_6093_);
lean_dec(v_lingeringTimeout_6092_);
lean_dec(v_socket_6091_);
lean_dec_ref(v_inst_6090_);
goto v___jp_6096_;
}
}
v___jp_6096_:
{
lean_object* v___x_6097_; 
v___x_6097_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_6097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed(lean_object* v_a_6112_, lean_object* v_maximumRecvSize_6113_, lean_object* v_inst_6114_, lean_object* v_socket_6115_, lean_object* v_lingeringTimeout_6116_, lean_object* v_connectionContext_6117_, lean_object* v_x_6118_, lean_object* v___y_6119_){
_start:
{
lean_object* v_res_6120_; 
v_res_6120_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15(v_a_6112_, v_maximumRecvSize_6113_, v_inst_6114_, v_socket_6115_, v_lingeringTimeout_6116_, v_connectionContext_6117_, v_x_6118_);
lean_dec(v_maximumRecvSize_6113_);
lean_dec_ref(v_a_6112_);
return v_res_6120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(lean_object* v_a_6121_, uint8_t v___x_6122_, lean_object* v___f_6123_, lean_object* v_x_6124_){
_start:
{
if (lean_obj_tag(v_x_6124_) == 0)
{
lean_object* v___x_6126_; 
lean_dec_ref(v___f_6123_);
v___x_6126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6126_, 0, v_x_6124_);
return v___x_6126_;
}
else
{
lean_object* v___x_6128_; uint8_t v_isShared_6129_; uint8_t v_isSharedCheck_6138_; 
v_isSharedCheck_6138_ = !lean_is_exclusive(v_x_6124_);
if (v_isSharedCheck_6138_ == 0)
{
lean_object* v_unused_6139_; 
v_unused_6139_ = lean_ctor_get(v_x_6124_, 0);
lean_dec(v_unused_6139_);
v___x_6128_ = v_x_6124_;
v_isShared_6129_ = v_isSharedCheck_6138_;
goto v_resetjp_6127_;
}
else
{
lean_dec(v_x_6124_);
v___x_6128_ = lean_box(0);
v_isShared_6129_ = v_isSharedCheck_6138_;
goto v_resetjp_6127_;
}
v_resetjp_6127_:
{
lean_object* v___x_6130_; uint8_t v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6134_; 
v___x_6130_ = lean_unsigned_to_nat(0u);
v___x_6131_ = l_Std_Http_Internal_Outbox_failed___redArg(v_a_6121_);
v___x_6132_ = lean_box(v___x_6131_);
if (v_isShared_6129_ == 0)
{
lean_ctor_set(v___x_6128_, 0, v___x_6132_);
v___x_6134_ = v___x_6128_;
goto v_reusejp_6133_;
}
else
{
lean_object* v_reuseFailAlloc_6137_; 
v_reuseFailAlloc_6137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6137_, 0, v___x_6132_);
v___x_6134_ = v_reuseFailAlloc_6137_;
goto v_reusejp_6133_;
}
v_reusejp_6133_:
{
lean_object* v___x_6135_; lean_object* v___x_6136_; 
v___x_6135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6134_);
v___x_6136_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6130_, v___x_6122_, v___x_6135_, v___f_6123_);
return v___x_6136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed(lean_object* v_a_6140_, lean_object* v___x_6141_, lean_object* v___f_6142_, lean_object* v_x_6143_, lean_object* v___y_6144_){
_start:
{
uint8_t v___x_9679__boxed_6145_; lean_object* v_res_6146_; 
v___x_9679__boxed_6145_ = lean_unbox(v___x_6141_);
v_res_6146_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16(v_a_6140_, v___x_9679__boxed_6145_, v___f_6142_, v_x_6143_);
lean_dec_ref(v_a_6140_);
return v_res_6146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(lean_object* v_h_6147_, lean_object* v_handler_6148_, lean_object* v_a_6149_, uint8_t v___x_6150_, lean_object* v___f_6151_, lean_object* v_x_6152_){
_start:
{
if (lean_obj_tag(v_x_6152_) == 0)
{
lean_object* v___x_6154_; 
lean_dec_ref(v___f_6151_);
lean_dec(v_handler_6148_);
lean_dec_ref(v_h_6147_);
v___x_6154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6154_, 0, v_x_6152_);
return v___x_6154_;
}
else
{
lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; 
lean_dec_ref_known(v_x_6152_, 1);
v___x_6155_ = lean_unsigned_to_nat(0u);
v___x_6156_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_h_6147_, v_handler_6148_, v_a_6149_);
v___x_6157_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6155_, v___x_6150_, v___x_6156_, v___f_6151_);
return v___x_6157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed(lean_object* v_h_6158_, lean_object* v_handler_6159_, lean_object* v_a_6160_, lean_object* v___x_6161_, lean_object* v___f_6162_, lean_object* v_x_6163_, lean_object* v___y_6164_){
_start:
{
uint8_t v___x_9724__boxed_6165_; lean_object* v_res_6166_; 
v___x_9724__boxed_6165_ = lean_unbox(v___x_6161_);
v_res_6166_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17(v_h_6158_, v_handler_6159_, v_a_6160_, v___x_9724__boxed_6165_, v___f_6162_, v_x_6163_);
lean_dec_ref(v_a_6160_);
return v_res_6166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(lean_object* v_a_6167_, uint8_t v___x_6168_, lean_object* v___f_6169_, lean_object* v_____r_6170_){
_start:
{
lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; 
v___x_6172_ = lean_unsigned_to_nat(0u);
v___x_6173_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_a_6167_);
v___x_6174_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6172_, v___x_6168_, v___x_6173_, v___f_6169_);
return v___x_6174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed(lean_object* v_a_6175_, lean_object* v___x_6176_, lean_object* v___f_6177_, lean_object* v_____r_6178_, lean_object* v___y_6179_){
_start:
{
uint8_t v___x_9749__boxed_6180_; lean_object* v_res_6181_; 
v___x_9749__boxed_6180_ = lean_unbox(v___x_6176_);
v_res_6181_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18(v_a_6175_, v___x_9749__boxed_6180_, v___f_6177_, v_____r_6178_);
return v_res_6181_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(lean_object* v___f_6182_, lean_object* v_x_6183_){
_start:
{
if (lean_obj_tag(v_x_6183_) == 0)
{
lean_object* v___x_6185_; 
lean_dec_ref(v___f_6182_);
v___x_6185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6185_, 0, v_x_6183_);
return v___x_6185_;
}
else
{
lean_object* v_a_6186_; lean_object* v___x_6187_; 
v_a_6186_ = lean_ctor_get(v_x_6183_, 0);
lean_inc(v_a_6186_);
lean_dec_ref_known(v_x_6183_, 1);
v___x_6187_ = lean_apply_2(v___f_6182_, v_a_6186_, lean_box(0));
return v___x_6187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed(lean_object* v___f_6188_, lean_object* v_x_6189_, lean_object* v___y_6190_){
_start:
{
lean_object* v_res_6191_; 
v_res_6191_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19(v___f_6188_, v_x_6189_);
return v_res_6191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(lean_object* v_a_6192_, lean_object* v___f_6193_, uint8_t v___x_6194_, lean_object* v___f_6195_, lean_object* v___f_6196_, lean_object* v_____r_6197_){
_start:
{
lean_object* v_handlerTask_6199_; 
v_handlerTask_6199_ = lean_ctor_get(v_a_6192_, 9);
lean_inc(v_handlerTask_6199_);
lean_dec_ref(v_a_6192_);
if (lean_obj_tag(v_handlerTask_6199_) == 1)
{
lean_object* v_val_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; 
lean_dec_ref(v___f_6196_);
v_val_6200_ = lean_ctor_get(v_handlerTask_6199_, 0);
lean_inc(v_val_6200_);
lean_dec_ref_known(v_handlerTask_6199_, 1);
v___x_6201_ = lean_alloc_closure((void*)(l_Std_Async_Async_ofTask___boxed), 3, 2);
lean_closure_set(v___x_6201_, 0, lean_box(0));
lean_closure_set(v___x_6201_, 1, v_val_6200_);
v___x_6202_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___boxed), 6, 5);
lean_closure_set(v___x_6202_, 0, lean_box(0));
lean_closure_set(v___x_6202_, 1, lean_box(0));
lean_closure_set(v___x_6202_, 2, lean_box(0));
lean_closure_set(v___x_6202_, 3, v___x_6201_);
lean_closure_set(v___x_6202_, 4, v___f_6193_);
v___x_6203_ = lean_unsigned_to_nat(0u);
v___x_6204_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_6204_, 0, lean_box(0));
lean_closure_set(v___x_6204_, 1, v___x_6202_);
v___x_6205_ = lean_io_as_task(v___x_6204_, v___x_6203_);
lean_dec_ref(v___x_6205_);
v___x_6206_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
v___x_6207_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6203_, v___x_6194_, v___x_6206_, v___f_6195_);
return v___x_6207_;
}
else
{
lean_object* v___x_6208_; lean_object* v___x_6209_; 
lean_dec(v_handlerTask_6199_);
lean_dec_ref(v___f_6195_);
lean_dec_ref(v___f_6193_);
v___x_6208_ = lean_box(0);
v___x_6209_ = lean_apply_2(v___f_6196_, v___x_6208_, lean_box(0));
return v___x_6209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed(lean_object* v_a_6210_, lean_object* v___f_6211_, lean_object* v___x_6212_, lean_object* v___f_6213_, lean_object* v___f_6214_, lean_object* v_____r_6215_, lean_object* v___y_6216_){
_start:
{
uint8_t v___x_9791__boxed_6217_; lean_object* v_res_6218_; 
v___x_9791__boxed_6217_ = lean_unbox(v___x_6212_);
v_res_6218_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20(v_a_6210_, v___f_6211_, v___x_9791__boxed_6217_, v___f_6213_, v___f_6214_, v_____r_6215_);
return v_res_6218_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__22(lean_object* v_close_6219_, lean_object* v_val_6220_, uint8_t v___x_6221_, lean_object* v___f_6222_, lean_object* v___f_6223_, lean_object* v_x_6224_){
_start:
{
if (lean_obj_tag(v_x_6224_) == 0)
{
lean_object* v_a_6226_; lean_object* v___x_6228_; uint8_t v_isShared_6229_; uint8_t v_isSharedCheck_6234_; 
lean_dec_ref(v___f_6223_);
lean_dec_ref(v___f_6222_);
lean_dec(v_val_6220_);
lean_dec_ref(v_close_6219_);
v_a_6226_ = lean_ctor_get(v_x_6224_, 0);
v_isSharedCheck_6234_ = !lean_is_exclusive(v_x_6224_);
if (v_isSharedCheck_6234_ == 0)
{
v___x_6228_ = v_x_6224_;
v_isShared_6229_ = v_isSharedCheck_6234_;
goto v_resetjp_6227_;
}
else
{
lean_inc(v_a_6226_);
lean_dec(v_x_6224_);
v___x_6228_ = lean_box(0);
v_isShared_6229_ = v_isSharedCheck_6234_;
goto v_resetjp_6227_;
}
v_resetjp_6227_:
{
lean_object* v___x_6231_; 
if (v_isShared_6229_ == 0)
{
v___x_6231_ = v___x_6228_;
goto v_reusejp_6230_;
}
else
{
lean_object* v_reuseFailAlloc_6233_; 
v_reuseFailAlloc_6233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6233_, 0, v_a_6226_);
v___x_6231_ = v_reuseFailAlloc_6233_;
goto v_reusejp_6230_;
}
v_reusejp_6230_:
{
lean_object* v___x_6232_; 
v___x_6232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6232_, 0, v___x_6231_);
return v___x_6232_;
}
}
}
else
{
lean_object* v_a_6235_; uint8_t v___x_6236_; 
v_a_6235_ = lean_ctor_get(v_x_6224_, 0);
lean_inc(v_a_6235_);
lean_dec_ref_known(v_x_6224_, 1);
v___x_6236_ = lean_unbox(v_a_6235_);
lean_dec(v_a_6235_);
if (v___x_6236_ == 0)
{
lean_object* v___x_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; 
lean_dec_ref(v___f_6223_);
v___x_6237_ = lean_unsigned_to_nat(0u);
v___x_6238_ = lean_apply_2(v_close_6219_, v_val_6220_, lean_box(0));
v___x_6239_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6237_, v___x_6221_, v___x_6238_, v___f_6222_);
return v___x_6239_;
}
else
{
lean_object* v___x_6240_; lean_object* v___x_6241_; 
lean_dec_ref(v___f_6222_);
lean_dec(v_val_6220_);
lean_dec_ref(v_close_6219_);
v___x_6240_ = lean_box(0);
v___x_6241_ = lean_apply_2(v___f_6223_, v___x_6240_, lean_box(0));
return v___x_6241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__22___boxed(lean_object* v_close_6242_, lean_object* v_val_6243_, lean_object* v___x_6244_, lean_object* v___f_6245_, lean_object* v___f_6246_, lean_object* v_x_6247_, lean_object* v___y_6248_){
_start:
{
uint8_t v___x_9833__boxed_6249_; lean_object* v_res_6250_; 
v___x_9833__boxed_6249_ = lean_unbox(v___x_6244_);
v_res_6250_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__22(v_close_6242_, v_val_6243_, v___x_9833__boxed_6249_, v___f_6245_, v___f_6246_, v_x_6247_);
return v_res_6250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__21(lean_object* v_a_6251_, lean_object* v_responseBodyInstance_6252_, uint8_t v___x_6253_, lean_object* v___f_6254_, lean_object* v___f_6255_, lean_object* v_____r_6256_){
_start:
{
lean_object* v_respStream_6258_; 
v_respStream_6258_ = lean_ctor_get(v_a_6251_, 6);
lean_inc(v_respStream_6258_);
lean_dec_ref(v_a_6251_);
if (lean_obj_tag(v_respStream_6258_) == 1)
{
lean_object* v_val_6259_; lean_object* v_close_6260_; lean_object* v_isClosed_6261_; lean_object* v___x_6262_; lean_object* v___f_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; 
v_val_6259_ = lean_ctor_get(v_respStream_6258_, 0);
lean_inc_n(v_val_6259_, 2);
lean_dec_ref_known(v_respStream_6258_, 1);
v_close_6260_ = lean_ctor_get(v_responseBodyInstance_6252_, 1);
lean_inc_ref(v_close_6260_);
v_isClosed_6261_ = lean_ctor_get(v_responseBodyInstance_6252_, 2);
lean_inc_ref(v_isClosed_6261_);
lean_dec_ref(v_responseBodyInstance_6252_);
v___x_6262_ = lean_box(v___x_6253_);
v___f_6263_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__22___boxed), 7, 5);
lean_closure_set(v___f_6263_, 0, v_close_6260_);
lean_closure_set(v___f_6263_, 1, v_val_6259_);
lean_closure_set(v___f_6263_, 2, v___x_6262_);
lean_closure_set(v___f_6263_, 3, v___f_6254_);
lean_closure_set(v___f_6263_, 4, v___f_6255_);
v___x_6264_ = lean_unsigned_to_nat(0u);
v___x_6265_ = lean_apply_2(v_isClosed_6261_, v_val_6259_, lean_box(0));
v___x_6266_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6264_, v___x_6253_, v___x_6265_, v___f_6263_);
return v___x_6266_;
}
else
{
lean_object* v___x_6267_; lean_object* v___x_6268_; 
lean_dec(v_respStream_6258_);
lean_dec_ref(v___f_6254_);
lean_dec_ref(v_responseBodyInstance_6252_);
v___x_6267_ = lean_box(0);
v___x_6268_ = lean_apply_2(v___f_6255_, v___x_6267_, lean_box(0));
return v___x_6268_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__21___boxed(lean_object* v_a_6269_, lean_object* v_responseBodyInstance_6270_, lean_object* v___x_6271_, lean_object* v___f_6272_, lean_object* v___f_6273_, lean_object* v_____r_6274_, lean_object* v___y_6275_){
_start:
{
uint8_t v___x_9883__boxed_6276_; lean_object* v_res_6277_; 
v___x_9883__boxed_6276_ = lean_unbox(v___x_6271_);
v_res_6277_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__21(v_a_6269_, v_responseBodyInstance_6270_, v___x_9883__boxed_6276_, v___f_6272_, v___f_6273_, v_____r_6274_);
return v_res_6277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__23(lean_object* v_close_6278_, lean_object* v_socket_6279_, lean_object* v_x_6280_){
_start:
{
lean_object* v_val_6283_; lean_object* v___x_6285_; 
v___x_6285_ = lean_apply_2(v_close_6278_, v_socket_6279_, lean_box(0));
if (lean_obj_tag(v___x_6285_) == 0)
{
lean_object* v_a_6286_; lean_object* v___x_6288_; uint8_t v_isShared_6289_; uint8_t v_isSharedCheck_6293_; 
v_a_6286_ = lean_ctor_get(v___x_6285_, 0);
v_isSharedCheck_6293_ = !lean_is_exclusive(v___x_6285_);
if (v_isSharedCheck_6293_ == 0)
{
v___x_6288_ = v___x_6285_;
v_isShared_6289_ = v_isSharedCheck_6293_;
goto v_resetjp_6287_;
}
else
{
lean_inc(v_a_6286_);
lean_dec(v___x_6285_);
v___x_6288_ = lean_box(0);
v_isShared_6289_ = v_isSharedCheck_6293_;
goto v_resetjp_6287_;
}
v_resetjp_6287_:
{
lean_object* v___x_6291_; 
if (v_isShared_6289_ == 0)
{
lean_ctor_set_tag(v___x_6288_, 1);
v___x_6291_ = v___x_6288_;
goto v_reusejp_6290_;
}
else
{
lean_object* v_reuseFailAlloc_6292_; 
v_reuseFailAlloc_6292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6292_, 0, v_a_6286_);
v___x_6291_ = v_reuseFailAlloc_6292_;
goto v_reusejp_6290_;
}
v_reusejp_6290_:
{
v_val_6283_ = v___x_6291_;
goto v___jp_6282_;
}
}
}
else
{
lean_object* v_a_6294_; lean_object* v___x_6296_; uint8_t v_isShared_6297_; uint8_t v_isSharedCheck_6301_; 
v_a_6294_ = lean_ctor_get(v___x_6285_, 0);
v_isSharedCheck_6301_ = !lean_is_exclusive(v___x_6285_);
if (v_isSharedCheck_6301_ == 0)
{
v___x_6296_ = v___x_6285_;
v_isShared_6297_ = v_isSharedCheck_6301_;
goto v_resetjp_6295_;
}
else
{
lean_inc(v_a_6294_);
lean_dec(v___x_6285_);
v___x_6296_ = lean_box(0);
v_isShared_6297_ = v_isSharedCheck_6301_;
goto v_resetjp_6295_;
}
v_resetjp_6295_:
{
lean_object* v___x_6299_; 
if (v_isShared_6297_ == 0)
{
lean_ctor_set_tag(v___x_6296_, 0);
v___x_6299_ = v___x_6296_;
goto v_reusejp_6298_;
}
else
{
lean_object* v_reuseFailAlloc_6300_; 
v_reuseFailAlloc_6300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6300_, 0, v_a_6294_);
v___x_6299_ = v_reuseFailAlloc_6300_;
goto v_reusejp_6298_;
}
v_reusejp_6298_:
{
v_val_6283_ = v___x_6299_;
goto v___jp_6282_;
}
}
}
v___jp_6282_:
{
lean_object* v___x_6284_; 
v___x_6284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6284_, 0, v_val_6283_);
return v___x_6284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__23___boxed(lean_object* v_close_6302_, lean_object* v_socket_6303_, lean_object* v_x_6304_, lean_object* v___y_6305_){
_start:
{
lean_object* v_res_6306_; 
v_res_6306_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__23(v_close_6302_, v_socket_6303_, v_x_6304_);
lean_dec(v_x_6304_);
return v_res_6306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24(lean_object* v_inst_6308_, lean_object* v_maximumRecvSize_6309_, lean_object* v_socket_6310_, lean_object* v_lingeringTimeout_6311_, lean_object* v_connectionContext_6312_, lean_object* v_a_6313_, uint8_t v___x_6314_, lean_object* v_h_6315_, lean_object* v_handler_6316_, lean_object* v___f_6317_, lean_object* v_responseBodyInstance_6318_, lean_object* v___f_6319_, lean_object* v_x_6320_){
_start:
{
if (lean_obj_tag(v_x_6320_) == 0)
{
lean_object* v_a_6322_; lean_object* v___x_6324_; uint8_t v_isShared_6325_; uint8_t v_isSharedCheck_6330_; 
lean_dec_ref(v___f_6319_);
lean_dec_ref(v_responseBodyInstance_6318_);
lean_dec_ref(v___f_6317_);
lean_dec(v_handler_6316_);
lean_dec_ref(v_h_6315_);
lean_dec_ref(v_a_6313_);
lean_dec_ref(v_connectionContext_6312_);
lean_dec(v_lingeringTimeout_6311_);
lean_dec(v_socket_6310_);
lean_dec(v_maximumRecvSize_6309_);
lean_dec_ref(v_inst_6308_);
v_a_6322_ = lean_ctor_get(v_x_6320_, 0);
v_isSharedCheck_6330_ = !lean_is_exclusive(v_x_6320_);
if (v_isSharedCheck_6330_ == 0)
{
v___x_6324_ = v_x_6320_;
v_isShared_6325_ = v_isSharedCheck_6330_;
goto v_resetjp_6323_;
}
else
{
lean_inc(v_a_6322_);
lean_dec(v_x_6320_);
v___x_6324_ = lean_box(0);
v_isShared_6325_ = v_isSharedCheck_6330_;
goto v_resetjp_6323_;
}
v_resetjp_6323_:
{
lean_object* v___x_6327_; 
if (v_isShared_6325_ == 0)
{
v___x_6327_ = v___x_6324_;
goto v_reusejp_6326_;
}
else
{
lean_object* v_reuseFailAlloc_6329_; 
v_reuseFailAlloc_6329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6329_, 0, v_a_6322_);
v___x_6327_ = v_reuseFailAlloc_6329_;
goto v_reusejp_6326_;
}
v_reusejp_6326_:
{
lean_object* v___x_6328_; 
v___x_6328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6328_, 0, v___x_6327_);
return v___x_6328_;
}
}
}
else
{
lean_object* v_a_6331_; lean_object* v_close_6332_; lean_object* v___f_6333_; lean_object* v___x_6334_; lean_object* v___f_6335_; lean_object* v___x_6336_; lean_object* v___f_6337_; lean_object* v___x_6338_; lean_object* v___f_6339_; lean_object* v___f_6340_; lean_object* v___x_6341_; lean_object* v___f_6342_; lean_object* v___f_6343_; lean_object* v___x_6344_; lean_object* v___f_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; lean_object* v___f_6349_; lean_object* v___x_6350_; lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___y_6354_; 
v_a_6331_ = lean_ctor_get(v_x_6320_, 0);
lean_inc_n(v_a_6331_, 4);
lean_dec_ref_known(v_x_6320_, 1);
v_close_6332_ = lean_ctor_get(v_inst_6308_, 3);
lean_inc_ref(v_close_6332_);
lean_inc(v_socket_6310_);
v___f_6333_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__15___boxed), 8, 6);
lean_closure_set(v___f_6333_, 0, v_a_6331_);
lean_closure_set(v___f_6333_, 1, v_maximumRecvSize_6309_);
lean_closure_set(v___f_6333_, 2, v_inst_6308_);
lean_closure_set(v___f_6333_, 3, v_socket_6310_);
lean_closure_set(v___f_6333_, 4, v_lingeringTimeout_6311_);
lean_closure_set(v___f_6333_, 5, v_connectionContext_6312_);
v___x_6334_ = lean_box(v___x_6314_);
lean_inc_ref_n(v_a_6313_, 2);
v___f_6335_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__16___boxed), 5, 3);
lean_closure_set(v___f_6335_, 0, v_a_6313_);
lean_closure_set(v___f_6335_, 1, v___x_6334_);
lean_closure_set(v___f_6335_, 2, v___f_6333_);
v___x_6336_ = lean_box(v___x_6314_);
v___f_6337_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__17___boxed), 7, 5);
lean_closure_set(v___f_6337_, 0, v_h_6315_);
lean_closure_set(v___f_6337_, 1, v_handler_6316_);
lean_closure_set(v___f_6337_, 2, v_a_6313_);
lean_closure_set(v___f_6337_, 3, v___x_6336_);
lean_closure_set(v___f_6337_, 4, v___f_6335_);
v___x_6338_ = lean_box(v___x_6314_);
v___f_6339_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__18___boxed), 5, 3);
lean_closure_set(v___f_6339_, 0, v_a_6313_);
lean_closure_set(v___f_6339_, 1, v___x_6338_);
lean_closure_set(v___f_6339_, 2, v___f_6337_);
lean_inc_ref(v___f_6339_);
v___f_6340_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 3, 1);
lean_closure_set(v___f_6340_, 0, v___f_6339_);
v___x_6341_ = lean_box(v___x_6314_);
v___f_6342_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__20___boxed), 7, 5);
lean_closure_set(v___f_6342_, 0, v_a_6331_);
lean_closure_set(v___f_6342_, 1, v___f_6317_);
lean_closure_set(v___f_6342_, 2, v___x_6341_);
lean_closure_set(v___f_6342_, 3, v___f_6340_);
lean_closure_set(v___f_6342_, 4, v___f_6339_);
lean_inc_ref(v___f_6342_);
v___f_6343_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__19___boxed), 3, 1);
lean_closure_set(v___f_6343_, 0, v___f_6342_);
v___x_6344_ = lean_box(v___x_6314_);
v___f_6345_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__21___boxed), 7, 5);
lean_closure_set(v___f_6345_, 0, v_a_6331_);
lean_closure_set(v___f_6345_, 1, v_responseBodyInstance_6318_);
lean_closure_set(v___f_6345_, 2, v___x_6344_);
lean_closure_set(v___f_6345_, 3, v___f_6343_);
lean_closure_set(v___f_6345_, 4, v___f_6342_);
v___x_6346_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___closed__0));
v___x_6347_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___boxed), 4, 3);
lean_closure_set(v___x_6347_, 0, lean_box(0));
lean_closure_set(v___x_6347_, 1, v_a_6331_);
lean_closure_set(v___x_6347_, 2, v___x_6346_);
v___x_6348_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___boxed), 6, 5);
lean_closure_set(v___x_6348_, 0, lean_box(0));
lean_closure_set(v___x_6348_, 1, lean_box(0));
lean_closure_set(v___x_6348_, 2, lean_box(0));
lean_closure_set(v___x_6348_, 3, v___x_6347_);
lean_closure_set(v___x_6348_, 4, v___f_6345_);
v___f_6349_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__23___boxed), 4, 2);
lean_closure_set(v___f_6349_, 0, v_close_6332_);
lean_closure_set(v___f_6349_, 1, v_socket_6310_);
v___x_6350_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_6350_, 0, lean_box(0));
lean_closure_set(v___x_6350_, 1, lean_box(0));
lean_closure_set(v___x_6350_, 2, lean_box(0));
lean_closure_set(v___x_6350_, 3, v___f_6319_);
v___x_6351_ = lean_unsigned_to_nat(0u);
v___x_6352_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_6348_, v___f_6349_, v___x_6351_, v___x_6314_);
if (lean_obj_tag(v___x_6352_) == 0)
{
lean_object* v_a_6356_; 
lean_dec_ref(v___x_6350_);
v_a_6356_ = lean_ctor_get(v___x_6352_, 0);
lean_inc(v_a_6356_);
lean_dec_ref_known(v___x_6352_, 1);
if (lean_obj_tag(v_a_6356_) == 0)
{
lean_object* v_a_6357_; lean_object* v___x_6359_; uint8_t v_isShared_6360_; uint8_t v_isSharedCheck_6364_; 
v_a_6357_ = lean_ctor_get(v_a_6356_, 0);
v_isSharedCheck_6364_ = !lean_is_exclusive(v_a_6356_);
if (v_isSharedCheck_6364_ == 0)
{
v___x_6359_ = v_a_6356_;
v_isShared_6360_ = v_isSharedCheck_6364_;
goto v_resetjp_6358_;
}
else
{
lean_inc(v_a_6357_);
lean_dec(v_a_6356_);
v___x_6359_ = lean_box(0);
v_isShared_6360_ = v_isSharedCheck_6364_;
goto v_resetjp_6358_;
}
v_resetjp_6358_:
{
lean_object* v___x_6362_; 
if (v_isShared_6360_ == 0)
{
v___x_6362_ = v___x_6359_;
goto v_reusejp_6361_;
}
else
{
lean_object* v_reuseFailAlloc_6363_; 
v_reuseFailAlloc_6363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6363_, 0, v_a_6357_);
v___x_6362_ = v_reuseFailAlloc_6363_;
goto v_reusejp_6361_;
}
v_reusejp_6361_:
{
v___y_6354_ = v___x_6362_;
goto v___jp_6353_;
}
}
}
else
{
lean_object* v_a_6365_; lean_object* v___x_6367_; uint8_t v_isShared_6368_; uint8_t v_isSharedCheck_6373_; 
v_a_6365_ = lean_ctor_get(v_a_6356_, 0);
v_isSharedCheck_6373_ = !lean_is_exclusive(v_a_6356_);
if (v_isSharedCheck_6373_ == 0)
{
v___x_6367_ = v_a_6356_;
v_isShared_6368_ = v_isSharedCheck_6373_;
goto v_resetjp_6366_;
}
else
{
lean_inc(v_a_6365_);
lean_dec(v_a_6356_);
v___x_6367_ = lean_box(0);
v_isShared_6368_ = v_isSharedCheck_6373_;
goto v_resetjp_6366_;
}
v_resetjp_6366_:
{
lean_object* v_fst_6369_; lean_object* v___x_6371_; 
v_fst_6369_ = lean_ctor_get(v_a_6365_, 0);
lean_inc(v_fst_6369_);
lean_dec(v_a_6365_);
if (v_isShared_6368_ == 0)
{
lean_ctor_set(v___x_6367_, 0, v_fst_6369_);
v___x_6371_ = v___x_6367_;
goto v_reusejp_6370_;
}
else
{
lean_object* v_reuseFailAlloc_6372_; 
v_reuseFailAlloc_6372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6372_, 0, v_fst_6369_);
v___x_6371_ = v_reuseFailAlloc_6372_;
goto v_reusejp_6370_;
}
v_reusejp_6370_:
{
v___y_6354_ = v___x_6371_;
goto v___jp_6353_;
}
}
}
}
else
{
lean_object* v_a_6374_; lean_object* v___x_6376_; uint8_t v_isShared_6377_; uint8_t v_isSharedCheck_6382_; 
v_a_6374_ = lean_ctor_get(v___x_6352_, 0);
v_isSharedCheck_6382_ = !lean_is_exclusive(v___x_6352_);
if (v_isSharedCheck_6382_ == 0)
{
v___x_6376_ = v___x_6352_;
v_isShared_6377_ = v_isSharedCheck_6382_;
goto v_resetjp_6375_;
}
else
{
lean_inc(v_a_6374_);
lean_dec(v___x_6352_);
v___x_6376_ = lean_box(0);
v_isShared_6377_ = v_isSharedCheck_6382_;
goto v_resetjp_6375_;
}
v_resetjp_6375_:
{
lean_object* v___x_6378_; lean_object* v___x_6380_; 
v___x_6378_ = lean_task_map(v___x_6350_, v_a_6374_, v___x_6351_, v___x_6314_);
if (v_isShared_6377_ == 0)
{
lean_ctor_set(v___x_6376_, 0, v___x_6378_);
v___x_6380_ = v___x_6376_;
goto v_reusejp_6379_;
}
else
{
lean_object* v_reuseFailAlloc_6381_; 
v_reuseFailAlloc_6381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6381_, 0, v___x_6378_);
v___x_6380_ = v_reuseFailAlloc_6381_;
goto v_reusejp_6379_;
}
v_reusejp_6379_:
{
return v___x_6380_;
}
}
}
v___jp_6353_:
{
lean_object* v___x_6355_; 
v___x_6355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6355_, 0, v___y_6354_);
return v___x_6355_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___boxed(lean_object* v_inst_6383_, lean_object* v_maximumRecvSize_6384_, lean_object* v_socket_6385_, lean_object* v_lingeringTimeout_6386_, lean_object* v_connectionContext_6387_, lean_object* v_a_6388_, lean_object* v___x_6389_, lean_object* v_h_6390_, lean_object* v_handler_6391_, lean_object* v___f_6392_, lean_object* v_responseBodyInstance_6393_, lean_object* v___f_6394_, lean_object* v_x_6395_, lean_object* v___y_6396_){
_start:
{
uint8_t v___x_9966__boxed_6397_; lean_object* v_res_6398_; 
v___x_9966__boxed_6397_ = lean_unbox(v___x_6389_);
v_res_6398_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24(v_inst_6383_, v_maximumRecvSize_6384_, v_socket_6385_, v_lingeringTimeout_6386_, v_connectionContext_6387_, v_a_6388_, v___x_9966__boxed_6397_, v_h_6390_, v_handler_6391_, v___f_6392_, v_responseBodyInstance_6393_, v___f_6394_, v_x_6395_);
return v_res_6398_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__25(lean_object* v_a_6399_, lean_object* v_x_6400_){
_start:
{
if (lean_obj_tag(v_x_6400_) == 0)
{
lean_object* v_a_6402_; lean_object* v___x_6404_; uint8_t v_isShared_6405_; uint8_t v_isSharedCheck_6410_; 
v_a_6402_ = lean_ctor_get(v_x_6400_, 0);
v_isSharedCheck_6410_ = !lean_is_exclusive(v_x_6400_);
if (v_isSharedCheck_6410_ == 0)
{
v___x_6404_ = v_x_6400_;
v_isShared_6405_ = v_isSharedCheck_6410_;
goto v_resetjp_6403_;
}
else
{
lean_inc(v_a_6402_);
lean_dec(v_x_6400_);
v___x_6404_ = lean_box(0);
v_isShared_6405_ = v_isSharedCheck_6410_;
goto v_resetjp_6403_;
}
v_resetjp_6403_:
{
lean_object* v___x_6407_; 
if (v_isShared_6405_ == 0)
{
v___x_6407_ = v___x_6404_;
goto v_reusejp_6406_;
}
else
{
lean_object* v_reuseFailAlloc_6409_; 
v_reuseFailAlloc_6409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6409_, 0, v_a_6402_);
v___x_6407_ = v_reuseFailAlloc_6409_;
goto v_reusejp_6406_;
}
v_reusejp_6406_:
{
lean_object* v___x_6408_; 
v___x_6408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6408_, 0, v___x_6407_);
return v___x_6408_;
}
}
}
else
{
lean_object* v___x_6411_; lean_object* v___x_6412_; 
lean_dec_ref_known(v_x_6400_, 1);
v___x_6411_ = l_IO_Promise_result_x21___redArg(v_a_6399_);
v___x_6412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6412_, 0, v___x_6411_);
return v___x_6412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__25___boxed(lean_object* v_a_6413_, lean_object* v_x_6414_, lean_object* v___y_6415_){
_start:
{
lean_object* v_res_6416_; 
v_res_6416_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__25(v_a_6413_, v_x_6414_);
lean_dec(v_a_6413_);
return v_res_6416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__26(lean_object* v___f_6417_, lean_object* v___x_6418_, lean_object* v___x_6419_, uint8_t v___x_6420_, lean_object* v_x_6421_){
_start:
{
if (lean_obj_tag(v_x_6421_) == 0)
{
lean_object* v_a_6423_; lean_object* v___x_6425_; uint8_t v_isShared_6426_; uint8_t v_isSharedCheck_6431_; 
lean_dec_ref(v___x_6419_);
lean_dec(v___x_6418_);
lean_dec_ref(v___f_6417_);
v_a_6423_ = lean_ctor_get(v_x_6421_, 0);
v_isSharedCheck_6431_ = !lean_is_exclusive(v_x_6421_);
if (v_isSharedCheck_6431_ == 0)
{
v___x_6425_ = v_x_6421_;
v_isShared_6426_ = v_isSharedCheck_6431_;
goto v_resetjp_6424_;
}
else
{
lean_inc(v_a_6423_);
lean_dec(v_x_6421_);
v___x_6425_ = lean_box(0);
v_isShared_6426_ = v_isSharedCheck_6431_;
goto v_resetjp_6424_;
}
v_resetjp_6424_:
{
lean_object* v___x_6428_; 
if (v_isShared_6426_ == 0)
{
v___x_6428_ = v___x_6425_;
goto v_reusejp_6427_;
}
else
{
lean_object* v_reuseFailAlloc_6430_; 
v_reuseFailAlloc_6430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6430_, 0, v_a_6423_);
v___x_6428_ = v_reuseFailAlloc_6430_;
goto v_reusejp_6427_;
}
v_reusejp_6427_:
{
lean_object* v___x_6429_; 
v___x_6429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6429_, 0, v___x_6428_);
return v___x_6429_;
}
}
}
else
{
lean_object* v_a_6432_; lean_object* v___x_6434_; uint8_t v_isShared_6435_; uint8_t v_isSharedCheck_6443_; 
v_a_6432_ = lean_ctor_get(v_x_6421_, 0);
v_isSharedCheck_6443_ = !lean_is_exclusive(v_x_6421_);
if (v_isSharedCheck_6443_ == 0)
{
v___x_6434_ = v_x_6421_;
v_isShared_6435_ = v_isSharedCheck_6443_;
goto v_resetjp_6433_;
}
else
{
lean_inc(v_a_6432_);
lean_dec(v_x_6421_);
v___x_6434_ = lean_box(0);
v_isShared_6435_ = v_isSharedCheck_6443_;
goto v_resetjp_6433_;
}
v_resetjp_6433_:
{
lean_object* v___f_6436_; lean_object* v___x_6437_; lean_object* v___x_6439_; 
lean_inc(v_a_6432_);
v___f_6436_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__25___boxed), 3, 1);
lean_closure_set(v___f_6436_, 0, v_a_6432_);
lean_inc(v___x_6418_);
v___x_6437_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_6417_, v___x_6418_, v_a_6432_, v___x_6419_);
if (v_isShared_6435_ == 0)
{
lean_ctor_set(v___x_6434_, 0, v___x_6437_);
v___x_6439_ = v___x_6434_;
goto v_reusejp_6438_;
}
else
{
lean_object* v_reuseFailAlloc_6442_; 
v_reuseFailAlloc_6442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6442_, 0, v___x_6437_);
v___x_6439_ = v_reuseFailAlloc_6442_;
goto v_reusejp_6438_;
}
v_reusejp_6438_:
{
lean_object* v___x_6440_; lean_object* v___x_6441_; 
v___x_6440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6440_, 0, v___x_6439_);
v___x_6441_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6418_, v___x_6420_, v___x_6440_, v___f_6436_);
return v___x_6441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__26___boxed(lean_object* v___f_6444_, lean_object* v___x_6445_, lean_object* v___x_6446_, lean_object* v___x_6447_, lean_object* v_x_6448_, lean_object* v___y_6449_){
_start:
{
uint8_t v___x_10139__boxed_6450_; lean_object* v_res_6451_; 
v___x_10139__boxed_6450_ = lean_unbox(v___x_6447_);
v_res_6451_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__26(v___f_6444_, v___x_6445_, v___x_6446_, v___x_10139__boxed_6450_, v_x_6448_);
return v_res_6451_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__27(uint8_t v___x_6452_, lean_object* v_h_6453_, lean_object* v_responseBodyInstance_6454_, lean_object* v_handler_6455_, lean_object* v_config_6456_, lean_object* v___f_6457_, lean_object* v_keepAliveTimeout_6458_, lean_object* v_inst_6459_, lean_object* v_socket_6460_, lean_object* v_connectionContext_6461_, lean_object* v_maximumRecvSize_6462_, lean_object* v_extensions_6463_, lean_object* v___f_6464_, lean_object* v_lingeringTimeout_6465_, lean_object* v___f_6466_, lean_object* v___f_6467_, lean_object* v___x_6468_, lean_object* v_x_6469_){
_start:
{
if (lean_obj_tag(v_x_6469_) == 0)
{
lean_object* v_a_6471_; lean_object* v___x_6473_; uint8_t v_isShared_6474_; uint8_t v_isSharedCheck_6479_; 
lean_dec_ref(v___x_6468_);
lean_dec_ref(v___f_6467_);
lean_dec_ref(v___f_6466_);
lean_dec(v_lingeringTimeout_6465_);
lean_dec_ref(v___f_6464_);
lean_dec(v_extensions_6463_);
lean_dec(v_maximumRecvSize_6462_);
lean_dec_ref(v_connectionContext_6461_);
lean_dec(v_socket_6460_);
lean_dec_ref(v_inst_6459_);
lean_dec(v_keepAliveTimeout_6458_);
lean_dec_ref(v___f_6457_);
lean_dec_ref(v_config_6456_);
lean_dec(v_handler_6455_);
lean_dec_ref(v_responseBodyInstance_6454_);
lean_dec_ref(v_h_6453_);
v_a_6471_ = lean_ctor_get(v_x_6469_, 0);
v_isSharedCheck_6479_ = !lean_is_exclusive(v_x_6469_);
if (v_isSharedCheck_6479_ == 0)
{
v___x_6473_ = v_x_6469_;
v_isShared_6474_ = v_isSharedCheck_6479_;
goto v_resetjp_6472_;
}
else
{
lean_inc(v_a_6471_);
lean_dec(v_x_6469_);
v___x_6473_ = lean_box(0);
v_isShared_6474_ = v_isSharedCheck_6479_;
goto v_resetjp_6472_;
}
v_resetjp_6472_:
{
lean_object* v___x_6476_; 
if (v_isShared_6474_ == 0)
{
v___x_6476_ = v___x_6473_;
goto v_reusejp_6475_;
}
else
{
lean_object* v_reuseFailAlloc_6478_; 
v_reuseFailAlloc_6478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6478_, 0, v_a_6471_);
v___x_6476_ = v_reuseFailAlloc_6478_;
goto v_reusejp_6475_;
}
v_reusejp_6475_:
{
lean_object* v___x_6477_; 
v___x_6477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6477_, 0, v___x_6476_);
return v___x_6477_;
}
}
}
else
{
lean_object* v_a_6480_; lean_object* v___x_6482_; uint8_t v_isShared_6483_; uint8_t v_isSharedCheck_6502_; 
v_a_6480_ = lean_ctor_get(v_x_6469_, 0);
v_isSharedCheck_6502_ = !lean_is_exclusive(v_x_6469_);
if (v_isSharedCheck_6502_ == 0)
{
v___x_6482_ = v_x_6469_;
v_isShared_6483_ = v_isSharedCheck_6502_;
goto v_resetjp_6481_;
}
else
{
lean_inc(v_a_6480_);
lean_dec(v_x_6469_);
v___x_6482_ = lean_box(0);
v_isShared_6483_ = v_isSharedCheck_6502_;
goto v_resetjp_6481_;
}
v_resetjp_6481_:
{
lean_object* v___x_6484_; lean_object* v___f_6485_; lean_object* v___x_6486_; lean_object* v___f_6487_; lean_object* v___x_6488_; lean_object* v___f_6489_; lean_object* v___x_6490_; lean_object* v___f_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___f_6494_; lean_object* v___x_6495_; lean_object* v___x_6497_; 
v___x_6484_ = lean_box(v___x_6452_);
lean_inc(v_maximumRecvSize_6462_);
lean_inc_ref_n(v_connectionContext_6461_, 3);
lean_inc(v_socket_6460_);
lean_inc_ref_n(v_inst_6459_, 2);
lean_inc_n(v_a_6480_, 2);
lean_inc_ref(v_config_6456_);
lean_inc_n(v_handler_6455_, 3);
lean_inc_ref_n(v_responseBodyInstance_6454_, 2);
lean_inc_ref_n(v_h_6453_, 3);
v___f_6485_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__7___boxed), 14, 12);
lean_closure_set(v___f_6485_, 0, v___x_6484_);
lean_closure_set(v___f_6485_, 1, v_h_6453_);
lean_closure_set(v___f_6485_, 2, v_responseBodyInstance_6454_);
lean_closure_set(v___f_6485_, 3, v_handler_6455_);
lean_closure_set(v___f_6485_, 4, v_config_6456_);
lean_closure_set(v___f_6485_, 5, v___f_6457_);
lean_closure_set(v___f_6485_, 6, v_a_6480_);
lean_closure_set(v___f_6485_, 7, v_keepAliveTimeout_6458_);
lean_closure_set(v___f_6485_, 8, v_inst_6459_);
lean_closure_set(v___f_6485_, 9, v_socket_6460_);
lean_closure_set(v___f_6485_, 10, v_connectionContext_6461_);
lean_closure_set(v___f_6485_, 11, v_maximumRecvSize_6462_);
v___x_6486_ = lean_box(v___x_6452_);
v___f_6487_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__8___boxed), 8, 6);
lean_closure_set(v___f_6487_, 0, v_h_6453_);
lean_closure_set(v___f_6487_, 1, v_handler_6455_);
lean_closure_set(v___f_6487_, 2, v_extensions_6463_);
lean_closure_set(v___f_6487_, 3, v_connectionContext_6461_);
lean_closure_set(v___f_6487_, 4, v___x_6486_);
lean_closure_set(v___f_6487_, 5, v___f_6485_);
v___x_6488_ = lean_box(v___x_6452_);
v___f_6489_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__14___boxed), 13, 10);
lean_closure_set(v___f_6489_, 0, v_h_6453_);
lean_closure_set(v___f_6489_, 1, v_responseBodyInstance_6454_);
lean_closure_set(v___f_6489_, 2, v_handler_6455_);
lean_closure_set(v___f_6489_, 3, v_config_6456_);
lean_closure_set(v___f_6489_, 4, v_connectionContext_6461_);
lean_closure_set(v___f_6489_, 5, v___x_6488_);
lean_closure_set(v___f_6489_, 6, v___f_6487_);
lean_closure_set(v___f_6489_, 7, v_a_6480_);
lean_closure_set(v___f_6489_, 8, v___f_6464_);
lean_closure_set(v___f_6489_, 9, v_inst_6459_);
v___x_6490_ = lean_box(v___x_6452_);
v___f_6491_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__24___boxed), 14, 12);
lean_closure_set(v___f_6491_, 0, v_inst_6459_);
lean_closure_set(v___f_6491_, 1, v_maximumRecvSize_6462_);
lean_closure_set(v___f_6491_, 2, v_socket_6460_);
lean_closure_set(v___f_6491_, 3, v_lingeringTimeout_6465_);
lean_closure_set(v___f_6491_, 4, v_connectionContext_6461_);
lean_closure_set(v___f_6491_, 5, v_a_6480_);
lean_closure_set(v___f_6491_, 6, v___x_6490_);
lean_closure_set(v___f_6491_, 7, v_h_6453_);
lean_closure_set(v___f_6491_, 8, v_handler_6455_);
lean_closure_set(v___f_6491_, 9, v___f_6466_);
lean_closure_set(v___f_6491_, 10, v_responseBodyInstance_6454_);
lean_closure_set(v___f_6491_, 11, v___f_6467_);
v___x_6492_ = lean_unsigned_to_nat(0u);
v___x_6493_ = lean_box(v___x_6452_);
v___f_6494_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__26___boxed), 6, 4);
lean_closure_set(v___f_6494_, 0, v___f_6489_);
lean_closure_set(v___f_6494_, 1, v___x_6492_);
lean_closure_set(v___f_6494_, 2, v___x_6468_);
lean_closure_set(v___f_6494_, 3, v___x_6493_);
v___x_6495_ = lean_io_promise_new();
if (v_isShared_6483_ == 0)
{
lean_ctor_set(v___x_6482_, 0, v___x_6495_);
v___x_6497_ = v___x_6482_;
goto v_reusejp_6496_;
}
else
{
lean_object* v_reuseFailAlloc_6501_; 
v_reuseFailAlloc_6501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6501_, 0, v___x_6495_);
v___x_6497_ = v_reuseFailAlloc_6501_;
goto v_reusejp_6496_;
}
v_reusejp_6496_:
{
lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; 
v___x_6498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6498_, 0, v___x_6497_);
v___x_6499_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6492_, v___x_6452_, v___x_6498_, v___f_6494_);
v___x_6500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6492_, v___x_6452_, v___x_6499_, v___f_6491_);
return v___x_6500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__27___boxed(lean_object** _args){
lean_object* v___x_6503_ = _args[0];
lean_object* v_h_6504_ = _args[1];
lean_object* v_responseBodyInstance_6505_ = _args[2];
lean_object* v_handler_6506_ = _args[3];
lean_object* v_config_6507_ = _args[4];
lean_object* v___f_6508_ = _args[5];
lean_object* v_keepAliveTimeout_6509_ = _args[6];
lean_object* v_inst_6510_ = _args[7];
lean_object* v_socket_6511_ = _args[8];
lean_object* v_connectionContext_6512_ = _args[9];
lean_object* v_maximumRecvSize_6513_ = _args[10];
lean_object* v_extensions_6514_ = _args[11];
lean_object* v___f_6515_ = _args[12];
lean_object* v_lingeringTimeout_6516_ = _args[13];
lean_object* v___f_6517_ = _args[14];
lean_object* v___f_6518_ = _args[15];
lean_object* v___x_6519_ = _args[16];
lean_object* v_x_6520_ = _args[17];
lean_object* v___y_6521_ = _args[18];
_start:
{
uint8_t v___x_10196__boxed_6522_; lean_object* v_res_6523_; 
v___x_10196__boxed_6522_ = lean_unbox(v___x_6503_);
v_res_6523_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__27(v___x_10196__boxed_6522_, v_h_6504_, v_responseBodyInstance_6505_, v_handler_6506_, v_config_6507_, v___f_6508_, v_keepAliveTimeout_6509_, v_inst_6510_, v_socket_6511_, v_connectionContext_6512_, v_maximumRecvSize_6513_, v_extensions_6514_, v___f_6515_, v_lingeringTimeout_6516_, v___f_6517_, v___f_6518_, v___x_6519_, v_x_6520_);
return v_res_6523_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__28(lean_object* v_config_6524_, lean_object* v_machine_6525_, lean_object* v_a_6526_, lean_object* v___x_6527_, lean_object* v_h_6528_, lean_object* v_responseBodyInstance_6529_, lean_object* v_handler_6530_, lean_object* v___f_6531_, lean_object* v_inst_6532_, lean_object* v_socket_6533_, lean_object* v_connectionContext_6534_, lean_object* v_extensions_6535_, lean_object* v___f_6536_, lean_object* v___f_6537_, lean_object* v___f_6538_, lean_object* v_x_6539_){
_start:
{
if (lean_obj_tag(v_x_6539_) == 0)
{
lean_object* v_a_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6549_; 
lean_dec_ref(v___f_6538_);
lean_dec_ref(v___f_6537_);
lean_dec_ref(v___f_6536_);
lean_dec(v_extensions_6535_);
lean_dec_ref(v_connectionContext_6534_);
lean_dec(v_socket_6533_);
lean_dec_ref(v_inst_6532_);
lean_dec_ref(v___f_6531_);
lean_dec(v_handler_6530_);
lean_dec_ref(v_responseBodyInstance_6529_);
lean_dec_ref(v_h_6528_);
lean_dec(v___x_6527_);
lean_dec_ref(v_a_6526_);
lean_dec_ref(v_machine_6525_);
lean_dec_ref(v_config_6524_);
v_a_6541_ = lean_ctor_get(v_x_6539_, 0);
v_isSharedCheck_6549_ = !lean_is_exclusive(v_x_6539_);
if (v_isSharedCheck_6549_ == 0)
{
v___x_6543_ = v_x_6539_;
v_isShared_6544_ = v_isSharedCheck_6549_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_a_6541_);
lean_dec(v_x_6539_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6549_;
goto v_resetjp_6542_;
}
v_resetjp_6542_:
{
lean_object* v___x_6546_; 
if (v_isShared_6544_ == 0)
{
v___x_6546_ = v___x_6543_;
goto v_reusejp_6545_;
}
else
{
lean_object* v_reuseFailAlloc_6548_; 
v_reuseFailAlloc_6548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6548_, 0, v_a_6541_);
v___x_6546_ = v_reuseFailAlloc_6548_;
goto v_reusejp_6545_;
}
v_reusejp_6545_:
{
lean_object* v___x_6547_; 
v___x_6547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6547_, 0, v___x_6546_);
return v___x_6547_;
}
}
}
else
{
lean_object* v_a_6550_; lean_object* v___x_6552_; uint8_t v_isShared_6553_; uint8_t v_isSharedCheck_6573_; 
v_a_6550_ = lean_ctor_get(v_x_6539_, 0);
v_isSharedCheck_6573_ = !lean_is_exclusive(v_x_6539_);
if (v_isSharedCheck_6573_ == 0)
{
v___x_6552_ = v_x_6539_;
v_isShared_6553_ = v_isSharedCheck_6573_;
goto v_resetjp_6551_;
}
else
{
lean_inc(v_a_6550_);
lean_dec(v_x_6539_);
v___x_6552_ = lean_box(0);
v_isShared_6553_ = v_isSharedCheck_6573_;
goto v_resetjp_6551_;
}
v_resetjp_6551_:
{
lean_object* v_lingeringTimeout_6554_; lean_object* v_keepAliveTimeout_6555_; lean_object* v_writeTimeout_6556_; lean_object* v_maximumRecvSize_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; uint8_t v___x_6560_; uint8_t v___x_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___f_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; lean_object* v___x_6567_; lean_object* v___x_6569_; 
v_lingeringTimeout_6554_ = lean_ctor_get(v_config_6524_, 4);
lean_inc(v_lingeringTimeout_6554_);
v_keepAliveTimeout_6555_ = lean_ctor_get(v_config_6524_, 5);
lean_inc_n(v_keepAliveTimeout_6555_, 3);
v_writeTimeout_6556_ = lean_ctor_get(v_config_6524_, 7);
lean_inc(v_writeTimeout_6556_);
v_maximumRecvSize_6557_ = lean_ctor_get(v_config_6524_, 8);
lean_inc(v_maximumRecvSize_6557_);
v___x_6558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6558_, 0, v_keepAliveTimeout_6555_);
v___x_6559_ = lean_box(0);
v___x_6560_ = 0;
v___x_6561_ = 1;
v___x_6562_ = lean_alloc_ctor(0, 11, 5);
lean_ctor_set(v___x_6562_, 0, v_machine_6525_);
lean_ctor_set(v___x_6562_, 1, v_a_6526_);
lean_ctor_set(v___x_6562_, 2, v___x_6558_);
lean_ctor_set(v___x_6562_, 3, v_keepAliveTimeout_6555_);
lean_ctor_set(v___x_6562_, 4, v___x_6559_);
lean_ctor_set(v___x_6562_, 5, v_a_6550_);
lean_ctor_set(v___x_6562_, 6, v___x_6559_);
lean_ctor_set(v___x_6562_, 7, v___x_6527_);
lean_ctor_set(v___x_6562_, 8, v___x_6559_);
lean_ctor_set(v___x_6562_, 9, v___x_6559_);
lean_ctor_set(v___x_6562_, 10, v___x_6559_);
lean_ctor_set_uint8(v___x_6562_, sizeof(void*)*11, v___x_6560_);
lean_ctor_set_uint8(v___x_6562_, sizeof(void*)*11 + 1, v___x_6560_);
lean_ctor_set_uint8(v___x_6562_, sizeof(void*)*11 + 2, v___x_6560_);
lean_ctor_set_uint8(v___x_6562_, sizeof(void*)*11 + 3, v___x_6560_);
lean_ctor_set_uint8(v___x_6562_, sizeof(void*)*11 + 4, v___x_6561_);
v___x_6563_ = lean_box(v___x_6560_);
lean_inc(v_socket_6533_);
v___f_6564_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__27___boxed), 19, 17);
lean_closure_set(v___f_6564_, 0, v___x_6563_);
lean_closure_set(v___f_6564_, 1, v_h_6528_);
lean_closure_set(v___f_6564_, 2, v_responseBodyInstance_6529_);
lean_closure_set(v___f_6564_, 3, v_handler_6530_);
lean_closure_set(v___f_6564_, 4, v_config_6524_);
lean_closure_set(v___f_6564_, 5, v___f_6531_);
lean_closure_set(v___f_6564_, 6, v_keepAliveTimeout_6555_);
lean_closure_set(v___f_6564_, 7, v_inst_6532_);
lean_closure_set(v___f_6564_, 8, v_socket_6533_);
lean_closure_set(v___f_6564_, 9, v_connectionContext_6534_);
lean_closure_set(v___f_6564_, 10, v_maximumRecvSize_6557_);
lean_closure_set(v___f_6564_, 11, v_extensions_6535_);
lean_closure_set(v___f_6564_, 12, v___f_6536_);
lean_closure_set(v___f_6564_, 13, v_lingeringTimeout_6554_);
lean_closure_set(v___f_6564_, 14, v___f_6537_);
lean_closure_set(v___f_6564_, 15, v___f_6538_);
lean_closure_set(v___f_6564_, 16, v___x_6562_);
v___x_6565_ = l_Int_toNat(v_writeTimeout_6556_);
lean_dec(v_writeTimeout_6556_);
v___x_6566_ = lean_unsigned_to_nat(0u);
v___x_6567_ = l_Std_Http_Internal_Outbox_new___redArg(v_socket_6533_, v___x_6565_);
if (v_isShared_6553_ == 0)
{
lean_ctor_set(v___x_6552_, 0, v___x_6567_);
v___x_6569_ = v___x_6552_;
goto v_reusejp_6568_;
}
else
{
lean_object* v_reuseFailAlloc_6572_; 
v_reuseFailAlloc_6572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6572_, 0, v___x_6567_);
v___x_6569_ = v_reuseFailAlloc_6572_;
goto v_reusejp_6568_;
}
v_reusejp_6568_:
{
lean_object* v___x_6570_; lean_object* v___x_6571_; 
v___x_6570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6570_, 0, v___x_6569_);
v___x_6571_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6566_, v___x_6560_, v___x_6570_, v___f_6564_);
return v___x_6571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__28___boxed(lean_object** _args){
lean_object* v_config_6574_ = _args[0];
lean_object* v_machine_6575_ = _args[1];
lean_object* v_a_6576_ = _args[2];
lean_object* v___x_6577_ = _args[3];
lean_object* v_h_6578_ = _args[4];
lean_object* v_responseBodyInstance_6579_ = _args[5];
lean_object* v_handler_6580_ = _args[6];
lean_object* v___f_6581_ = _args[7];
lean_object* v_inst_6582_ = _args[8];
lean_object* v_socket_6583_ = _args[9];
lean_object* v_connectionContext_6584_ = _args[10];
lean_object* v_extensions_6585_ = _args[11];
lean_object* v___f_6586_ = _args[12];
lean_object* v___f_6587_ = _args[13];
lean_object* v___f_6588_ = _args[14];
lean_object* v_x_6589_ = _args[15];
lean_object* v___y_6590_ = _args[16];
_start:
{
lean_object* v_res_6591_; 
v_res_6591_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__28(v_config_6574_, v_machine_6575_, v_a_6576_, v___x_6577_, v_h_6578_, v_responseBodyInstance_6579_, v_handler_6580_, v___f_6581_, v_inst_6582_, v_socket_6583_, v_connectionContext_6584_, v_extensions_6585_, v___f_6586_, v___f_6587_, v___f_6588_, v_x_6589_);
return v_res_6591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__29(lean_object* v_config_6592_, lean_object* v_machine_6593_, lean_object* v_h_6594_, lean_object* v_responseBodyInstance_6595_, lean_object* v_handler_6596_, lean_object* v___f_6597_, lean_object* v_inst_6598_, lean_object* v_socket_6599_, lean_object* v_connectionContext_6600_, lean_object* v_extensions_6601_, lean_object* v___f_6602_, lean_object* v___f_6603_, lean_object* v___f_6604_, lean_object* v_x_6605_){
_start:
{
if (lean_obj_tag(v_x_6605_) == 0)
{
lean_object* v_a_6607_; lean_object* v___x_6609_; uint8_t v_isShared_6610_; uint8_t v_isSharedCheck_6615_; 
lean_dec_ref(v___f_6604_);
lean_dec_ref(v___f_6603_);
lean_dec_ref(v___f_6602_);
lean_dec(v_extensions_6601_);
lean_dec_ref(v_connectionContext_6600_);
lean_dec(v_socket_6599_);
lean_dec_ref(v_inst_6598_);
lean_dec_ref(v___f_6597_);
lean_dec(v_handler_6596_);
lean_dec_ref(v_responseBodyInstance_6595_);
lean_dec_ref(v_h_6594_);
lean_dec_ref(v_machine_6593_);
lean_dec_ref(v_config_6592_);
v_a_6607_ = lean_ctor_get(v_x_6605_, 0);
v_isSharedCheck_6615_ = !lean_is_exclusive(v_x_6605_);
if (v_isSharedCheck_6615_ == 0)
{
v___x_6609_ = v_x_6605_;
v_isShared_6610_ = v_isSharedCheck_6615_;
goto v_resetjp_6608_;
}
else
{
lean_inc(v_a_6607_);
lean_dec(v_x_6605_);
v___x_6609_ = lean_box(0);
v_isShared_6610_ = v_isSharedCheck_6615_;
goto v_resetjp_6608_;
}
v_resetjp_6608_:
{
lean_object* v___x_6612_; 
if (v_isShared_6610_ == 0)
{
v___x_6612_ = v___x_6609_;
goto v_reusejp_6611_;
}
else
{
lean_object* v_reuseFailAlloc_6614_; 
v_reuseFailAlloc_6614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6614_, 0, v_a_6607_);
v___x_6612_ = v_reuseFailAlloc_6614_;
goto v_reusejp_6611_;
}
v_reusejp_6611_:
{
lean_object* v___x_6613_; 
v___x_6613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6613_, 0, v___x_6612_);
return v___x_6613_;
}
}
}
else
{
lean_object* v_a_6616_; lean_object* v___x_6618_; uint8_t v_isShared_6619_; uint8_t v_isSharedCheck_6630_; 
v_a_6616_ = lean_ctor_get(v_x_6605_, 0);
v_isSharedCheck_6630_ = !lean_is_exclusive(v_x_6605_);
if (v_isSharedCheck_6630_ == 0)
{
v___x_6618_ = v_x_6605_;
v_isShared_6619_ = v_isSharedCheck_6630_;
goto v_resetjp_6617_;
}
else
{
lean_inc(v_a_6616_);
lean_dec(v_x_6605_);
v___x_6618_ = lean_box(0);
v_isShared_6619_ = v_isSharedCheck_6630_;
goto v_resetjp_6617_;
}
v_resetjp_6617_:
{
lean_object* v___x_6620_; lean_object* v___f_6621_; lean_object* v___x_6622_; uint8_t v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6626_; 
v___x_6620_ = lean_box(0);
v___f_6621_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__28___boxed), 17, 15);
lean_closure_set(v___f_6621_, 0, v_config_6592_);
lean_closure_set(v___f_6621_, 1, v_machine_6593_);
lean_closure_set(v___f_6621_, 2, v_a_6616_);
lean_closure_set(v___f_6621_, 3, v___x_6620_);
lean_closure_set(v___f_6621_, 4, v_h_6594_);
lean_closure_set(v___f_6621_, 5, v_responseBodyInstance_6595_);
lean_closure_set(v___f_6621_, 6, v_handler_6596_);
lean_closure_set(v___f_6621_, 7, v___f_6597_);
lean_closure_set(v___f_6621_, 8, v_inst_6598_);
lean_closure_set(v___f_6621_, 9, v_socket_6599_);
lean_closure_set(v___f_6621_, 10, v_connectionContext_6600_);
lean_closure_set(v___f_6621_, 11, v_extensions_6601_);
lean_closure_set(v___f_6621_, 12, v___f_6602_);
lean_closure_set(v___f_6621_, 13, v___f_6603_);
lean_closure_set(v___f_6621_, 14, v___f_6604_);
v___x_6622_ = lean_unsigned_to_nat(0u);
v___x_6623_ = 0;
v___x_6624_ = l_Std_CloseableChannel_new___redArg(v___x_6620_);
if (v_isShared_6619_ == 0)
{
lean_ctor_set(v___x_6618_, 0, v___x_6624_);
v___x_6626_ = v___x_6618_;
goto v_reusejp_6625_;
}
else
{
lean_object* v_reuseFailAlloc_6629_; 
v_reuseFailAlloc_6629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6629_, 0, v___x_6624_);
v___x_6626_ = v_reuseFailAlloc_6629_;
goto v_reusejp_6625_;
}
v_reusejp_6625_:
{
lean_object* v___x_6627_; lean_object* v___x_6628_; 
v___x_6627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6627_, 0, v___x_6626_);
v___x_6628_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6622_, v___x_6623_, v___x_6627_, v___f_6621_);
return v___x_6628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__29___boxed(lean_object* v_config_6631_, lean_object* v_machine_6632_, lean_object* v_h_6633_, lean_object* v_responseBodyInstance_6634_, lean_object* v_handler_6635_, lean_object* v___f_6636_, lean_object* v_inst_6637_, lean_object* v_socket_6638_, lean_object* v_connectionContext_6639_, lean_object* v_extensions_6640_, lean_object* v___f_6641_, lean_object* v___f_6642_, lean_object* v___f_6643_, lean_object* v_x_6644_, lean_object* v___y_6645_){
_start:
{
lean_object* v_res_6646_; 
v_res_6646_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__29(v_config_6631_, v_machine_6632_, v_h_6633_, v_responseBodyInstance_6634_, v_handler_6635_, v___f_6636_, v_inst_6637_, v_socket_6638_, v_connectionContext_6639_, v_extensions_6640_, v___f_6641_, v___f_6642_, v___f_6643_, v_x_6644_);
return v_res_6646_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_6650_, lean_object* v_h_6651_, lean_object* v_connection_6652_, lean_object* v_config_6653_, lean_object* v_connectionContext_6654_, lean_object* v_handler_6655_){
_start:
{
lean_object* v_responseBodyInstance_6657_; lean_object* v_socket_6658_; lean_object* v_machine_6659_; lean_object* v_extensions_6660_; lean_object* v___f_6661_; lean_object* v___f_6662_; lean_object* v___f_6663_; lean_object* v___f_6664_; lean_object* v___f_6665_; lean_object* v___x_6666_; uint8_t v___x_6667_; lean_object* v___x_6668_; lean_object* v___x_6669_; 
v_responseBodyInstance_6657_ = lean_ctor_get(v_h_6651_, 0);
lean_inc_ref_n(v_responseBodyInstance_6657_, 2);
v_socket_6658_ = lean_ctor_get(v_connection_6652_, 0);
lean_inc(v_socket_6658_);
v_machine_6659_ = lean_ctor_get(v_connection_6652_, 1);
lean_inc_ref(v_machine_6659_);
v_extensions_6660_ = lean_ctor_get(v_connection_6652_, 2);
lean_inc(v_extensions_6660_);
lean_dec_ref(v_connection_6652_);
v___f_6661_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__0));
v___f_6662_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__1));
v___f_6663_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___closed__2));
v___f_6664_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_6664_, 0, v_responseBodyInstance_6657_);
v___f_6665_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__29___boxed), 15, 13);
lean_closure_set(v___f_6665_, 0, v_config_6653_);
lean_closure_set(v___f_6665_, 1, v_machine_6659_);
lean_closure_set(v___f_6665_, 2, v_h_6651_);
lean_closure_set(v___f_6665_, 3, v_responseBodyInstance_6657_);
lean_closure_set(v___f_6665_, 4, v_handler_6655_);
lean_closure_set(v___f_6665_, 5, v___f_6663_);
lean_closure_set(v___f_6665_, 6, v_inst_6650_);
lean_closure_set(v___f_6665_, 7, v_socket_6658_);
lean_closure_set(v___f_6665_, 8, v_connectionContext_6654_);
lean_closure_set(v___f_6665_, 9, v_extensions_6660_);
lean_closure_set(v___f_6665_, 10, v___f_6662_);
lean_closure_set(v___f_6665_, 11, v___f_6664_);
lean_closure_set(v___f_6665_, 12, v___f_6661_);
v___x_6666_ = lean_unsigned_to_nat(0u);
v___x_6667_ = 0;
v___x_6668_ = l_Std_Http_Body_mkStream();
v___x_6669_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6666_, v___x_6667_, v___x_6668_, v___f_6665_);
return v___x_6669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_6670_, lean_object* v_h_6671_, lean_object* v_connection_6672_, lean_object* v_config_6673_, lean_object* v_connectionContext_6674_, lean_object* v_handler_6675_, lean_object* v_a_6676_){
_start:
{
lean_object* v_res_6677_; 
v_res_6677_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_6670_, v_h_6671_, v_connection_6672_, v_config_6673_, v_connectionContext_6674_, v_handler_6675_);
return v_res_6677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_6678_, lean_object* v_00_u03c3_6679_, lean_object* v_inst_6680_, lean_object* v_h_6681_, lean_object* v_connection_6682_, lean_object* v_config_6683_, lean_object* v_connectionContext_6684_, lean_object* v_handler_6685_){
_start:
{
lean_object* v___x_6687_; 
v___x_6687_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_6680_, v_h_6681_, v_connection_6682_, v_config_6683_, v_connectionContext_6684_, v_handler_6685_);
return v___x_6687_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_6688_, lean_object* v_00_u03c3_6689_, lean_object* v_inst_6690_, lean_object* v_h_6691_, lean_object* v_connection_6692_, lean_object* v_config_6693_, lean_object* v_connectionContext_6694_, lean_object* v_handler_6695_, lean_object* v_a_6696_){
_start:
{
lean_object* v_res_6697_; 
v_res_6697_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_6688_, v_00_u03c3_6689_, v_inst_6690_, v_h_6691_, v_connection_6692_, v_config_6693_, v_connectionContext_6694_, v_handler_6695_);
return v_res_6697_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_6698_; lean_object* v___x_6699_; 
v___x_6698_ = 0;
v___x_6699_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_6698_);
return v___x_6699_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_6700_; lean_object* v___x_6701_; 
v___x_6700_ = lean_unsigned_to_nat(4096u);
v___x_6701_ = lean_mk_empty_byte_array(v___x_6700_);
return v___x_6701_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_6702_; lean_object* v___x_6703_; 
v___x_6702_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_6703_ = l_ByteArray_mkIterator(v___x_6702_);
return v___x_6703_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_6704_; lean_object* v___x_6705_; lean_object* v___x_6706_; lean_object* v___x_6707_; lean_object* v___x_6708_; lean_object* v___x_6709_; 
v___x_6704_ = 0;
v___x_6705_ = lean_unsigned_to_nat(0u);
v___x_6706_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_6707_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_6708_ = lean_box(0);
v___x_6709_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_6709_, 0, v___x_6708_);
lean_ctor_set(v___x_6709_, 1, v___x_6707_);
lean_ctor_set(v___x_6709_, 2, v___x_6706_);
lean_ctor_set(v___x_6709_, 3, v___x_6705_);
lean_ctor_set(v___x_6709_, 4, v___x_6705_);
lean_ctor_set(v___x_6709_, 5, v___x_6705_);
lean_ctor_set_uint8(v___x_6709_, sizeof(void*)*6, v___x_6704_);
return v___x_6709_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_6717_; lean_object* v___x_6718_; 
v___x_6717_ = 1;
v___x_6718_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_6717_);
return v___x_6718_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_6719_; uint8_t v___x_6720_; lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; lean_object* v___x_6724_; lean_object* v___x_6725_; lean_object* v___x_6726_; 
v___x_6719_ = lean_unsigned_to_nat(0u);
v___x_6720_ = 0;
v___x_6721_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_6722_ = lean_box(0);
v___x_6723_ = lean_box(0);
v___x_6724_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_6725_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_6726_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_6726_, 0, v___x_6725_);
lean_ctor_set(v___x_6726_, 1, v___x_6724_);
lean_ctor_set(v___x_6726_, 2, v___x_6723_);
lean_ctor_set(v___x_6726_, 3, v___x_6722_);
lean_ctor_set(v___x_6726_, 4, v___x_6721_);
lean_ctor_set(v___x_6726_, 5, v___x_6719_);
lean_ctor_set_uint8(v___x_6726_, sizeof(void*)*6, v___x_6720_);
lean_ctor_set_uint8(v___x_6726_, sizeof(void*)*6 + 1, v___x_6720_);
lean_ctor_set_uint8(v___x_6726_, sizeof(void*)*6 + 2, v___x_6720_);
return v___x_6726_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_6727_, lean_object* v_client_6728_, lean_object* v_extensions_6729_, lean_object* v_inst_6730_, lean_object* v_inst_6731_, lean_object* v_handler_6732_, lean_object* v_x_6733_){
_start:
{
if (lean_obj_tag(v_x_6733_) == 0)
{
lean_object* v_a_6735_; lean_object* v___x_6737_; uint8_t v_isShared_6738_; uint8_t v_isSharedCheck_6743_; 
lean_dec(v_handler_6732_);
lean_dec_ref(v_inst_6731_);
lean_dec_ref(v_inst_6730_);
lean_dec(v_extensions_6729_);
lean_dec(v_client_6728_);
lean_dec_ref(v_config_6727_);
v_a_6735_ = lean_ctor_get(v_x_6733_, 0);
v_isSharedCheck_6743_ = !lean_is_exclusive(v_x_6733_);
if (v_isSharedCheck_6743_ == 0)
{
v___x_6737_ = v_x_6733_;
v_isShared_6738_ = v_isSharedCheck_6743_;
goto v_resetjp_6736_;
}
else
{
lean_inc(v_a_6735_);
lean_dec(v_x_6733_);
v___x_6737_ = lean_box(0);
v_isShared_6738_ = v_isSharedCheck_6743_;
goto v_resetjp_6736_;
}
v_resetjp_6736_:
{
lean_object* v___x_6740_; 
if (v_isShared_6738_ == 0)
{
v___x_6740_ = v___x_6737_;
goto v_reusejp_6739_;
}
else
{
lean_object* v_reuseFailAlloc_6742_; 
v_reuseFailAlloc_6742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6742_, 0, v_a_6735_);
v___x_6740_ = v_reuseFailAlloc_6742_;
goto v_reusejp_6739_;
}
v_reusejp_6739_:
{
lean_object* v___x_6741_; 
v___x_6741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6741_, 0, v___x_6740_);
return v___x_6741_;
}
}
}
else
{
lean_object* v_a_6744_; uint8_t v___x_6745_; lean_object* v___x_6746_; lean_object* v___x_6747_; lean_object* v___x_6748_; lean_object* v___x_6749_; lean_object* v___x_6750_; uint8_t v_enableKeepAlive_6751_; lean_object* v___x_6752_; lean_object* v___x_6753_; lean_object* v___x_6754_; 
v_a_6744_ = lean_ctor_get(v_x_6733_, 0);
lean_inc(v_a_6744_);
lean_dec_ref_known(v_x_6733_, 1);
v___x_6745_ = 0;
v___x_6746_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_6747_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_6748_ = lean_box(0);
v___x_6749_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_6750_ = l_Std_Http_Config_toH1Config(v_config_6727_);
v_enableKeepAlive_6751_ = lean_ctor_get_uint8(v___x_6750_, sizeof(void*)*19);
v___x_6752_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_6752_, 0, v___x_6746_);
lean_ctor_set(v___x_6752_, 1, v___x_6749_);
lean_ctor_set(v___x_6752_, 2, v___x_6750_);
lean_ctor_set(v___x_6752_, 3, v___x_6747_);
lean_ctor_set(v___x_6752_, 4, v___x_6748_);
lean_ctor_set(v___x_6752_, 5, v___x_6748_);
lean_ctor_set_uint8(v___x_6752_, sizeof(void*)*6, v_enableKeepAlive_6751_);
lean_ctor_set_uint8(v___x_6752_, sizeof(void*)*6 + 1, v___x_6745_);
v___x_6753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6753_, 0, v_client_6728_);
lean_ctor_set(v___x_6753_, 1, v___x_6752_);
lean_ctor_set(v___x_6753_, 2, v_extensions_6729_);
v___x_6754_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_6730_, v_inst_6731_, v___x_6753_, v_config_6727_, v_a_6744_, v_handler_6732_);
return v___x_6754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_6755_, lean_object* v_client_6756_, lean_object* v_extensions_6757_, lean_object* v_inst_6758_, lean_object* v_inst_6759_, lean_object* v_handler_6760_, lean_object* v_x_6761_, lean_object* v___y_6762_){
_start:
{
lean_object* v_res_6763_; 
v_res_6763_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_6755_, v_client_6756_, v_extensions_6757_, v_inst_6758_, v_inst_6759_, v_handler_6760_, v_x_6761_);
return v_res_6763_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_6764_, lean_object* v_inst_6765_, lean_object* v_client_6766_, lean_object* v_handler_6767_, lean_object* v_config_6768_, lean_object* v_extensions_6769_, lean_object* v_a_6770_){
_start:
{
lean_object* v___f_6772_; lean_object* v___x_6773_; uint8_t v___x_6774_; lean_object* v___x_6775_; lean_object* v___x_6776_; lean_object* v___x_6777_; 
v___f_6772_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_6772_, 0, v_config_6768_);
lean_closure_set(v___f_6772_, 1, v_client_6766_);
lean_closure_set(v___f_6772_, 2, v_extensions_6769_);
lean_closure_set(v___f_6772_, 3, v_inst_6764_);
lean_closure_set(v___f_6772_, 4, v_inst_6765_);
lean_closure_set(v___f_6772_, 5, v_handler_6767_);
v___x_6773_ = lean_unsigned_to_nat(0u);
v___x_6774_ = 0;
lean_inc_ref(v_a_6770_);
v___x_6775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6775_, 0, v_a_6770_);
v___x_6776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6776_, 0, v___x_6775_);
v___x_6777_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6773_, v___x_6774_, v___x_6776_, v___f_6772_);
return v___x_6777_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_6778_, lean_object* v_inst_6779_, lean_object* v_client_6780_, lean_object* v_handler_6781_, lean_object* v_config_6782_, lean_object* v_extensions_6783_, lean_object* v_a_6784_, lean_object* v_a_6785_){
_start:
{
lean_object* v_res_6786_; 
v_res_6786_ = l_Std_Http_Server_serveConnection___redArg(v_inst_6778_, v_inst_6779_, v_client_6780_, v_handler_6781_, v_config_6782_, v_extensions_6783_, v_a_6784_);
lean_dec_ref(v_a_6784_);
return v_res_6786_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_6787_, lean_object* v_00_u03c3_6788_, lean_object* v_inst_6789_, lean_object* v_inst_6790_, lean_object* v_client_6791_, lean_object* v_handler_6792_, lean_object* v_config_6793_, lean_object* v_extensions_6794_, lean_object* v_a_6795_){
_start:
{
lean_object* v___x_6797_; 
v___x_6797_ = l_Std_Http_Server_serveConnection___redArg(v_inst_6789_, v_inst_6790_, v_client_6791_, v_handler_6792_, v_config_6793_, v_extensions_6794_, v_a_6795_);
return v___x_6797_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_6798_, lean_object* v_00_u03c3_6799_, lean_object* v_inst_6800_, lean_object* v_inst_6801_, lean_object* v_client_6802_, lean_object* v_handler_6803_, lean_object* v_config_6804_, lean_object* v_extensions_6805_, lean_object* v_a_6806_, lean_object* v_a_6807_){
_start:
{
lean_object* v_res_6808_; 
v_res_6808_ = l_Std_Http_Server_serveConnection(v_t_6798_, v_00_u03c3_6799_, v_inst_6800_, v_inst_6801_, v_client_6802_, v_handler_6803_, v_config_6804_, v_extensions_6805_, v_a_6806_);
lean_dec_ref(v_a_6806_);
return v_res_6808_;
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
