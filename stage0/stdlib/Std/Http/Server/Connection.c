// Lean compiler output
// Module: Std.Http.Server.Connection
// Imports: public import Std.Async.TCP public import Std.Async.ContextAsync public import Std.Http.Transport public import Std.Http.Transport.Outbox public import Std.Http.Protocol.H1 public import Std.Http.Server.Config public import Std.Http.Server.Handler import Std.Async.Watchdog
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
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Channel_recvSelector___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Http_Body_Stream_interestSelector(lean_object*);
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
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* l_Std_Http_Body_mkStream();
lean_object* l_Std_Http_Protocol_H1_Machine_canContinue(uint8_t, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Channel_send___redArg(lean_object*, lean_object*);
lean_object* l_Std_CancellationToken_selector(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Async_Selector_sleep(lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Async_BaseAsync_toRawBaseIO___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_Http_Internal_Outbox_failed___redArg(lean_object*);
lean_object* l_Std_Http_Protocol_H1_Machine_step(uint8_t, lean_object*);
lean_object* l_Std_Http_Internal_Outbox_takeError_x3f___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t l_ByteArray_isEmpty(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Http_Internal_appendFieldLine___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Headers_fold___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(uint8_t, lean_object*);
lean_object* l_Std_Http_Protocol_H1_Message_Head_setHeaders(uint8_t, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* l_Std_Http_Internal_appendNat(lean_object*, lean_object*);
lean_object* l_Std_Http_Status_reasonPhrase(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Http_Protocol_H1_Message_Head_headers(uint8_t, lean_object*);
uint8_t l_Std_Http_Protocol_H1_Writer_instBEqState_beq(lean_object*, lean_object*);
uint8_t l_Std_Http_Protocol_H1_Message_Head_version(uint8_t, lean_object*);
uint8_t l_Std_Http_instBEqVersion_beq(uint8_t, uint8_t);
lean_object* lean_get_current_time();
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_DateTime_toHTTPDateString(lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg(lean_object*);
uint8_t l_Std_Async_Watchdog_hasFired(lean_object*);
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
uint8_t l_Std_Async_Watchdog_disarm(lean_object*);
extern lean_object* l_instInhabitedError;
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Std_Http_Internal_Outbox_idle_x3f___redArg(lean_object*);
lean_object* l_Std_Async_Watchdog_armAfter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Http_Internal_Outbox_writeDeadline_x3f___redArg(lean_object*);
lean_object* l_Std_Async_Watchdog_arm(lean_object*, lean_object*);
lean_object* l_Std_Async_Watchdog_armUntil(lean_object*, lean_object*);
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
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_Std_Async_Async_ofTask___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t l_Std_Http_Method_isSafe(uint8_t);
lean_object* l_Std_Http_Internal_Outbox_new___redArg(lean_object*, lean_object*);
lean_object* l_Std_CancellationContext_cancel(lean_object*, lean_object*);
lean_object* l_Std_Async_Watchdog_new(lean_object*);
lean_object* l_Std_Http_Protocol_H1_instEmptyCollectionHead(uint8_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Http_Config_toH1Config(lean_object*);
lean_object* l_Std_CancellationContext_fork(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_writeDue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_writeDue_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__0_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_appendFieldLine___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__3_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__4_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "200 OK"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__8 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__8_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__16 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__16_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__17 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__17_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__11_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__12_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__18 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__18_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__18_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__13_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__14_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__15_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__16_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__19 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__19_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__19_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__17_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__20 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__20_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__21;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__22;
static const lean_array_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__23 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__23_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__24;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__25;
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
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___closed__0;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "the request body is incomplete: "};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Invalid status line"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Invalid header"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__2_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Timeout"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__3_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Entity too large"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__4_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "URI too long"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__5 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__5_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Unsupported version"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__6 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__6_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Unsupported transfer coding"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__7 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__7_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unsupported method"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__8 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__8_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Invalid chunk"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__9 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__9_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Connection closed"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__10 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__10_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Bad message"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__11 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__11_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Too many headers"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__12 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__12_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Headers too large"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__13 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__13_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Other error: "};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__14 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__14_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__0;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__1;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_BaseAsync_lift___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__2_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__3 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__3_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__2_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__4_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__5;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_EAsync_instMonadFinally___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__6 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__6_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "the request body was discarded after the response was written"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__7 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__7_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "the handler returned the interim status "};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___closed__0_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " as its final response"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint16_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__22(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__22___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__22___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1_value;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "request header timeout"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__3;
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "request timeout"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__4 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__4_value;
static lean_once_cell_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__0_value)}};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__3_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__0_value)} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__1_value),((lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__2_value)} };
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_armTimer___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_armTimer___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_armTimer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_armTimer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__17(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__18___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__20(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__21(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__22(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__23(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__24(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__26(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__25(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__28___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "the connection closed before the request body was complete"};
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__28___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__28___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__29(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__30(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__31___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__32___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__33___boxed(lean_object**);
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__0_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__1_value;
static const lean_closure_object l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__2 = (const lean_object*)&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_writeDue_elim___redArg(lean_object* v_t_111_, lean_object* v_writeDue_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_111_, v_writeDue_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_writeDue_elim(lean_object* v_00_u03b2_114_, lean_object* v_motive_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_writeDue_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_116_, v_writeDue_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim___redArg(lean_object* v_t_120_, lean_object* v_timeout_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_120_, v_timeout_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_timeout_elim(lean_object* v_00_u03b2_123_, lean_object* v_motive_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_timeout_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Recv_ctorElim___redArg(v_t_125_, v_timeout_127_);
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
lean_dec(v_x_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(lean_object* v_t_151_, lean_object* v_k_152_){
_start:
{
if (lean_obj_tag(v_t_151_) == 0)
{
return v_k_152_;
}
else
{
lean_object* v_deadline_153_; lean_object* v___x_154_; 
v_deadline_153_ = lean_ctor_get(v_t_151_, 0);
lean_inc(v_deadline_153_);
lean_dec(v_t_151_);
v___x_154_ = lean_apply_1(v_k_152_, v_deadline_153_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim(lean_object* v_motive_155_, lean_object* v_ctorIdx_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_k_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_157_, v_k_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___boxed(lean_object* v_motive_161_, lean_object* v_ctorIdx_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_k_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim(v_motive_161_, v_ctorIdx_162_, v_t_163_, v_h_164_, v_k_165_);
lean_dec(v_ctorIdx_162_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_keepAlive_elim___redArg(lean_object* v_t_167_, lean_object* v_keepAlive_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_167_, v_keepAlive_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_keepAlive_elim(lean_object* v_motive_170_, lean_object* v_t_171_, lean_object* v_h_172_, lean_object* v_keepAlive_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_171_, v_keepAlive_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_header_elim___redArg(lean_object* v_t_175_, lean_object* v_header_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_175_, v_header_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_header_elim(lean_object* v_motive_178_, lean_object* v_t_179_, lean_object* v_h_180_, lean_object* v_header_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_179_, v_header_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_request_elim___redArg(lean_object* v_t_183_, lean_object* v_request_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_183_, v_request_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_request_elim(lean_object* v_motive_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_request_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_Timer_ctorElim___redArg(v_t_187_, v_request_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent___redArg(lean_object* v_wd_191_, lean_object* v_ctx_192_, uint8_t v_idle_193_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = l_Std_Async_Watchdog_hasFired(v_wd_191_);
if (v___x_197_ == 0)
{
lean_object* v_token_198_; lean_object* v___x_199_; 
v_token_198_ = lean_ctor_get(v_ctx_192_, 1);
lean_inc_ref(v_token_198_);
lean_dec_ref(v_ctx_192_);
v___x_199_ = l_Std_CancellationToken_getCancellationReason(v_token_198_);
if (lean_obj_tag(v___x_199_) == 1)
{
lean_object* v_val_200_; 
v_val_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_200_);
lean_dec_ref_known(v___x_199_, 1);
if (lean_obj_tag(v_val_200_) == 0)
{
lean_object* v___x_201_; 
v___x_201_ = lean_box(5);
return v___x_201_;
}
else
{
lean_dec(v_val_200_);
goto v___jp_195_;
}
}
else
{
lean_dec(v___x_199_);
goto v___jp_195_;
}
}
else
{
lean_dec_ref(v_ctx_192_);
if (v_idle_193_ == 0)
{
lean_object* v___x_202_; 
v___x_202_ = lean_box(5);
return v___x_202_;
}
else
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(7);
return v___x_203_;
}
}
v___jp_195_:
{
lean_object* v___x_196_; 
v___x_196_ = lean_box(6);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent___redArg___boxed(lean_object* v_wd_204_, lean_object* v_ctx_205_, lean_object* v_idle_206_, lean_object* v_a_207_){
_start:
{
uint8_t v_idle_boxed_208_; lean_object* v_res_209_; 
v_idle_boxed_208_ = lean_unbox(v_idle_206_);
v_res_209_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent___redArg(v_wd_204_, v_ctx_205_, v_idle_boxed_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent(lean_object* v_00_u03b2_210_, lean_object* v_wd_211_, lean_object* v_ctx_212_, uint8_t v_idle_213_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent___redArg(v_wd_211_, v_ctx_212_, v_idle_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent___boxed(lean_object* v_00_u03b2_216_, lean_object* v_wd_217_, lean_object* v_ctx_218_, lean_object* v_idle_219_, lean_object* v_a_220_){
_start:
{
uint8_t v_idle_boxed_221_; lean_object* v_res_222_; 
v_idle_boxed_221_ = lean_unbox(v_idle_219_);
v_res_222_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent(v_00_u03b2_216_, v_wd_217_, v_ctx_218_, v_idle_boxed_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0(lean_object* v_x_227_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_object* v___x_229_; 
lean_dec_ref_known(v_x_227_, 1);
v___x_229_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_229_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v_x_227_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___boxed(lean_object* v_x_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0(v_x_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(lean_object* v_inst_235_, lean_object* v_handler_236_, lean_object* v_error_237_){
_start:
{
lean_object* v_onFailure_239_; lean_object* v___f_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_onFailure_239_ = lean_ctor_get(v_inst_235_, 2);
lean_inc_ref(v_onFailure_239_);
lean_dec_ref(v_inst_235_);
v___f_240_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___closed__0));
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = 0;
v___x_243_ = lean_apply_3(v_onFailure_239_, v_handler_236_, v_error_237_, lean_box(0));
v___x_244_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_241_, v___x_242_, v___x_243_, v___f_240_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___boxed(lean_object* v_inst_245_, lean_object* v_handler_246_, lean_object* v_error_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_245_, v_handler_246_, v_error_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure(lean_object* v_00_u03c3_250_, lean_object* v_inst_251_, lean_object* v_handler_252_, lean_object* v_error_253_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_251_, v_handler_252_, v_error_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___boxed(lean_object* v_00_u03c3_256_, lean_object* v_inst_257_, lean_object* v_handler_258_, lean_object* v_error_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure(v_00_u03c3_256_, v_inst_257_, v_handler_258_, v_error_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(lean_object* v_x_262_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v_x_262_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0___boxed(lean_object* v_x_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__0(v_x_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(lean_object* v_x_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___closed__1));
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1___boxed(lean_object* v_x_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__1(v_x_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(lean_object* v_x_280_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v_x_280_);
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2___boxed(lean_object* v_x_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__2(v_x_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(uint8_t v_x_288_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_290_, 0, v_x_288_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3___boxed(lean_object* v_x_293_, lean_object* v___y_294_){
_start:
{
uint8_t v_x_1902__boxed_295_; lean_object* v_res_296_; 
v_x_1902__boxed_295_ = lean_unbox(v_x_293_);
v_res_296_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__3(v_x_1902__boxed_295_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(lean_object* v_x_297_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_299_, 0, v_x_297_);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4___boxed(lean_object* v_x_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__4(v_x_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_319_; 
v_a_311_ = lean_ctor_get(v_x_309_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v_x_309_);
if (v_isSharedCheck_319_ == 0)
{
v___x_313_ = v_x_309_;
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v_x_309_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_318_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
}
else
{
lean_object* v___x_320_; 
lean_dec_ref_known(v_x_309_, 1);
v___x_320_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___closed__1));
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5___boxed(lean_object* v_x_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__5(v_x_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(lean_object* v_inst_324_, lean_object* v_handler_325_, lean_object* v___f_326_, lean_object* v_x_327_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_330_; uint8_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_a_329_ = lean_ctor_get(v_x_327_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v_x_327_, 1);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = 0;
v___x_332_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_324_, v_handler_325_, v_a_329_);
v___x_333_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_330_, v___x_331_, v___x_332_, v___f_326_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; 
lean_dec_ref(v___f_326_);
lean_dec(v_handler_325_);
lean_dec_ref(v_inst_324_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v_x_327_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed(lean_object* v_inst_335_, lean_object* v_handler_336_, lean_object* v___f_337_, lean_object* v_x_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6(v_inst_335_, v_handler_336_, v___f_337_, v_x_338_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(lean_object* v___f_341_, lean_object* v_response_342_, lean_object* v___x_343_, lean_object* v___f_344_, lean_object* v_requestBody_345_, lean_object* v___f_346_, lean_object* v_responseBody_347_, lean_object* v_inst_348_, lean_object* v___f_349_, lean_object* v_____r_350_, lean_object* v_selectables_351_){
_start:
{
lean_object* v_selectables_354_; lean_object* v_selectables_360_; lean_object* v_selectables_366_; 
if (lean_obj_tag(v_responseBody_347_) == 1)
{
lean_object* v_val_371_; lean_object* v_recvSelector_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v_selectables_375_; 
v_val_371_ = lean_ctor_get(v_responseBody_347_, 0);
lean_inc(v_val_371_);
lean_dec_ref_known(v_responseBody_347_, 1);
v_recvSelector_372_ = lean_ctor_get(v_inst_348_, 3);
lean_inc_ref(v_recvSelector_372_);
lean_dec_ref(v_inst_348_);
v___x_373_ = lean_apply_1(v_recvSelector_372_, v_val_371_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v___f_349_);
v_selectables_375_ = lean_array_push(v_selectables_351_, v___x_374_);
v_selectables_366_ = v_selectables_375_;
goto v___jp_365_;
}
else
{
lean_dec_ref(v___f_349_);
lean_dec_ref(v_inst_348_);
lean_dec(v_responseBody_347_);
v_selectables_366_ = v_selectables_351_;
goto v___jp_365_;
}
v___jp_353_:
{
lean_object* v___x_355_; uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = 0;
v___x_357_ = l_Std_Async_Selectable_one___redArg(v_selectables_354_);
v___x_358_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_355_, v___x_356_, v___x_357_, v___f_341_);
return v___x_358_;
}
v___jp_359_:
{
if (lean_obj_tag(v_response_342_) == 1)
{
lean_object* v_val_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_selectables_364_; 
v_val_361_ = lean_ctor_get(v_response_342_, 0);
lean_inc(v_val_361_);
lean_dec_ref_known(v_response_342_, 1);
v___x_362_ = l_Std_Channel_recvSelector___redArg(v___x_343_, v_val_361_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v___f_344_);
v_selectables_364_ = lean_array_push(v_selectables_360_, v___x_363_);
v_selectables_354_ = v_selectables_364_;
goto v___jp_353_;
}
else
{
lean_dec_ref(v___f_344_);
lean_dec_ref(v___x_343_);
lean_dec(v_response_342_);
v_selectables_354_ = v_selectables_360_;
goto v___jp_353_;
}
}
v___jp_365_:
{
if (lean_obj_tag(v_requestBody_345_) == 1)
{
lean_object* v_val_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_selectables_370_; 
v_val_367_ = lean_ctor_get(v_requestBody_345_, 0);
lean_inc(v_val_367_);
lean_dec_ref_known(v_requestBody_345_, 1);
v___x_368_ = l_Std_Http_Body_Stream_interestSelector(v_val_367_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___f_346_);
v_selectables_370_ = lean_array_push(v_selectables_366_, v___x_369_);
v_selectables_360_ = v_selectables_370_;
goto v___jp_359_;
}
else
{
lean_dec_ref(v___f_346_);
lean_dec(v_requestBody_345_);
v_selectables_360_ = v_selectables_366_;
goto v___jp_359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed(lean_object* v___f_376_, lean_object* v_response_377_, lean_object* v___x_378_, lean_object* v___f_379_, lean_object* v_requestBody_380_, lean_object* v___f_381_, lean_object* v_responseBody_382_, lean_object* v_inst_383_, lean_object* v___f_384_, lean_object* v_____r_385_, lean_object* v_selectables_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(v___f_376_, v_response_377_, v___x_378_, v___f_379_, v_requestBody_380_, v___f_381_, v_responseBody_382_, v_inst_383_, v___f_384_, v_____r_385_, v_selectables_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(lean_object* v___f_389_, lean_object* v_selectables_390_, lean_object* v___f_391_, lean_object* v_x_392_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v___f_391_);
lean_dec_ref(v_selectables_390_);
lean_dec_ref(v___f_389_);
v_a_394_ = lean_ctor_get(v_x_392_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v_x_392_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v_x_392_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v_x_392_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_401_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; 
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_a_403_ = lean_ctor_get(v_x_392_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v_x_392_, 1);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v_a_403_);
lean_ctor_set(v___x_404_, 1, v___f_389_);
v___x_405_ = lean_array_push(v_selectables_390_, v___x_404_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_apply_3(v___f_391_, v___x_406_, v___x_405_, lean_box(0));
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed(lean_object* v___f_408_, lean_object* v_selectables_409_, lean_object* v___f_410_, lean_object* v_x_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8(v___f_408_, v_selectables_409_, v___f_410_, v_x_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(lean_object* v_val_414_, lean_object* v___f_415_, lean_object* v_x_416_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v___f_415_);
v_a_418_ = lean_ctor_get(v_x_416_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_x_416_);
if (v_isSharedCheck_426_ == 0)
{
v___x_420_ = v_x_416_;
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v_x_416_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_426_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_425_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; 
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_a_427_ = lean_ctor_get(v_x_416_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v_x_416_, 1);
v___x_428_ = lean_nat_sub(v_val_414_, v_a_427_);
lean_dec(v_a_427_);
v___x_429_ = lean_nat_to_int(v___x_428_);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = 0;
v___x_432_ = l_Std_Async_Selector_sleep(v___x_429_);
lean_dec(v___x_429_);
v___x_433_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_430_, v___x_431_, v___x_432_, v___f_415_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed(lean_object* v_val_434_, lean_object* v___f_435_, lean_object* v_x_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9(v_val_434_, v___f_435_, v_x_436_);
lean_dec(v_val_434_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(lean_object* v_wd_439_, lean_object* v_connectionContext_440_, uint8_t v_idle_441_, lean_object* v_x_442_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent___redArg(v_wd_439_, v_connectionContext_440_, v_idle_441_);
v___x_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed(lean_object* v_wd_447_, lean_object* v_connectionContext_448_, lean_object* v_idle_449_, lean_object* v_x_450_, lean_object* v___y_451_){
_start:
{
uint8_t v_idle_boxed_452_; lean_object* v_res_453_; 
v_idle_boxed_452_ = lean_unbox(v_idle_449_);
v_res_453_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10(v_wd_447_, v_connectionContext_448_, v_idle_boxed_452_, v_x_450_);
return v_res_453_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = l_instInhabitedError;
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_config_465_, lean_object* v_handler_466_, lean_object* v_wd_467_, lean_object* v_sources_468_){
_start:
{
lean_object* v_socket_470_; lean_object* v_writeDue_471_; lean_object* v_expect_472_; lean_object* v_response_473_; lean_object* v_responseBody_474_; lean_object* v_requestBody_475_; lean_object* v_connectionContext_476_; uint8_t v_idle_477_; lean_object* v___f_478_; lean_object* v___f_479_; lean_object* v___f_480_; lean_object* v___f_481_; lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___f_486_; lean_object* v_selectables_488_; lean_object* v___y_507_; lean_object* v___y_524_; 
v_socket_470_ = lean_ctor_get(v_sources_468_, 0);
lean_inc(v_socket_470_);
v_writeDue_471_ = lean_ctor_get(v_sources_468_, 2);
lean_inc(v_writeDue_471_);
v_expect_472_ = lean_ctor_get(v_sources_468_, 3);
lean_inc(v_expect_472_);
v_response_473_ = lean_ctor_get(v_sources_468_, 4);
lean_inc_n(v_response_473_, 2);
v_responseBody_474_ = lean_ctor_get(v_sources_468_, 5);
lean_inc_n(v_responseBody_474_, 2);
v_requestBody_475_ = lean_ctor_get(v_sources_468_, 6);
lean_inc_n(v_requestBody_475_, 2);
v_connectionContext_476_ = lean_ctor_get(v_sources_468_, 7);
lean_inc_ref(v_connectionContext_476_);
v_idle_477_ = lean_ctor_get_uint8(v_sources_468_, sizeof(void*)*8);
lean_dec_ref(v_sources_468_);
v___f_478_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__0));
v___f_479_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__1));
v___f_480_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__2));
v___f_481_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__3));
v___f_482_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__4));
v___f_483_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__5));
v___f_484_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__6___boxed), 5, 3);
lean_closure_set(v___f_484_, 0, v_inst_463_);
lean_closure_set(v___f_484_, 1, v_handler_466_);
lean_closure_set(v___f_484_, 2, v___f_483_);
v___x_485_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___closed__6);
lean_inc_ref(v_inst_464_);
lean_inc_ref(v___f_484_);
v___f_486_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7___boxed), 12, 9);
lean_closure_set(v___f_486_, 0, v___f_484_);
lean_closure_set(v___f_486_, 1, v_response_473_);
lean_closure_set(v___f_486_, 2, v___x_485_);
lean_closure_set(v___f_486_, 3, v___f_482_);
lean_closure_set(v___f_486_, 4, v_requestBody_475_);
lean_closure_set(v___f_486_, 5, v___f_481_);
lean_closure_set(v___f_486_, 6, v_responseBody_474_);
lean_closure_set(v___f_486_, 7, v_inst_464_);
lean_closure_set(v___f_486_, 8, v___f_480_);
if (lean_obj_tag(v_expect_472_) == 0)
{
lean_object* v_defaultPayloadBytes_527_; 
v_defaultPayloadBytes_527_ = lean_ctor_get(v_config_465_, 9);
lean_inc(v_defaultPayloadBytes_527_);
v___y_524_ = v_defaultPayloadBytes_527_;
goto v___jp_523_;
}
else
{
lean_object* v_val_528_; 
v_val_528_ = lean_ctor_get(v_expect_472_, 0);
lean_inc(v_val_528_);
lean_dec_ref_known(v_expect_472_, 1);
v___y_524_ = v_val_528_;
goto v___jp_523_;
}
v___jp_487_:
{
if (lean_obj_tag(v_writeDue_471_) == 1)
{
lean_object* v_val_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v___f_484_);
lean_dec(v_requestBody_475_);
lean_dec(v_responseBody_474_);
lean_dec(v_response_473_);
lean_dec_ref(v_inst_464_);
v_val_489_ = lean_ctor_get(v_writeDue_471_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v_writeDue_471_);
if (v_isSharedCheck_503_ == 0)
{
v___x_491_ = v_writeDue_471_;
v_isShared_492_ = v_isSharedCheck_503_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_val_489_);
lean_dec(v_writeDue_471_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_503_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___f_493_; lean_object* v___f_494_; lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___f_493_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_493_, 0, v___f_479_);
lean_closure_set(v___f_493_, 1, v_selectables_488_);
lean_closure_set(v___f_493_, 2, v___f_486_);
v___f_494_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_494_, 0, v_val_489_);
lean_closure_set(v___f_494_, 1, v___f_493_);
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = 0;
v___x_497_ = lean_io_mono_ms_now();
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_497_);
v___x_499_ = v___x_491_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_502_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
v___x_501_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_495_, v___x_496_, v___x_500_, v___f_494_);
return v___x_501_;
}
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec_ref(v___f_486_);
lean_dec(v_writeDue_471_);
v___x_504_ = lean_box(0);
v___x_505_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__7(v___f_484_, v_response_473_, v___x_485_, v___f_482_, v_requestBody_475_, v___f_481_, v_responseBody_474_, v_inst_464_, v___f_480_, v___x_504_, v_selectables_488_);
return v___x_505_;
}
}
v___jp_506_:
{
lean_object* v_token_508_; lean_object* v___x_509_; lean_object* v___f_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_selectables_515_; 
v_token_508_ = lean_ctor_get(v_connectionContext_476_, 1);
lean_inc_ref(v_token_508_);
v___x_509_ = lean_box(v_idle_477_);
v___f_510_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___lam__10___boxed), 5, 3);
lean_closure_set(v___f_510_, 0, v_wd_467_);
lean_closure_set(v___f_510_, 1, v_connectionContext_476_);
lean_closure_set(v___f_510_, 2, v___x_509_);
v___x_511_ = l_Std_CancellationToken_selector(v_token_508_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v___f_510_);
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_mk_empty_array_with_capacity(v___x_513_);
v_selectables_515_ = lean_array_push(v___x_514_, v___x_512_);
if (lean_obj_tag(v_socket_470_) == 1)
{
lean_object* v_val_516_; lean_object* v_recvSelector_517_; uint64_t v_expectedBytes_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_selectables_522_; 
v_val_516_ = lean_ctor_get(v_socket_470_, 0);
lean_inc(v_val_516_);
lean_dec_ref_known(v_socket_470_, 1);
v_recvSelector_517_ = lean_ctor_get(v_inst_462_, 2);
lean_inc_ref(v_recvSelector_517_);
lean_dec_ref(v_inst_462_);
v_expectedBytes_518_ = lean_uint64_of_nat(v___y_507_);
lean_dec(v___y_507_);
v___x_519_ = lean_box_uint64(v_expectedBytes_518_);
v___x_520_ = lean_apply_2(v_recvSelector_517_, v_val_516_, v___x_519_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___f_478_);
v_selectables_522_ = lean_array_push(v_selectables_515_, v___x_521_);
v_selectables_488_ = v_selectables_522_;
goto v___jp_487_;
}
else
{
lean_dec(v___y_507_);
lean_dec(v_socket_470_);
lean_dec_ref(v_inst_462_);
v_selectables_488_ = v_selectables_515_;
goto v___jp_487_;
}
}
v___jp_523_:
{
lean_object* v_maximumRecvSize_525_; uint8_t v___x_526_; 
v_maximumRecvSize_525_ = lean_ctor_get(v_config_465_, 8);
lean_inc(v_maximumRecvSize_525_);
lean_dec_ref(v_config_465_);
v___x_526_ = lean_nat_dec_le(v___y_524_, v_maximumRecvSize_525_);
if (v___x_526_ == 0)
{
lean_dec(v___y_524_);
v___y_507_ = v_maximumRecvSize_525_;
goto v___jp_506_;
}
else
{
lean_dec(v_maximumRecvSize_525_);
v___y_507_ = v___y_524_;
goto v___jp_506_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg___boxed(lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_config_532_, lean_object* v_handler_533_, lean_object* v_wd_534_, lean_object* v_sources_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_529_, v_inst_530_, v_inst_531_, v_config_532_, v_handler_533_, v_wd_534_, v_sources_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(lean_object* v_00_u03b1_538_, lean_object* v_00_u03c3_539_, lean_object* v_00_u03b2_540_, lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_config_544_, lean_object* v_handler_545_, lean_object* v_wd_546_, lean_object* v_sources_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_541_, v_inst_542_, v_inst_543_, v_config_544_, v_handler_545_, v_wd_546_, v_sources_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___boxed(lean_object* v_00_u03b1_550_, lean_object* v_00_u03c3_551_, lean_object* v_00_u03b2_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_config_556_, lean_object* v_handler_557_, lean_object* v_wd_558_, lean_object* v_sources_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent(v_00_u03b1_550_, v_00_u03c3_551_, v_00_u03b2_552_, v_inst_553_, v_inst_554_, v_inst_555_, v_config_556_, v_handler_557_, v_wd_558_, v_sources_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(lean_object* v_machine_562_, lean_object* v_x_563_){
_start:
{
lean_object* v___y_566_; uint8_t v___y_567_; 
if (lean_obj_tag(v_x_563_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref(v_machine_562_);
v_a_572_ = lean_ctor_get(v_x_563_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v_x_563_);
if (v_isSharedCheck_580_ == 0)
{
v___x_574_ = v_x_563_;
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v_x_563_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_579_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; 
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___y_583_; uint8_t v___x_589_; 
v_a_581_ = lean_ctor_get(v_x_563_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v_x_563_, 1);
v___x_589_ = lean_unbox(v_a_581_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_box(40);
v___y_583_ = v___x_590_;
goto v___jp_582_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = lean_box(0);
v___y_583_ = v___x_591_;
goto v___jp_582_;
}
v___jp_582_:
{
uint8_t v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_584_ = 0;
lean_inc(v___y_583_);
v___x_585_ = l_Std_Http_Protocol_H1_Machine_canContinue(v___x_584_, v_machine_562_, v___y_583_);
v___x_586_ = lean_unbox(v_a_581_);
lean_dec(v_a_581_);
if (v___x_586_ == 0)
{
uint8_t v___x_587_; 
v___x_587_ = 1;
v___y_566_ = v___x_585_;
v___y_567_ = v___x_587_;
goto v___jp_565_;
}
else
{
uint8_t v___x_588_; 
v___x_588_ = 0;
v___y_566_ = v___x_585_;
v___y_567_ = v___x_588_;
goto v___jp_565_;
}
}
}
v___jp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_568_ = lean_box(v___y_567_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v___y_566_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed(lean_object* v_machine_592_, lean_object* v_x_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0(v_machine_592_, v_x_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(uint8_t v___y_596_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_box(v___y_596_);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1___boxed(lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
uint8_t v___y_1377__boxed_603_; lean_object* v_res_604_; 
v___y_1377__boxed_603_ = lean_unbox(v___y_601_);
v_res_604_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__1(v___y_1377__boxed_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__2(lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_607_; 
v_a_606_ = lean_ctor_get(v_x_605_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v_x_605_, 1);
v___x_607_ = lean_task_pure(v_a_606_);
return v___x_607_;
}
else
{
lean_object* v_a_608_; 
v_a_608_ = lean_ctor_get(v_x_605_, 0);
lean_inc_ref(v_a_608_);
lean_dec_ref_known(v_x_605_, 1);
return v_a_608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(lean_object* v_a_609_, lean_object* v_x_610_){
_start:
{
if (lean_obj_tag(v_x_610_) == 0)
{
uint8_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec_ref_known(v_x_610_, 1);
v___x_612_ = 0;
v___x_613_ = lean_box(0);
v___x_614_ = lean_box(v___x_612_);
v___x_615_ = l_Std_Channel_send___redArg(v_a_609_, v___x_614_);
lean_dec_ref(v___x_615_);
return v___x_613_;
}
else
{
lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_a_616_ = lean_ctor_get(v_x_610_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v_x_610_, 1);
v___x_617_ = lean_box(0);
v___x_618_ = l_Std_Channel_send___redArg(v_a_609_, v_a_616_);
lean_dec_ref(v___x_618_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed(lean_object* v_a_619_, lean_object* v_x_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3(v_a_619_, v_x_620_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(uint8_t v___x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_box(v___x_623_);
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed(lean_object* v___x_629_, lean_object* v_x_630_, lean_object* v___y_631_){
_start:
{
uint8_t v___x_1421__boxed_632_; lean_object* v_res_633_; 
v___x_1421__boxed_632_ = lean_unbox(v___x_629_);
v_res_633_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4(v___x_1421__boxed_632_, v_x_630_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(lean_object* v_connectionContext_634_, uint8_t v___x_635_, lean_object* v_a_636_, lean_object* v___f_637_, lean_object* v___f_638_, lean_object* v___x_639_, uint8_t v___x_640_, lean_object* v___f_641_, lean_object* v_x_642_){
_start:
{
if (lean_obj_tag(v_x_642_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref(v___f_641_);
lean_dec(v___x_639_);
lean_dec_ref(v___f_638_);
lean_dec_ref(v___f_637_);
lean_dec_ref(v_a_636_);
lean_dec_ref(v_connectionContext_634_);
v_a_644_ = lean_ctor_get(v_x_642_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v_x_642_);
if (v_isSharedCheck_652_ == 0)
{
v___x_646_ = v_x_642_;
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v_x_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_651_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; 
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
}
else
{
lean_object* v_a_653_; lean_object* v_token_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_a_653_ = lean_ctor_get(v_x_642_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v_x_642_, 1);
v_token_654_ = lean_ctor_get(v_connectionContext_634_, 1);
lean_inc_ref(v_token_654_);
lean_dec_ref(v_connectionContext_634_);
v___x_655_ = lean_box(v___x_635_);
v___x_656_ = l_Std_Channel_recvSelector___redArg(v___x_655_, v_a_636_);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___f_637_);
v___x_658_ = l_Std_CancellationToken_selector(v_token_654_);
lean_inc_ref(v___f_638_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___f_638_);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v_a_653_);
lean_ctor_set(v___x_660_, 1, v___f_638_);
v___x_661_ = lean_unsigned_to_nat(3u);
v___x_662_ = lean_mk_empty_array_with_capacity(v___x_661_);
v___x_663_ = lean_array_push(v___x_662_, v___x_657_);
v___x_664_ = lean_array_push(v___x_663_, v___x_659_);
v___x_665_ = lean_array_push(v___x_664_, v___x_660_);
v___x_666_ = l_Std_Async_Selectable_one___redArg(v___x_665_);
v___x_667_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_639_, v___x_640_, v___x_666_, v___f_641_);
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed(lean_object* v_connectionContext_668_, lean_object* v___x_669_, lean_object* v_a_670_, lean_object* v___f_671_, lean_object* v___f_672_, lean_object* v___x_673_, lean_object* v___x_674_, lean_object* v___f_675_, lean_object* v_x_676_, lean_object* v___y_677_){
_start:
{
uint8_t v___x_1436__boxed_678_; uint8_t v___x_1441__boxed_679_; lean_object* v_res_680_; 
v___x_1436__boxed_678_ = lean_unbox(v___x_669_);
v___x_1441__boxed_679_ = lean_unbox(v___x_674_);
v_res_680_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5(v_connectionContext_668_, v___x_1436__boxed_678_, v_a_670_, v___f_671_, v___f_672_, v___x_673_, v___x_1441__boxed_679_, v___f_675_, v_x_676_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(lean_object* v_config_681_, lean_object* v___x_682_, uint8_t v___x_683_, lean_object* v___f_684_, lean_object* v_x_685_){
_start:
{
if (lean_obj_tag(v_x_685_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v___f_684_);
lean_dec(v___x_682_);
v_a_687_ = lean_ctor_get(v_x_685_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v_x_685_);
if (v_isSharedCheck_695_ == 0)
{
v___x_689_ = v_x_685_;
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v_x_685_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_694_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; 
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
}
else
{
lean_object* v_lingeringTimeout_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
lean_dec_ref_known(v_x_685_, 1);
v_lingeringTimeout_696_ = lean_ctor_get(v_config_681_, 4);
v___x_697_ = l_Std_Async_Selector_sleep(v_lingeringTimeout_696_);
v___x_698_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_682_, v___x_683_, v___x_697_, v___f_684_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed(lean_object* v_config_699_, lean_object* v___x_700_, lean_object* v___x_701_, lean_object* v___f_702_, lean_object* v_x_703_, lean_object* v___y_704_){
_start:
{
uint8_t v___x_1510__boxed_705_; lean_object* v_res_706_; 
v___x_1510__boxed_705_ = lean_unbox(v___x_701_);
v_res_706_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6(v_config_699_, v___x_700_, v___x_1510__boxed_705_, v___f_702_, v_x_703_);
lean_dec_ref(v_config_699_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(lean_object* v_connectionContext_710_, uint8_t v___x_711_, lean_object* v_a_712_, lean_object* v___f_713_, lean_object* v___x_714_, lean_object* v___f_715_, lean_object* v_config_716_, lean_object* v___f_717_, lean_object* v_x_718_){
_start:
{
if (lean_obj_tag(v_x_718_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v___f_717_);
lean_dec_ref(v_config_716_);
lean_dec_ref(v___f_715_);
lean_dec(v___x_714_);
lean_dec_ref(v___f_713_);
lean_dec_ref(v_a_712_);
lean_dec_ref(v_connectionContext_710_);
v_a_720_ = lean_ctor_get(v_x_718_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v_x_718_);
if (v_isSharedCheck_728_ == 0)
{
v___x_722_ = v_x_718_;
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v_x_718_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_727_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; 
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_746_; 
v_a_729_ = lean_ctor_get(v_x_718_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_718_);
if (v_isSharedCheck_746_ == 0)
{
v___x_731_ = v_x_718_;
v_isShared_732_ = v_isSharedCheck_746_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v_x_718_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_746_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
uint8_t v___x_733_; lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_733_ = 0;
v___f_734_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___closed__0));
v___x_735_ = lean_box(v___x_711_);
v___x_736_ = lean_box(v___x_733_);
lean_inc_n(v___x_714_, 3);
v___f_737_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__5___boxed), 10, 8);
lean_closure_set(v___f_737_, 0, v_connectionContext_710_);
lean_closure_set(v___f_737_, 1, v___x_735_);
lean_closure_set(v___f_737_, 2, v_a_712_);
lean_closure_set(v___f_737_, 3, v___f_713_);
lean_closure_set(v___f_737_, 4, v___f_734_);
lean_closure_set(v___f_737_, 5, v___x_714_);
lean_closure_set(v___f_737_, 6, v___x_736_);
lean_closure_set(v___f_737_, 7, v___f_715_);
v___x_738_ = lean_box(v___x_733_);
v___f_739_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__6___boxed), 6, 4);
lean_closure_set(v___f_739_, 0, v_config_716_);
lean_closure_set(v___f_739_, 1, v___x_714_);
lean_closure_set(v___f_739_, 2, v___x_738_);
lean_closure_set(v___f_739_, 3, v___f_737_);
v___x_740_ = l_BaseIO_chainTask___redArg(v_a_729_, v___f_717_, v___x_714_, v___x_733_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_740_);
v___x_742_ = v___x_731_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_745_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
v___x_744_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_714_, v___x_733_, v___x_743_, v___f_739_);
return v___x_744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed(lean_object* v_connectionContext_747_, lean_object* v___x_748_, lean_object* v_a_749_, lean_object* v___f_750_, lean_object* v___x_751_, lean_object* v___f_752_, lean_object* v_config_753_, lean_object* v___f_754_, lean_object* v_x_755_, lean_object* v___y_756_){
_start:
{
uint8_t v___x_1550__boxed_757_; lean_object* v_res_758_; 
v___x_1550__boxed_757_ = lean_unbox(v___x_748_);
v_res_758_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7(v_connectionContext_747_, v___x_1550__boxed_757_, v_a_749_, v___f_750_, v___x_751_, v___f_752_, v_config_753_, v___f_754_, v_x_755_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(lean_object* v_inst_759_, lean_object* v_handler_760_, lean_object* v_head_761_, lean_object* v_connectionContext_762_, uint8_t v___x_763_, lean_object* v___f_764_, lean_object* v___f_765_, lean_object* v_config_766_, lean_object* v___f_767_, lean_object* v_x_768_){
_start:
{
if (lean_obj_tag(v_x_768_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v___f_767_);
lean_dec_ref(v_config_766_);
lean_dec_ref(v___f_765_);
lean_dec_ref(v___f_764_);
lean_dec_ref(v_connectionContext_762_);
lean_dec_ref(v_head_761_);
lean_dec(v_handler_760_);
lean_dec_ref(v_inst_759_);
v_a_770_ = lean_ctor_get(v_x_768_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_768_);
if (v_isSharedCheck_778_ == 0)
{
v___x_772_ = v_x_768_;
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v_x_768_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_777_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_799_; 
v_a_779_ = lean_ctor_get(v_x_768_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v_x_768_);
if (v_isSharedCheck_799_ == 0)
{
v___x_781_ = v_x_768_;
v_isShared_782_ = v_isSharedCheck_799_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v_x_768_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_799_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_onContinue_783_; lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___f_788_; uint8_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v_onContinue_783_ = lean_ctor_get(v_inst_759_, 3);
lean_inc_ref(v_onContinue_783_);
lean_dec_ref(v_inst_759_);
lean_inc(v_a_779_);
v___f_784_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_784_, 0, v_a_779_);
v___x_785_ = lean_apply_2(v_onContinue_783_, v_handler_760_, v_head_761_);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_box(v___x_763_);
v___f_788_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_788_, 0, v_connectionContext_762_);
lean_closure_set(v___f_788_, 1, v___x_787_);
lean_closure_set(v___f_788_, 2, v_a_779_);
lean_closure_set(v___f_788_, 3, v___f_764_);
lean_closure_set(v___f_788_, 4, v___x_786_);
lean_closure_set(v___f_788_, 5, v___f_765_);
lean_closure_set(v___f_788_, 6, v_config_766_);
lean_closure_set(v___f_788_, 7, v___f_784_);
v___x_789_ = 0;
v___x_790_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_790_, 0, lean_box(0));
lean_closure_set(v___x_790_, 1, v___x_785_);
v___x_791_ = lean_io_as_task(v___x_790_, v___x_786_);
v___x_792_ = 1;
v___x_793_ = lean_task_bind(v___x_791_, v___f_767_, v___x_786_, v___x_792_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_793_);
v___x_795_ = v___x_781_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_798_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
v___x_797_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_786_, v___x_789_, v___x_796_, v___f_788_);
return v___x_797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed(lean_object* v_inst_800_, lean_object* v_handler_801_, lean_object* v_head_802_, lean_object* v_connectionContext_803_, lean_object* v___x_804_, lean_object* v___f_805_, lean_object* v___f_806_, lean_object* v_config_807_, lean_object* v___f_808_, lean_object* v_x_809_, lean_object* v___y_810_){
_start:
{
uint8_t v___x_1633__boxed_811_; lean_object* v_res_812_; 
v___x_1633__boxed_811_ = lean_unbox(v___x_804_);
v_res_812_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8(v_inst_800_, v_handler_801_, v_head_802_, v_connectionContext_803_, v___x_1633__boxed_811_, v___f_805_, v___f_806_, v_config_807_, v___f_808_, v_x_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(lean_object* v_inst_815_, lean_object* v_handler_816_, lean_object* v_machine_817_, lean_object* v_head_818_, lean_object* v_config_819_, lean_object* v_connectionContext_820_){
_start:
{
lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___f_824_; uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___f_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___f_822_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_822_, 0, v_machine_817_);
v___f_823_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__0));
v___f_824_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___closed__1));
v___x_825_ = 0;
v___x_826_ = lean_box(v___x_825_);
v___f_827_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__8___boxed), 11, 9);
lean_closure_set(v___f_827_, 0, v_inst_815_);
lean_closure_set(v___f_827_, 1, v_handler_816_);
lean_closure_set(v___f_827_, 2, v_head_818_);
lean_closure_set(v___f_827_, 3, v_connectionContext_820_);
lean_closure_set(v___f_827_, 4, v___x_826_);
lean_closure_set(v___f_827_, 5, v___f_823_);
lean_closure_set(v___f_827_, 6, v___f_822_);
lean_closure_set(v___f_827_, 7, v_config_819_);
lean_closure_set(v___f_827_, 8, v___f_824_);
v___x_828_ = lean_box(0);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = l_Std_CloseableChannel_new___redArg(v___x_828_);
v___x_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
v___x_833_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_829_, v___x_825_, v___x_832_, v___f_827_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___boxed(lean_object* v_inst_834_, lean_object* v_handler_835_, lean_object* v_machine_836_, lean_object* v_head_837_, lean_object* v_config_838_, lean_object* v_connectionContext_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_834_, v_handler_835_, v_machine_836_, v_head_837_, v_config_838_, v_connectionContext_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(lean_object* v_00_u03c3_842_, lean_object* v_inst_843_, lean_object* v_handler_844_, lean_object* v_machine_845_, lean_object* v_head_846_, lean_object* v_config_847_, lean_object* v_connectionContext_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_843_, v_handler_844_, v_machine_845_, v_head_846_, v_config_847_, v_connectionContext_848_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___boxed(lean_object* v_00_u03c3_851_, lean_object* v_inst_852_, lean_object* v_handler_853_, lean_object* v_machine_854_, lean_object* v_head_855_, lean_object* v_config_856_, lean_object* v_connectionContext_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent(v_00_u03c3_851_, v_inst_852_, v_handler_853_, v_machine_854_, v_head_855_, v_config_856_, v_connectionContext_857_);
return v_res_859_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(lean_object* v_x_860_){
_start:
{
lean_object* v_fst_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_fst_861_ = lean_ctor_get(v_x_860_, 0);
v___x_862_ = l_Std_Http_Header_Name_contentLength;
v___x_863_ = lean_string_dec_eq(v_fst_861_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = l_Std_Http_Header_Name_transferEncoding;
v___x_865_ = lean_string_dec_eq(v_fst_861_, v___x_864_);
return v___x_865_;
}
else
{
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0___boxed(lean_object* v_x_866_){
_start:
{
uint8_t v_res_867_; lean_object* v_r_868_; 
v_res_867_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__0(v_x_866_);
lean_dec_ref(v_x_866_);
v_r_868_ = lean_box(v_res_867_);
return v_r_868_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(lean_object* v___y_869_, lean_object* v_____r_870_){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_872_ = lean_box(0);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___y_869_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed(lean_object* v___y_876_, lean_object* v_____r_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1(v___y_876_, v_____r_877_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(lean_object* v___f_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v___f_880_);
v_a_883_ = lean_ctor_get(v_x_881_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v_x_881_);
if (v_isSharedCheck_891_ == 0)
{
v___x_885_ = v_x_881_;
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v_x_881_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_890_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; 
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_893_; 
v_a_892_ = lean_ctor_get(v_x_881_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v_x_881_, 1);
v___x_893_ = lean_apply_2(v___f_880_, v_a_892_, lean_box(0));
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed(lean_object* v___f_894_, lean_object* v_x_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2(v___f_894_, v_x_895_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(lean_object* v_close_898_, lean_object* v_body_899_, lean_object* v___f_900_, lean_object* v___f_901_, lean_object* v_x_902_){
_start:
{
if (lean_obj_tag(v_x_902_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref(v___f_901_);
lean_dec_ref(v___f_900_);
lean_dec(v_body_899_);
lean_dec_ref(v_close_898_);
v_a_904_ = lean_ctor_get(v_x_902_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v_x_902_);
if (v_isSharedCheck_912_ == 0)
{
v___x_906_ = v_x_902_;
v_isShared_907_ = v_isSharedCheck_912_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v_x_902_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_912_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_911_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_910_; 
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
}
}
else
{
lean_object* v_a_913_; uint8_t v___x_914_; 
v_a_913_ = lean_ctor_get(v_x_902_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v_x_902_, 1);
v___x_914_ = lean_unbox(v_a_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; 
lean_dec_ref(v___f_901_);
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = lean_apply_2(v_close_898_, v_body_899_, lean_box(0));
v___x_917_ = lean_unbox(v_a_913_);
lean_dec(v_a_913_);
v___x_918_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_915_, v___x_917_, v___x_916_, v___f_900_);
return v___x_918_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec(v_a_913_);
lean_dec_ref(v___f_900_);
lean_dec(v_body_899_);
lean_dec_ref(v_close_898_);
v___x_919_ = lean_box(0);
v___x_920_ = lean_apply_2(v___f_901_, v___x_919_, lean_box(0));
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed(lean_object* v_close_921_, lean_object* v_body_922_, lean_object* v___f_923_, lean_object* v___f_924_, lean_object* v_x_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3(v_close_921_, v_body_922_, v___f_923_, v___f_924_, v_x_925_);
return v_res_927_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(lean_object* v___x_928_, lean_object* v_x_929_){
_start:
{
lean_object* v_fst_930_; uint8_t v___x_931_; 
v_fst_930_ = lean_ctor_get(v_x_929_, 0);
v___x_931_ = lean_string_dec_eq(v_fst_930_, v___x_928_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed(lean_object* v___x_932_, lean_object* v_x_933_){
_start:
{
uint8_t v_res_934_; lean_object* v_r_935_; 
v_res_934_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4(v___x_932_, v_x_933_);
lean_dec_ref(v_x_933_);
lean_dec_ref(v___x_932_);
v_r_935_ = lean_box(v_res_934_);
return v_r_935_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(lean_object* v___x_936_, lean_object* v_x1_937_, lean_object* v_x2_938_){
_start:
{
lean_object* v_fst_939_; uint8_t v___x_940_; 
v_fst_939_ = lean_ctor_get(v_x2_938_, 0);
v___x_940_ = lean_string_dec_eq(v_fst_939_, v___x_936_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
v___x_941_ = lean_array_push(v_x1_937_, v_x2_938_);
return v___x_941_;
}
else
{
lean_dec_ref(v_x2_938_);
return v_x1_937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed(lean_object* v___x_942_, lean_object* v_x1_943_, lean_object* v_x2_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5(v___x_942_, v_x1_943_, v_x2_944_);
lean_dec_ref(v___x_942_);
return v_res_945_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__0));
v___x_948_ = lean_string_to_utf8(v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1);
v___x_950_ = lean_byte_array_size(v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__4));
v___x_954_ = lean_string_to_utf8(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = l_ByteArray_empty;
v___x_956_ = lean_byte_array_size(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5);
v___x_958_ = lean_byte_array_size(v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__8));
v___x_961_ = lean_string_to_utf8(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9);
v___x_963_ = lean_byte_array_size(v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__21(void){
_start:
{
lean_object* v___x_983_; lean_object* v___f_984_; 
v___x_983_ = l_Std_Http_Header_Name_transferEncoding;
v___f_984_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_984_, 0, v___x_983_);
return v___f_984_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__22(void){
_start:
{
lean_object* v___x_985_; lean_object* v___f_986_; 
v___x_985_ = l_Std_Http_Header_Name_transferEncoding;
v___f_986_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_986_, 0, v___x_985_);
return v___f_986_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__24(void){
_start:
{
lean_object* v___x_989_; lean_object* v___f_990_; 
v___x_989_ = l_Std_Http_Header_Name_contentLength;
v___f_990_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_990_, 0, v___x_989_);
return v___f_990_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__25(void){
_start:
{
lean_object* v___x_991_; lean_object* v___f_992_; 
v___x_991_ = l_Std_Http_Header_Name_contentLength;
v___f_992_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_992_, 0, v___x_991_);
return v___f_992_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(lean_object* v_body_993_, lean_object* v_close_994_, lean_object* v_isClosed_995_, lean_object* v_line_996_, lean_object* v___f_997_, lean_object* v_machine_998_, lean_object* v_x_999_){
_start:
{
lean_object* v___y_1002_; uint8_t v_omitBody_1003_; lean_object* v___y_1016_; uint8_t v___y_1020_; uint8_t v___y_1021_; lean_object* v_reader_1022_; lean_object* v_writer_1023_; lean_object* v_config_1024_; lean_object* v_events_1025_; lean_object* v_error_1026_; lean_object* v_date_1027_; uint8_t v_keepAlive_1028_; uint8_t v_pullBodyStalled_1029_; uint8_t v___y_1030_; uint8_t v___y_1098_; lean_object* v___y_1099_; uint8_t v___y_1100_; uint8_t v___y_1120_; lean_object* v___y_1121_; uint8_t v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1128_; uint8_t v___y_1129_; uint16_t v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; uint8_t v___y_1151_; uint8_t v___y_1152_; lean_object* v_val_1153_; lean_object* v___y_1163_; uint8_t v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; uint8_t v___y_1169_; uint8_t v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; uint8_t v___y_1173_; lean_object* v___y_1174_; uint8_t v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; uint8_t v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; uint8_t v___y_1187_; uint8_t v___y_1188_; uint8_t v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; uint8_t v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; uint8_t v___y_1205_; uint8_t v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; uint8_t v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; uint8_t v___y_1217_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; uint8_t v___y_1236_; uint8_t v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; uint8_t v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; uint8_t v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; uint8_t v___y_1246_; uint8_t v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; uint8_t v___y_1266_; uint8_t v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; uint8_t v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; uint8_t v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; uint8_t v___y_1276_; uint8_t v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; uint8_t v___y_1317_; uint8_t v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; uint8_t v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; uint8_t v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; uint8_t v___y_1327_; uint8_t v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1345_; uint8_t v___y_1346_; lean_object* v___y_1347_; uint8_t v___y_1348_; uint8_t v___y_1349_; lean_object* v___y_1354_; uint8_t v___y_1355_; uint16_t v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; uint8_t v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; uint8_t v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; uint8_t v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1372_; uint8_t v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; uint8_t v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1398_; uint8_t v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; uint8_t v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; uint8_t v___y_1405_; lean_object* v___y_1406_; uint8_t v___y_1407_; uint8_t v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; uint8_t v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; uint8_t v___y_1425_; uint8_t v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; uint8_t v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; uint8_t v___y_1432_; lean_object* v___y_1433_; uint8_t v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; uint8_t v___y_1437_; uint8_t v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; uint8_t v___y_1445_; uint8_t v___y_1446_; uint8_t v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; uint8_t v___y_1450_; lean_object* v___y_1451_; uint8_t v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; uint8_t v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1472_; lean_object* v_reader_1473_; lean_object* v_userData_1474_; lean_object* v_outputData_1475_; lean_object* v_state_1476_; lean_object* v_knownSize_1477_; lean_object* v_messageHead_1478_; uint8_t v_userClosedBody_1479_; uint8_t v_omitBody_1480_; lean_object* v_userDataBytes_1481_; lean_object* v_config_1482_; lean_object* v_events_1483_; lean_object* v_error_1484_; lean_object* v_date_1485_; uint8_t v_keepAlive_1486_; uint8_t v_pullBodyStalled_1487_; 
if (lean_obj_tag(v_x_999_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref(v_machine_998_);
lean_dec_ref(v___f_997_);
lean_dec_ref(v_line_996_);
lean_dec_ref(v_isClosed_995_);
lean_dec_ref(v_close_994_);
lean_dec(v_body_993_);
v_a_1516_ = lean_ctor_get(v_x_999_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_x_999_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1518_ = v_x_999_;
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v_x_999_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
return v___x_1522_;
}
}
}
else
{
lean_object* v_a_1525_; 
v_a_1525_ = lean_ctor_get(v_x_999_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v_x_999_, 1);
if (lean_obj_tag(v_a_1525_) == 1)
{
lean_object* v_writer_1526_; lean_object* v_reader_1527_; lean_object* v_config_1528_; lean_object* v_events_1529_; lean_object* v_error_1530_; lean_object* v_date_1531_; uint8_t v_keepAlive_1532_; uint8_t v_pullBodyStalled_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1555_; 
v_writer_1526_ = lean_ctor_get(v_machine_998_, 1);
v_reader_1527_ = lean_ctor_get(v_machine_998_, 0);
v_config_1528_ = lean_ctor_get(v_machine_998_, 2);
v_events_1529_ = lean_ctor_get(v_machine_998_, 3);
v_error_1530_ = lean_ctor_get(v_machine_998_, 4);
v_date_1531_ = lean_ctor_get(v_machine_998_, 5);
v_keepAlive_1532_ = lean_ctor_get_uint8(v_machine_998_, sizeof(void*)*6);
v_pullBodyStalled_1533_ = lean_ctor_get_uint8(v_machine_998_, sizeof(void*)*6 + 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_machine_998_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1535_ = v_machine_998_;
v_isShared_1536_ = v_isSharedCheck_1555_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_date_1531_);
lean_inc(v_error_1530_);
lean_inc(v_events_1529_);
lean_inc(v_config_1528_);
lean_inc(v_writer_1526_);
lean_inc(v_reader_1527_);
lean_dec(v_machine_998_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1555_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v_userData_1537_; lean_object* v_outputData_1538_; lean_object* v_state_1539_; lean_object* v_messageHead_1540_; uint8_t v_userClosedBody_1541_; uint8_t v_omitBody_1542_; lean_object* v_userDataBytes_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1553_; 
v_userData_1537_ = lean_ctor_get(v_writer_1526_, 0);
v_outputData_1538_ = lean_ctor_get(v_writer_1526_, 1);
v_state_1539_ = lean_ctor_get(v_writer_1526_, 2);
v_messageHead_1540_ = lean_ctor_get(v_writer_1526_, 4);
v_userClosedBody_1541_ = lean_ctor_get_uint8(v_writer_1526_, sizeof(void*)*6);
v_omitBody_1542_ = lean_ctor_get_uint8(v_writer_1526_, sizeof(void*)*6 + 1);
v_userDataBytes_1543_ = lean_ctor_get(v_writer_1526_, 5);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_writer_1526_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; 
v_unused_1554_ = lean_ctor_get(v_writer_1526_, 3);
lean_dec(v_unused_1554_);
v___x_1545_ = v_writer_1526_;
v_isShared_1546_ = v_isSharedCheck_1553_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_userDataBytes_1543_);
lean_inc(v_messageHead_1540_);
lean_inc(v_state_1539_);
lean_inc(v_outputData_1538_);
lean_inc(v_userData_1537_);
lean_dec(v_writer_1526_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1553_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
lean_inc(v_userDataBytes_1543_);
lean_inc(v_messageHead_1540_);
lean_inc_ref(v_a_1525_);
lean_inc(v_state_1539_);
lean_inc_ref(v_outputData_1538_);
lean_inc_ref(v_userData_1537_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 3, v_a_1525_);
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_userData_1537_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_outputData_1538_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_state_1539_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_a_1525_);
lean_ctor_set(v_reuseFailAlloc_1552_, 4, v_messageHead_1540_);
lean_ctor_set(v_reuseFailAlloc_1552_, 5, v_userDataBytes_1543_);
lean_ctor_set_uint8(v_reuseFailAlloc_1552_, sizeof(void*)*6, v_userClosedBody_1541_);
lean_ctor_set_uint8(v_reuseFailAlloc_1552_, sizeof(void*)*6 + 1, v_omitBody_1542_);
v___x_1548_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1550_; 
lean_inc(v_date_1531_);
lean_inc(v_error_1530_);
lean_inc_ref(v_events_1529_);
lean_inc_ref(v_config_1528_);
lean_inc_ref(v_reader_1527_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 1, v___x_1548_);
v___x_1550_ = v___x_1535_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_reader_1527_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1551_, 2, v_config_1528_);
lean_ctor_set(v_reuseFailAlloc_1551_, 3, v_events_1529_);
lean_ctor_set(v_reuseFailAlloc_1551_, 4, v_error_1530_);
lean_ctor_set(v_reuseFailAlloc_1551_, 5, v_date_1531_);
lean_ctor_set_uint8(v_reuseFailAlloc_1551_, sizeof(void*)*6, v_keepAlive_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1551_, sizeof(void*)*6 + 1, v_pullBodyStalled_1533_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
v___y_1472_ = v___x_1550_;
v_reader_1473_ = v_reader_1527_;
v_userData_1474_ = v_userData_1537_;
v_outputData_1475_ = v_outputData_1538_;
v_state_1476_ = v_state_1539_;
v_knownSize_1477_ = v_a_1525_;
v_messageHead_1478_ = v_messageHead_1540_;
v_userClosedBody_1479_ = v_userClosedBody_1541_;
v_omitBody_1480_ = v_omitBody_1542_;
v_userDataBytes_1481_ = v_userDataBytes_1543_;
v_config_1482_ = v_config_1528_;
v_events_1483_ = v_events_1529_;
v_error_1484_ = v_error_1530_;
v_date_1485_ = v_date_1531_;
v_keepAlive_1486_ = v_keepAlive_1532_;
v_pullBodyStalled_1487_ = v_pullBodyStalled_1533_;
goto v___jp_1471_;
}
}
}
}
}
else
{
lean_object* v_writer_1556_; lean_object* v_reader_1557_; lean_object* v_config_1558_; lean_object* v_events_1559_; lean_object* v_error_1560_; lean_object* v_date_1561_; uint8_t v_keepAlive_1562_; uint8_t v_pullBodyStalled_1563_; lean_object* v_userData_1564_; lean_object* v_outputData_1565_; lean_object* v_state_1566_; lean_object* v_knownSize_1567_; lean_object* v_messageHead_1568_; uint8_t v_userClosedBody_1569_; uint8_t v_omitBody_1570_; lean_object* v_userDataBytes_1571_; 
lean_dec(v_a_1525_);
v_writer_1556_ = lean_ctor_get(v_machine_998_, 1);
v_reader_1557_ = lean_ctor_get(v_machine_998_, 0);
lean_inc_ref(v_reader_1557_);
v_config_1558_ = lean_ctor_get(v_machine_998_, 2);
lean_inc_ref(v_config_1558_);
v_events_1559_ = lean_ctor_get(v_machine_998_, 3);
lean_inc_ref(v_events_1559_);
v_error_1560_ = lean_ctor_get(v_machine_998_, 4);
lean_inc(v_error_1560_);
v_date_1561_ = lean_ctor_get(v_machine_998_, 5);
lean_inc(v_date_1561_);
v_keepAlive_1562_ = lean_ctor_get_uint8(v_machine_998_, sizeof(void*)*6);
v_pullBodyStalled_1563_ = lean_ctor_get_uint8(v_machine_998_, sizeof(void*)*6 + 1);
v_userData_1564_ = lean_ctor_get(v_writer_1556_, 0);
lean_inc_ref(v_userData_1564_);
v_outputData_1565_ = lean_ctor_get(v_writer_1556_, 1);
lean_inc_ref(v_outputData_1565_);
v_state_1566_ = lean_ctor_get(v_writer_1556_, 2);
lean_inc(v_state_1566_);
v_knownSize_1567_ = lean_ctor_get(v_writer_1556_, 3);
lean_inc(v_knownSize_1567_);
v_messageHead_1568_ = lean_ctor_get(v_writer_1556_, 4);
lean_inc(v_messageHead_1568_);
v_userClosedBody_1569_ = lean_ctor_get_uint8(v_writer_1556_, sizeof(void*)*6);
v_omitBody_1570_ = lean_ctor_get_uint8(v_writer_1556_, sizeof(void*)*6 + 1);
v_userDataBytes_1571_ = lean_ctor_get(v_writer_1556_, 5);
lean_inc(v_userDataBytes_1571_);
v___y_1472_ = v_machine_998_;
v_reader_1473_ = v_reader_1557_;
v_userData_1474_ = v_userData_1564_;
v_outputData_1475_ = v_outputData_1565_;
v_state_1476_ = v_state_1566_;
v_knownSize_1477_ = v_knownSize_1567_;
v_messageHead_1478_ = v_messageHead_1568_;
v_userClosedBody_1479_ = v_userClosedBody_1569_;
v_omitBody_1480_ = v_omitBody_1570_;
v_userDataBytes_1481_ = v_userDataBytes_1571_;
v_config_1482_ = v_config_1558_;
v_events_1483_ = v_events_1559_;
v_error_1484_ = v_error_1560_;
v_date_1485_ = v_date_1561_;
v_keepAlive_1486_ = v_keepAlive_1562_;
v_pullBodyStalled_1487_ = v_pullBodyStalled_1563_;
goto v___jp_1471_;
}
}
v___jp_1001_:
{
if (v_omitBody_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec_ref(v_isClosed_995_);
lean_dec_ref(v_close_994_);
v___x_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_body_993_);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___y_1002_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
else
{
lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___f_1008_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1008_, 0, v___y_1002_);
lean_inc_ref(v___f_1008_);
v___f_1009_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1009_, 0, v___f_1008_);
lean_inc(v_body_993_);
v___f_1010_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_1010_, 0, v_close_994_);
lean_closure_set(v___f_1010_, 1, v_body_993_);
lean_closure_set(v___f_1010_, 2, v___f_1009_);
lean_closure_set(v___f_1010_, 3, v___f_1008_);
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = 0;
v___x_1013_ = lean_apply_2(v_isClosed_995_, v_body_993_, lean_box(0));
v___x_1014_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1011_, v___x_1012_, v___x_1013_, v___f_1010_);
return v___x_1014_;
}
}
v___jp_1015_:
{
lean_object* v_writer_1017_; uint8_t v_omitBody_1018_; 
v_writer_1017_ = lean_ctor_get(v___y_1016_, 1);
v_omitBody_1018_ = lean_ctor_get_uint8(v_writer_1017_, sizeof(void*)*6 + 1);
v___y_1002_ = v___y_1016_;
v_omitBody_1003_ = v_omitBody_1018_;
goto v___jp_1001_;
}
v___jp_1019_:
{
lean_object* v_userData_1031_; lean_object* v_outputData_1032_; lean_object* v_state_1033_; lean_object* v_knownSize_1034_; uint8_t v_userClosedBody_1035_; uint8_t v_omitBody_1036_; lean_object* v_userDataBytes_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1095_; 
v_userData_1031_ = lean_ctor_get(v_writer_1023_, 0);
v_outputData_1032_ = lean_ctor_get(v_writer_1023_, 1);
v_state_1033_ = lean_ctor_get(v_writer_1023_, 2);
v_knownSize_1034_ = lean_ctor_get(v_writer_1023_, 3);
v_userClosedBody_1035_ = lean_ctor_get_uint8(v_writer_1023_, sizeof(void*)*6);
v_omitBody_1036_ = lean_ctor_get_uint8(v_writer_1023_, sizeof(void*)*6 + 1);
v_userDataBytes_1037_ = lean_ctor_get(v_writer_1023_, 5);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_writer_1023_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v_writer_1023_, 4);
lean_dec(v_unused_1096_);
v___x_1039_ = v_writer_1023_;
v_isShared_1040_ = v_isSharedCheck_1095_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_userDataBytes_1037_);
lean_inc(v_knownSize_1034_);
lean_inc(v_state_1033_);
lean_inc(v_outputData_1032_);
lean_inc(v_userData_1031_);
lean_dec(v_writer_1023_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1095_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
lean_inc_ref(v_line_996_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v_line_996_);
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_userData_1031_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_outputData_1032_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v_state_1033_);
lean_ctor_set(v_reuseFailAlloc_1094_, 3, v_knownSize_1034_);
lean_ctor_set(v_reuseFailAlloc_1094_, 4, v_line_996_);
lean_ctor_set(v_reuseFailAlloc_1094_, 5, v_userDataBytes_1037_);
lean_ctor_set_uint8(v_reuseFailAlloc_1094_, sizeof(void*)*6, v_userClosedBody_1035_);
lean_ctor_set_uint8(v_reuseFailAlloc_1094_, sizeof(void*)*6 + 1, v_omitBody_1036_);
v___x_1042_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v_machine_1043_; lean_object* v_machine_1044_; lean_object* v_writer_1045_; lean_object* v_reader_1046_; lean_object* v_config_1047_; lean_object* v_events_1048_; lean_object* v_error_1049_; lean_object* v_date_1050_; uint8_t v_keepAlive_1051_; uint8_t v_pullBodyStalled_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1093_; 
v_machine_1043_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_machine_1043_, 0, v_reader_1022_);
lean_ctor_set(v_machine_1043_, 1, v___x_1042_);
lean_ctor_set(v_machine_1043_, 2, v_config_1024_);
lean_ctor_set(v_machine_1043_, 3, v_events_1025_);
lean_ctor_set(v_machine_1043_, 4, v_error_1026_);
lean_ctor_set(v_machine_1043_, 5, v_date_1027_);
lean_ctor_set_uint8(v_machine_1043_, sizeof(void*)*6, v_keepAlive_1028_);
lean_ctor_set_uint8(v_machine_1043_, sizeof(void*)*6 + 1, v_pullBodyStalled_1029_);
v_machine_1044_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_maybeSuppressOutgoingBody(v___y_1020_, v_machine_1043_, v_line_996_);
lean_dec_ref(v_line_996_);
v_writer_1045_ = lean_ctor_get(v_machine_1044_, 1);
v_reader_1046_ = lean_ctor_get(v_machine_1044_, 0);
v_config_1047_ = lean_ctor_get(v_machine_1044_, 2);
v_events_1048_ = lean_ctor_get(v_machine_1044_, 3);
v_error_1049_ = lean_ctor_get(v_machine_1044_, 4);
v_date_1050_ = lean_ctor_get(v_machine_1044_, 5);
v_keepAlive_1051_ = lean_ctor_get_uint8(v_machine_1044_, sizeof(void*)*6);
v_pullBodyStalled_1052_ = lean_ctor_get_uint8(v_machine_1044_, sizeof(void*)*6 + 1);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_machine_1044_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1054_ = v_machine_1044_;
v_isShared_1055_ = v_isSharedCheck_1093_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_date_1050_);
lean_inc(v_error_1049_);
lean_inc(v_events_1048_);
lean_inc(v_config_1047_);
lean_inc(v_writer_1045_);
lean_inc(v_reader_1046_);
lean_dec(v_machine_1044_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1093_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v_userData_1056_; lean_object* v_outputData_1057_; lean_object* v_knownSize_1058_; lean_object* v_messageHead_1059_; uint8_t v_userClosedBody_1060_; uint8_t v_omitBody_1061_; lean_object* v_userDataBytes_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1091_; 
v_userData_1056_ = lean_ctor_get(v_writer_1045_, 0);
v_outputData_1057_ = lean_ctor_get(v_writer_1045_, 1);
v_knownSize_1058_ = lean_ctor_get(v_writer_1045_, 3);
v_messageHead_1059_ = lean_ctor_get(v_writer_1045_, 4);
v_userClosedBody_1060_ = lean_ctor_get_uint8(v_writer_1045_, sizeof(void*)*6);
v_omitBody_1061_ = lean_ctor_get_uint8(v_writer_1045_, sizeof(void*)*6 + 1);
v_userDataBytes_1062_ = lean_ctor_get(v_writer_1045_, 5);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_writer_1045_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v_writer_1045_, 2);
lean_dec(v_unused_1092_);
v___x_1064_ = v_writer_1045_;
v_isShared_1065_ = v_isSharedCheck_1091_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_userDataBytes_1062_);
lean_inc(v_messageHead_1059_);
lean_inc(v_knownSize_1058_);
lean_inc(v_outputData_1057_);
lean_inc(v_userData_1056_);
lean_dec(v_writer_1045_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1091_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = lean_box(2);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 2, v___x_1066_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_userData_1056_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_outputData_1057_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1090_, 3, v_knownSize_1058_);
lean_ctor_set(v_reuseFailAlloc_1090_, 4, v_messageHead_1059_);
lean_ctor_set(v_reuseFailAlloc_1090_, 5, v_userDataBytes_1062_);
lean_ctor_set_uint8(v_reuseFailAlloc_1090_, sizeof(void*)*6, v_userClosedBody_1060_);
lean_ctor_set_uint8(v_reuseFailAlloc_1090_, sizeof(void*)*6 + 1, v_omitBody_1061_);
v___x_1068_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
if (v___y_1030_ == 0)
{
lean_object* v_machine_1070_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v___x_1068_);
v_machine_1070_ = v___x_1054_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_reader_1046_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1071_, 2, v_config_1047_);
lean_ctor_set(v_reuseFailAlloc_1071_, 3, v_events_1048_);
lean_ctor_set(v_reuseFailAlloc_1071_, 4, v_error_1049_);
lean_ctor_set(v_reuseFailAlloc_1071_, 5, v_date_1050_);
lean_ctor_set_uint8(v_reuseFailAlloc_1071_, sizeof(void*)*6, v_keepAlive_1051_);
lean_ctor_set_uint8(v_reuseFailAlloc_1071_, sizeof(void*)*6 + 1, v_pullBodyStalled_1052_);
v_machine_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
v___y_1002_ = v_machine_1070_;
v_omitBody_1003_ = v_omitBody_1061_;
goto v___jp_1001_;
}
}
else
{
lean_object* v_input_1072_; lean_object* v_messageHead_1073_; lean_object* v_messageCount_1074_; lean_object* v_bodyBytesRead_1075_; lean_object* v_headerBytesRead_1076_; uint8_t v_peerClosed_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1088_; 
v_input_1072_ = lean_ctor_get(v_reader_1046_, 1);
v_messageHead_1073_ = lean_ctor_get(v_reader_1046_, 2);
v_messageCount_1074_ = lean_ctor_get(v_reader_1046_, 3);
v_bodyBytesRead_1075_ = lean_ctor_get(v_reader_1046_, 4);
v_headerBytesRead_1076_ = lean_ctor_get(v_reader_1046_, 5);
v_peerClosed_1077_ = lean_ctor_get_uint8(v_reader_1046_, sizeof(void*)*6);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_reader_1046_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v_reader_1046_, 0);
lean_dec(v_unused_1089_);
v___x_1079_ = v_reader_1046_;
v_isShared_1080_ = v_isSharedCheck_1088_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_headerBytesRead_1076_);
lean_inc(v_bodyBytesRead_1075_);
lean_inc(v_messageCount_1074_);
lean_inc(v_messageHead_1073_);
lean_inc(v_input_1072_);
lean_dec(v_reader_1046_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1088_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1081_ = lean_box(6);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1081_);
v___x_1083_ = v___x_1079_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_input_1072_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_messageHead_1073_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v_messageCount_1074_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v_bodyBytesRead_1075_);
lean_ctor_set(v_reuseFailAlloc_1087_, 5, v_headerBytesRead_1076_);
lean_ctor_set_uint8(v_reuseFailAlloc_1087_, sizeof(void*)*6, v_peerClosed_1077_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; 
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*6 + 1, v___y_1030_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v___x_1068_);
lean_ctor_set(v___x_1054_, 0, v___x_1083_);
v___x_1085_ = v___x_1054_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_config_1047_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v_events_1048_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v_error_1049_);
lean_ctor_set(v_reuseFailAlloc_1086_, 5, v_date_1050_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*6, v___y_1021_);
lean_ctor_set_uint8(v___x_1085_, sizeof(void*)*6 + 1, v___y_1021_);
v___y_1002_ = v___x_1085_;
v_omitBody_1003_ = v_omitBody_1061_;
goto v___jp_1001_;
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
v___jp_1097_:
{
lean_object* v_reader_1101_; lean_object* v_messageHead_1102_; lean_object* v_writer_1103_; lean_object* v_config_1104_; lean_object* v_events_1105_; lean_object* v_error_1106_; lean_object* v_date_1107_; uint8_t v_keepAlive_1108_; uint8_t v_pullBodyStalled_1109_; uint8_t v_method_1110_; uint8_t v___x_1111_; uint8_t v___x_1112_; 
v_reader_1101_ = lean_ctor_get(v___y_1099_, 0);
lean_inc_ref(v_reader_1101_);
v_messageHead_1102_ = lean_ctor_get(v_reader_1101_, 2);
v_writer_1103_ = lean_ctor_get(v___y_1099_, 1);
lean_inc_ref(v_writer_1103_);
v_config_1104_ = lean_ctor_get(v___y_1099_, 2);
lean_inc_ref(v_config_1104_);
v_events_1105_ = lean_ctor_get(v___y_1099_, 3);
lean_inc_ref(v_events_1105_);
v_error_1106_ = lean_ctor_get(v___y_1099_, 4);
lean_inc(v_error_1106_);
v_date_1107_ = lean_ctor_get(v___y_1099_, 5);
lean_inc(v_date_1107_);
v_keepAlive_1108_ = lean_ctor_get_uint8(v___y_1099_, sizeof(void*)*6);
v_pullBodyStalled_1109_ = lean_ctor_get_uint8(v___y_1099_, sizeof(void*)*6 + 1);
lean_dec_ref(v___y_1099_);
v_method_1110_ = lean_ctor_get_uint8(v_messageHead_1102_, sizeof(void*)*2);
v___x_1111_ = 5;
v___x_1112_ = l_Std_Http_instBEqMethod_beq(v_method_1110_, v___x_1111_);
if (v___x_1112_ == 0)
{
v___y_1020_ = v___y_1098_;
v___y_1021_ = v___y_1100_;
v_reader_1022_ = v_reader_1101_;
v_writer_1023_ = v_writer_1103_;
v_config_1024_ = v_config_1104_;
v_events_1025_ = v_events_1105_;
v_error_1026_ = v_error_1106_;
v_date_1027_ = v_date_1107_;
v_keepAlive_1028_ = v_keepAlive_1108_;
v_pullBodyStalled_1029_ = v_pullBodyStalled_1109_;
v___y_1030_ = v___x_1112_;
goto v___jp_1019_;
}
else
{
lean_object* v_status_1113_; uint16_t v___x_1114_; uint16_t v___x_1115_; uint8_t v___x_1116_; 
v_status_1113_ = lean_ctor_get(v_line_996_, 0);
v___x_1114_ = 200;
v___x_1115_ = l_Std_Http_Status_toCode(v_status_1113_);
v___x_1116_ = lean_uint16_dec_le(v___x_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
v___y_1020_ = v___y_1098_;
v___y_1021_ = v___y_1100_;
v_reader_1022_ = v_reader_1101_;
v_writer_1023_ = v_writer_1103_;
v_config_1024_ = v_config_1104_;
v_events_1025_ = v_events_1105_;
v_error_1026_ = v_error_1106_;
v_date_1027_ = v_date_1107_;
v_keepAlive_1028_ = v_keepAlive_1108_;
v_pullBodyStalled_1029_ = v_pullBodyStalled_1109_;
v___y_1030_ = v___x_1116_;
goto v___jp_1019_;
}
else
{
uint16_t v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = 300;
v___x_1118_ = lean_uint16_dec_lt(v___x_1115_, v___x_1117_);
v___y_1020_ = v___y_1098_;
v___y_1021_ = v___y_1100_;
v_reader_1022_ = v_reader_1101_;
v_writer_1023_ = v_writer_1103_;
v_config_1024_ = v_config_1104_;
v_events_1025_ = v_events_1105_;
v_error_1026_ = v_error_1106_;
v_date_1027_ = v_date_1107_;
v_keepAlive_1028_ = v_keepAlive_1108_;
v_pullBodyStalled_1029_ = v_pullBodyStalled_1109_;
v___y_1030_ = v___x_1118_;
goto v___jp_1019_;
}
}
}
v___jp_1119_:
{
uint8_t v___x_1122_; 
v___x_1122_ = 0;
v___y_1098_ = v___y_1120_;
v___y_1099_ = v___y_1121_;
v___y_1100_ = v___x_1122_;
goto v___jp_1097_;
}
v___jp_1123_:
{
lean_object* v___x_1126_; 
v___x_1126_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_rejectOutgoingFraming(v___y_1124_, v___y_1125_);
v___y_1016_ = v___x_1126_;
goto v___jp_1015_;
}
v___jp_1127_:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = lean_unsigned_to_nat(204u);
v___x_1134_ = lean_nat_dec_eq(v___y_1131_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = lean_unsigned_to_nat(304u);
v___x_1136_ = lean_nat_dec_eq(v___y_1131_, v___x_1135_);
lean_dec(v___y_1131_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_box(9);
v___x_1138_ = l_Std_Http_instBEqStatus_beq(v___y_1128_, v___x_1137_);
lean_dec(v___y_1128_);
if (v___x_1138_ == 0)
{
lean_object* v_reader_1139_; lean_object* v_messageHead_1140_; uint8_t v_method_1141_; uint8_t v___x_1142_; uint8_t v___x_1143_; 
v_reader_1139_ = lean_ctor_get(v___y_1132_, 0);
v_messageHead_1140_ = lean_ctor_get(v_reader_1139_, 2);
v_method_1141_ = lean_ctor_get_uint8(v_messageHead_1140_, sizeof(void*)*2);
v___x_1142_ = 9;
v___x_1143_ = l_Std_Http_instBEqMethod_beq(v_method_1141_, v___x_1142_);
if (v___x_1143_ == 0)
{
uint8_t v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = 5;
v___x_1145_ = l_Std_Http_instBEqMethod_beq(v_method_1141_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_dec_ref(v_line_996_);
v___y_1124_ = v___y_1129_;
v___y_1125_ = v___y_1132_;
goto v___jp_1123_;
}
else
{
uint16_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = 200;
v___x_1147_ = lean_uint16_dec_le(v___x_1146_, v___y_1130_);
if (v___x_1147_ == 0)
{
lean_dec_ref(v_line_996_);
v___y_1124_ = v___y_1129_;
v___y_1125_ = v___y_1132_;
goto v___jp_1123_;
}
else
{
uint16_t v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = 300;
v___x_1149_ = lean_uint16_dec_lt(v___y_1130_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_dec_ref(v_line_996_);
v___y_1124_ = v___y_1129_;
v___y_1125_ = v___y_1132_;
goto v___jp_1123_;
}
else
{
v___y_1120_ = v___y_1129_;
v___y_1121_ = v___y_1132_;
goto v___jp_1119_;
}
}
}
}
else
{
v___y_1120_ = v___y_1129_;
v___y_1121_ = v___y_1132_;
goto v___jp_1119_;
}
}
else
{
v___y_1120_ = v___y_1129_;
v___y_1121_ = v___y_1132_;
goto v___jp_1119_;
}
}
else
{
lean_dec(v___y_1128_);
v___y_1120_ = v___y_1129_;
v___y_1121_ = v___y_1132_;
goto v___jp_1119_;
}
}
else
{
lean_dec(v___y_1131_);
lean_dec(v___y_1128_);
v___y_1120_ = v___y_1129_;
v___y_1121_ = v___y_1132_;
goto v___jp_1119_;
}
}
v___jp_1150_:
{
uint8_t v___x_1154_; 
v___x_1154_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_unframeableForHttp10(v___y_1151_, v_val_1153_, v_line_996_);
if (v___x_1154_ == 0)
{
v___y_1098_ = v___y_1151_;
v___y_1099_ = v_val_1153_;
v___y_1100_ = v___y_1152_;
goto v___jp_1097_;
}
else
{
lean_object* v_status_1155_; uint16_t v___x_1156_; lean_object* v_code_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v_status_1155_ = lean_ctor_get(v_line_996_, 0);
v___x_1156_ = l_Std_Http_Status_toCode(v_status_1155_);
v_code_1157_ = lean_uint16_to_nat(v___x_1156_);
v___x_1158_ = lean_unsigned_to_nat(100u);
v___x_1159_ = lean_nat_dec_le(v___x_1158_, v_code_1157_);
if (v___x_1159_ == 0)
{
lean_inc(v_status_1155_);
v___y_1128_ = v_status_1155_;
v___y_1129_ = v___y_1151_;
v___y_1130_ = v___x_1156_;
v___y_1131_ = v_code_1157_;
v___y_1132_ = v_val_1153_;
goto v___jp_1127_;
}
else
{
lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = lean_unsigned_to_nat(200u);
v___x_1161_ = lean_nat_dec_lt(v_code_1157_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_inc(v_status_1155_);
v___y_1128_ = v_status_1155_;
v___y_1129_ = v___y_1151_;
v___y_1130_ = v___x_1156_;
v___y_1131_ = v_code_1157_;
v___y_1132_ = v_val_1153_;
goto v___jp_1127_;
}
else
{
v___y_1120_ = v___y_1151_;
v___y_1121_ = v_val_1153_;
goto v___jp_1119_;
}
}
}
}
v___jp_1162_:
{
if (lean_obj_tag(v___y_1163_) == 0)
{
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1165_);
v___y_1151_ = v___y_1164_;
v___y_1152_ = v___y_1173_;
v_val_1153_ = v___y_1166_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec_ref(v___y_1166_);
v___x_1181_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1181_, 0, v___y_1180_);
lean_ctor_set(v___x_1181_, 1, v___y_1176_);
lean_ctor_set(v___x_1181_, 2, v___y_1168_);
lean_ctor_set(v___x_1181_, 3, v___y_1163_);
lean_ctor_set(v___x_1181_, 4, v___y_1179_);
lean_ctor_set(v___x_1181_, 5, v___y_1174_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*6, v___y_1169_);
lean_ctor_set_uint8(v___x_1181_, sizeof(void*)*6 + 1, v___y_1170_);
v___x_1182_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1182_, 0, v___y_1167_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
lean_ctor_set(v___x_1182_, 2, v___y_1171_);
lean_ctor_set(v___x_1182_, 3, v___y_1172_);
lean_ctor_set(v___x_1182_, 4, v___y_1165_);
lean_ctor_set(v___x_1182_, 5, v___y_1177_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*6, v___y_1175_);
lean_ctor_set_uint8(v___x_1182_, sizeof(void*)*6 + 1, v___y_1178_);
v___y_1151_ = v___y_1164_;
v___y_1152_ = v___y_1173_;
v_val_1153_ = v___x_1182_;
goto v___jp_1150_;
}
}
v___jp_1183_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1199_, 0, v___y_1197_);
lean_ctor_set(v___x_1199_, 1, v___y_1198_);
lean_ctor_set(v___x_1199_, 2, v___y_1186_);
lean_ctor_set(v___x_1199_, 3, v___y_1192_);
lean_ctor_set(v___x_1199_, 4, v___y_1196_);
lean_ctor_set(v___x_1199_, 5, v___y_1193_);
lean_ctor_set_uint8(v___x_1199_, sizeof(void*)*6, v___y_1188_);
lean_ctor_set_uint8(v___x_1199_, sizeof(void*)*6 + 1, v___y_1189_);
v___x_1200_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_1200_, 0, v___y_1185_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
lean_ctor_set(v___x_1200_, 2, v___y_1190_);
lean_ctor_set(v___x_1200_, 3, v___y_1191_);
lean_ctor_set(v___x_1200_, 4, v___y_1184_);
lean_ctor_set(v___x_1200_, 5, v___y_1194_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*6, v___y_1187_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*6 + 1, v___y_1195_);
v___y_1002_ = v___x_1200_;
v_omitBody_1003_ = v___y_1189_;
goto v___jp_1001_;
}
v___jp_1201_:
{
uint8_t v___x_1218_; 
v___x_1218_ = l_ByteArray_isEmpty(v___y_1207_);
if (v___x_1218_ == 0)
{
lean_object* v_data_1219_; lean_object* v_size_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1230_; 
v_data_1219_ = lean_ctor_get(v___y_1212_, 0);
v_size_1220_ = lean_ctor_get(v___y_1212_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___y_1212_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1222_ = v___y_1212_;
v_isShared_1223_ = v_isSharedCheck_1230_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_size_1220_);
lean_inc(v_data_1219_);
lean_dec(v___y_1212_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1230_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
lean_inc_ref(v___y_1207_);
v___x_1224_ = lean_array_push(v_data_1219_, v___y_1207_);
v___x_1225_ = lean_byte_array_size(v___y_1207_);
lean_dec_ref(v___y_1207_);
v___x_1226_ = lean_nat_add(v_size_1220_, v___x_1225_);
lean_dec(v_size_1220_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 1, v___x_1226_);
lean_ctor_set(v___x_1222_, 0, v___x_1224_);
v___x_1228_ = v___x_1222_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
v___y_1184_ = v___y_1202_;
v___y_1185_ = v___y_1203_;
v___y_1186_ = v___y_1204_;
v___y_1187_ = v___y_1217_;
v___y_1188_ = v___y_1205_;
v___y_1189_ = v___y_1206_;
v___y_1190_ = v___y_1208_;
v___y_1191_ = v___y_1209_;
v___y_1192_ = v___y_1210_;
v___y_1193_ = v___y_1211_;
v___y_1194_ = v___y_1213_;
v___y_1195_ = v___y_1214_;
v___y_1196_ = v___y_1215_;
v___y_1197_ = v___y_1216_;
v___y_1198_ = v___x_1228_;
goto v___jp_1183_;
}
}
}
else
{
lean_dec_ref(v___y_1207_);
v___y_1184_ = v___y_1202_;
v___y_1185_ = v___y_1203_;
v___y_1186_ = v___y_1204_;
v___y_1187_ = v___y_1217_;
v___y_1188_ = v___y_1205_;
v___y_1189_ = v___y_1206_;
v___y_1190_ = v___y_1208_;
v___y_1191_ = v___y_1209_;
v___y_1192_ = v___y_1210_;
v___y_1193_ = v___y_1211_;
v___y_1194_ = v___y_1213_;
v___y_1195_ = v___y_1214_;
v___y_1196_ = v___y_1215_;
v___y_1197_ = v___y_1216_;
v___y_1198_ = v___y_1212_;
goto v___jp_1183_;
}
}
v___jp_1231_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1252_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__1);
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = lean_byte_array_size(v___y_1251_);
v___x_1255_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__2);
v___x_1256_ = lean_byte_array_copy_slice(v___x_1252_, v___x_1253_, v___y_1251_, v___x_1254_, v___x_1255_, v___y_1240_);
v___x_1257_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__3));
v___x_1258_ = l_Std_Http_Headers_fold___redArg(v___y_1248_, v___x_1256_, v___x_1257_);
lean_dec_ref(v___y_1248_);
v___x_1259_ = lean_byte_array_size(v___x_1258_);
v___x_1260_ = lean_byte_array_copy_slice(v___x_1252_, v___x_1253_, v___x_1258_, v___x_1259_, v___x_1255_, v___y_1240_);
if (v___y_1243_ == 0)
{
lean_dec_ref(v___y_1235_);
v___y_1202_ = v___y_1232_;
v___y_1203_ = v___y_1233_;
v___y_1204_ = v___y_1234_;
v___y_1205_ = v___y_1236_;
v___y_1206_ = v___y_1237_;
v___y_1207_ = v___x_1260_;
v___y_1208_ = v___y_1238_;
v___y_1209_ = v___y_1239_;
v___y_1210_ = v___y_1241_;
v___y_1211_ = v___y_1242_;
v___y_1212_ = v___y_1244_;
v___y_1213_ = v___y_1245_;
v___y_1214_ = v___y_1246_;
v___y_1215_ = v___y_1249_;
v___y_1216_ = v___y_1250_;
v___y_1217_ = v___y_1243_;
goto v___jp_1201_;
}
else
{
uint8_t v___x_1261_; 
v___x_1261_ = l_Std_Http_Protocol_H1_Message_Head_shouldKeepAlive(v___y_1247_, v___y_1235_);
lean_dec_ref(v___y_1235_);
v___y_1202_ = v___y_1232_;
v___y_1203_ = v___y_1233_;
v___y_1204_ = v___y_1234_;
v___y_1205_ = v___y_1236_;
v___y_1206_ = v___y_1237_;
v___y_1207_ = v___x_1260_;
v___y_1208_ = v___y_1238_;
v___y_1209_ = v___y_1239_;
v___y_1210_ = v___y_1241_;
v___y_1211_ = v___y_1242_;
v___y_1212_ = v___y_1244_;
v___y_1213_ = v___y_1245_;
v___y_1214_ = v___y_1246_;
v___y_1215_ = v___y_1249_;
v___y_1216_ = v___y_1250_;
v___y_1217_ = v___x_1261_;
goto v___jp_1201_;
}
}
v___jp_1262_:
{
lean_object* v_message_1281_; lean_object* v_status_1282_; lean_object* v_headers_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1312_; 
v_message_1281_ = l_Std_Http_Protocol_H1_Message_Head_setHeaders(v___y_1277_, v_line_996_, v___y_1280_);
v_status_1282_ = lean_ctor_get(v_message_1281_, 0);
v_headers_1283_ = lean_ctor_get(v_message_1281_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_message_1281_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1285_ = v_message_1281_;
v_isShared_1286_ = v_isSharedCheck_1312_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_headers_1283_);
lean_inc(v_status_1282_);
lean_dec(v_message_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1312_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
uint8_t v___x_1287_; lean_object* v_message_1289_; 
v___x_1287_ = 1;
lean_inc_ref(v_headers_1283_);
lean_inc(v_status_1282_);
if (v_isShared_1286_ == 0)
{
v_message_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_status_1282_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_headers_1283_);
v_message_1289_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; 
lean_ctor_set_uint8(v_message_1289_, sizeof(void*)*2, v___x_1287_);
v___x_1290_ = l_ByteArray_empty;
v___x_1291_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__5);
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__6);
v___x_1294_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__7);
v___x_1295_ = lean_byte_array_copy_slice(v___x_1291_, v___x_1292_, v___x_1290_, v___x_1293_, v___x_1294_, v___y_1270_);
v___x_1296_ = 32;
v___x_1297_ = lean_byte_array_push(v___x_1295_, v___x_1296_);
if (lean_obj_tag(v_status_1282_) == 4)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__9);
v___x_1299_ = lean_byte_array_size(v___x_1297_);
v___x_1300_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__10);
v___x_1301_ = lean_byte_array_copy_slice(v___x_1298_, v___x_1292_, v___x_1297_, v___x_1299_, v___x_1300_, v___y_1270_);
v___y_1232_ = v___y_1263_;
v___y_1233_ = v___y_1264_;
v___y_1234_ = v___y_1265_;
v___y_1235_ = v_message_1289_;
v___y_1236_ = v___y_1266_;
v___y_1237_ = v___y_1267_;
v___y_1238_ = v___y_1268_;
v___y_1239_ = v___y_1269_;
v___y_1240_ = v___y_1270_;
v___y_1241_ = v___y_1271_;
v___y_1242_ = v___y_1272_;
v___y_1243_ = v___y_1273_;
v___y_1244_ = v___y_1274_;
v___y_1245_ = v___y_1275_;
v___y_1246_ = v___y_1276_;
v___y_1247_ = v___y_1277_;
v___y_1248_ = v_headers_1283_;
v___y_1249_ = v___y_1278_;
v___y_1250_ = v___y_1279_;
v___y_1251_ = v___x_1301_;
goto v___jp_1231_;
}
else
{
uint16_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1302_ = l_Std_Http_Status_toCode(v_status_1282_);
v___x_1303_ = lean_uint16_to_nat(v___x_1302_);
v___x_1304_ = l_Std_Http_Internal_appendNat(v___x_1297_, v___x_1303_);
v___x_1305_ = lean_byte_array_push(v___x_1304_, v___x_1296_);
v___x_1306_ = l_Std_Http_Status_reasonPhrase(v_status_1282_);
lean_dec(v_status_1282_);
v___x_1307_ = lean_string_to_utf8(v___x_1306_);
v___x_1308_ = lean_byte_array_size(v___x_1305_);
v___x_1309_ = lean_byte_array_size(v___x_1307_);
v___x_1310_ = lean_byte_array_copy_slice(v___x_1307_, v___x_1292_, v___x_1305_, v___x_1308_, v___x_1309_, v___y_1270_);
lean_dec_ref(v___x_1307_);
v___y_1232_ = v___y_1263_;
v___y_1233_ = v___y_1264_;
v___y_1234_ = v___y_1265_;
v___y_1235_ = v_message_1289_;
v___y_1236_ = v___y_1266_;
v___y_1237_ = v___y_1267_;
v___y_1238_ = v___y_1268_;
v___y_1239_ = v___y_1269_;
v___y_1240_ = v___y_1270_;
v___y_1241_ = v___y_1271_;
v___y_1242_ = v___y_1272_;
v___y_1243_ = v___y_1273_;
v___y_1244_ = v___y_1274_;
v___y_1245_ = v___y_1275_;
v___y_1246_ = v___y_1276_;
v___y_1247_ = v___y_1277_;
v___y_1248_ = v_headers_1283_;
v___y_1249_ = v___y_1278_;
v___y_1250_ = v___y_1279_;
v___y_1251_ = v___x_1310_;
goto v___jp_1231_;
}
}
}
}
v___jp_1313_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = lean_array_get_size(v___y_1331_);
v___x_1334_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__20));
v___x_1335_ = lean_nat_dec_lt(v___x_1332_, v___x_1333_);
if (v___x_1335_ == 0)
{
v___y_1263_ = v___y_1314_;
v___y_1264_ = v___y_1315_;
v___y_1265_ = v___y_1316_;
v___y_1266_ = v___y_1317_;
v___y_1267_ = v___y_1318_;
v___y_1268_ = v___y_1319_;
v___y_1269_ = v___y_1320_;
v___y_1270_ = v___y_1321_;
v___y_1271_ = v___y_1322_;
v___y_1272_ = v___y_1323_;
v___y_1273_ = v___y_1324_;
v___y_1274_ = v___y_1325_;
v___y_1275_ = v___y_1326_;
v___y_1276_ = v___y_1327_;
v___y_1277_ = v___y_1328_;
v___y_1278_ = v___y_1329_;
v___y_1279_ = v___y_1330_;
v___y_1280_ = v___y_1331_;
goto v___jp_1262_;
}
else
{
lean_object* v___f_1336_; size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___f_1336_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__21, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__21_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__21);
v___x_1337_ = ((size_t)0ULL);
v___x_1338_ = lean_usize_of_nat(v___x_1333_);
lean_inc_ref(v___y_1331_);
v___x_1339_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1334_, v___f_1336_, v___y_1331_, v___x_1337_, v___x_1338_);
v___x_1340_ = lean_unbox(v___x_1339_);
lean_dec(v___x_1339_);
if (v___x_1340_ == 0)
{
v___y_1263_ = v___y_1314_;
v___y_1264_ = v___y_1315_;
v___y_1265_ = v___y_1316_;
v___y_1266_ = v___y_1317_;
v___y_1267_ = v___y_1318_;
v___y_1268_ = v___y_1319_;
v___y_1269_ = v___y_1320_;
v___y_1270_ = v___y_1321_;
v___y_1271_ = v___y_1322_;
v___y_1272_ = v___y_1323_;
v___y_1273_ = v___y_1324_;
v___y_1274_ = v___y_1325_;
v___y_1275_ = v___y_1326_;
v___y_1276_ = v___y_1327_;
v___y_1277_ = v___y_1328_;
v___y_1278_ = v___y_1329_;
v___y_1279_ = v___y_1330_;
v___y_1280_ = v___y_1331_;
goto v___jp_1262_;
}
else
{
lean_object* v___f_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___f_1341_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__22, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__22_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__22);
v___x_1342_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__23));
v___x_1343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1334_, v___f_1341_, v___y_1331_, v___x_1337_, v___x_1338_, v___x_1342_);
v___y_1263_ = v___y_1314_;
v___y_1264_ = v___y_1315_;
v___y_1265_ = v___y_1316_;
v___y_1266_ = v___y_1317_;
v___y_1267_ = v___y_1318_;
v___y_1268_ = v___y_1319_;
v___y_1269_ = v___y_1320_;
v___y_1270_ = v___y_1321_;
v___y_1271_ = v___y_1322_;
v___y_1272_ = v___y_1323_;
v___y_1273_ = v___y_1324_;
v___y_1274_ = v___y_1325_;
v___y_1275_ = v___y_1326_;
v___y_1276_ = v___y_1327_;
v___y_1277_ = v___y_1328_;
v___y_1278_ = v___y_1329_;
v___y_1279_ = v___y_1330_;
v___y_1280_ = v___x_1343_;
goto v___jp_1262_;
}
}
}
v___jp_1344_:
{
lean_object* v___x_1350_; 
lean_inc_ref(v___y_1347_);
v___x_1350_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_reconcileOutgoingFraming(v___y_1346_, v___y_1347_, v___y_1345_, v___y_1348_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v___x_1351_; 
lean_dec_ref(v_line_996_);
v___x_1351_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_rejectOutgoingFraming(v___y_1346_, v___y_1347_);
v___y_1016_ = v___x_1351_;
goto v___jp_1015_;
}
else
{
lean_object* v_val_1352_; 
lean_dec_ref(v___y_1347_);
v_val_1352_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_val_1352_);
lean_dec_ref_known(v___x_1350_, 1);
v___y_1151_ = v___y_1346_;
v___y_1152_ = v___y_1349_;
v_val_1153_ = v_val_1352_;
goto v___jp_1150_;
}
}
v___jp_1353_:
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = lean_unsigned_to_nat(204u);
v___x_1377_ = lean_nat_dec_eq(v___y_1361_, v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = lean_unsigned_to_nat(304u);
v___x_1379_ = lean_nat_dec_eq(v___y_1361_, v___x_1378_);
lean_dec(v___y_1361_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = lean_box(9);
v___x_1381_ = l_Std_Http_instBEqStatus_beq(v___y_1359_, v___x_1380_);
lean_dec(v___y_1359_);
if (v___x_1381_ == 0)
{
lean_object* v_messageHead_1382_; uint8_t v_method_1383_; uint8_t v___x_1384_; uint8_t v___x_1385_; 
v_messageHead_1382_ = lean_ctor_get(v___y_1360_, 2);
v_method_1383_ = lean_ctor_get_uint8(v_messageHead_1382_, sizeof(void*)*2);
v___x_1384_ = 9;
v___x_1385_ = l_Std_Http_instBEqMethod_beq(v_method_1383_, v___x_1384_);
if (v___x_1385_ == 0)
{
uint8_t v___x_1386_; uint8_t v___x_1387_; 
v___x_1386_ = 5;
v___x_1387_ = l_Std_Http_instBEqMethod_beq(v_method_1383_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1358_);
v___y_1345_ = v___y_1354_;
v___y_1346_ = v___y_1355_;
v___y_1347_ = v___y_1357_;
v___y_1348_ = v___y_1373_;
v___y_1349_ = v___y_1367_;
goto v___jp_1344_;
}
else
{
uint16_t v___x_1388_; uint8_t v___x_1389_; 
v___x_1388_ = 200;
v___x_1389_ = lean_uint16_dec_le(v___x_1388_, v___y_1356_);
if (v___x_1389_ == 0)
{
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1358_);
v___y_1345_ = v___y_1354_;
v___y_1346_ = v___y_1355_;
v___y_1347_ = v___y_1357_;
v___y_1348_ = v___y_1373_;
v___y_1349_ = v___y_1367_;
goto v___jp_1344_;
}
else
{
uint16_t v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = 300;
v___x_1391_ = lean_uint16_dec_lt(v___y_1356_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1358_);
v___y_1345_ = v___y_1354_;
v___y_1346_ = v___y_1355_;
v___y_1347_ = v___y_1357_;
v___y_1348_ = v___y_1373_;
v___y_1349_ = v___y_1367_;
goto v___jp_1344_;
}
else
{
v___y_1163_ = v___y_1354_;
v___y_1164_ = v___y_1355_;
v___y_1165_ = v___y_1358_;
v___y_1166_ = v___y_1357_;
v___y_1167_ = v___y_1360_;
v___y_1168_ = v___y_1362_;
v___y_1169_ = v___y_1363_;
v___y_1170_ = v___y_1364_;
v___y_1171_ = v___y_1365_;
v___y_1172_ = v___y_1366_;
v___y_1173_ = v___y_1367_;
v___y_1174_ = v___y_1368_;
v___y_1175_ = v___y_1370_;
v___y_1176_ = v___y_1369_;
v___y_1177_ = v___y_1371_;
v___y_1178_ = v___y_1372_;
v___y_1179_ = v___y_1374_;
v___y_1180_ = v___y_1375_;
goto v___jp_1162_;
}
}
}
}
else
{
v___y_1163_ = v___y_1354_;
v___y_1164_ = v___y_1355_;
v___y_1165_ = v___y_1358_;
v___y_1166_ = v___y_1357_;
v___y_1167_ = v___y_1360_;
v___y_1168_ = v___y_1362_;
v___y_1169_ = v___y_1363_;
v___y_1170_ = v___y_1364_;
v___y_1171_ = v___y_1365_;
v___y_1172_ = v___y_1366_;
v___y_1173_ = v___y_1367_;
v___y_1174_ = v___y_1368_;
v___y_1175_ = v___y_1370_;
v___y_1176_ = v___y_1369_;
v___y_1177_ = v___y_1371_;
v___y_1178_ = v___y_1372_;
v___y_1179_ = v___y_1374_;
v___y_1180_ = v___y_1375_;
goto v___jp_1162_;
}
}
else
{
v___y_1163_ = v___y_1354_;
v___y_1164_ = v___y_1355_;
v___y_1165_ = v___y_1358_;
v___y_1166_ = v___y_1357_;
v___y_1167_ = v___y_1360_;
v___y_1168_ = v___y_1362_;
v___y_1169_ = v___y_1363_;
v___y_1170_ = v___y_1364_;
v___y_1171_ = v___y_1365_;
v___y_1172_ = v___y_1366_;
v___y_1173_ = v___y_1367_;
v___y_1174_ = v___y_1368_;
v___y_1175_ = v___y_1370_;
v___y_1176_ = v___y_1369_;
v___y_1177_ = v___y_1371_;
v___y_1178_ = v___y_1372_;
v___y_1179_ = v___y_1374_;
v___y_1180_ = v___y_1375_;
goto v___jp_1162_;
}
}
else
{
lean_dec(v___y_1359_);
v___y_1163_ = v___y_1354_;
v___y_1164_ = v___y_1355_;
v___y_1165_ = v___y_1358_;
v___y_1166_ = v___y_1357_;
v___y_1167_ = v___y_1360_;
v___y_1168_ = v___y_1362_;
v___y_1169_ = v___y_1363_;
v___y_1170_ = v___y_1364_;
v___y_1171_ = v___y_1365_;
v___y_1172_ = v___y_1366_;
v___y_1173_ = v___y_1367_;
v___y_1174_ = v___y_1368_;
v___y_1175_ = v___y_1370_;
v___y_1176_ = v___y_1369_;
v___y_1177_ = v___y_1371_;
v___y_1178_ = v___y_1372_;
v___y_1179_ = v___y_1374_;
v___y_1180_ = v___y_1375_;
goto v___jp_1162_;
}
}
else
{
lean_dec(v___y_1361_);
lean_dec(v___y_1359_);
v___y_1163_ = v___y_1354_;
v___y_1164_ = v___y_1355_;
v___y_1165_ = v___y_1358_;
v___y_1166_ = v___y_1357_;
v___y_1167_ = v___y_1360_;
v___y_1168_ = v___y_1362_;
v___y_1169_ = v___y_1363_;
v___y_1170_ = v___y_1364_;
v___y_1171_ = v___y_1365_;
v___y_1172_ = v___y_1366_;
v___y_1173_ = v___y_1367_;
v___y_1174_ = v___y_1368_;
v___y_1175_ = v___y_1370_;
v___y_1176_ = v___y_1369_;
v___y_1177_ = v___y_1371_;
v___y_1178_ = v___y_1372_;
v___y_1179_ = v___y_1374_;
v___y_1180_ = v___y_1375_;
goto v___jp_1162_;
}
}
v___jp_1392_:
{
lean_object* v_status_1412_; uint16_t v___x_1413_; lean_object* v_code_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v_status_1412_ = lean_ctor_get(v_line_996_, 0);
v___x_1413_ = l_Std_Http_Status_toCode(v_status_1412_);
v_code_1414_ = lean_uint16_to_nat(v___x_1413_);
v___x_1415_ = lean_unsigned_to_nat(100u);
v___x_1416_ = lean_nat_dec_le(v___x_1415_, v_code_1414_);
if (v___x_1416_ == 0)
{
lean_inc(v_status_1412_);
v___y_1354_ = v___y_1411_;
v___y_1355_ = v___y_1393_;
v___y_1356_ = v___x_1413_;
v___y_1357_ = v___y_1394_;
v___y_1358_ = v___y_1395_;
v___y_1359_ = v_status_1412_;
v___y_1360_ = v___y_1396_;
v___y_1361_ = v_code_1414_;
v___y_1362_ = v___y_1397_;
v___y_1363_ = v___y_1398_;
v___y_1364_ = v___y_1399_;
v___y_1365_ = v___y_1400_;
v___y_1366_ = v___y_1401_;
v___y_1367_ = v___y_1402_;
v___y_1368_ = v___y_1403_;
v___y_1369_ = v___y_1404_;
v___y_1370_ = v___y_1405_;
v___y_1371_ = v___y_1406_;
v___y_1372_ = v___y_1407_;
v___y_1373_ = v___y_1408_;
v___y_1374_ = v___y_1409_;
v___y_1375_ = v___y_1410_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = lean_unsigned_to_nat(200u);
v___x_1418_ = lean_nat_dec_lt(v_code_1414_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_inc(v_status_1412_);
v___y_1354_ = v___y_1411_;
v___y_1355_ = v___y_1393_;
v___y_1356_ = v___x_1413_;
v___y_1357_ = v___y_1394_;
v___y_1358_ = v___y_1395_;
v___y_1359_ = v_status_1412_;
v___y_1360_ = v___y_1396_;
v___y_1361_ = v_code_1414_;
v___y_1362_ = v___y_1397_;
v___y_1363_ = v___y_1398_;
v___y_1364_ = v___y_1399_;
v___y_1365_ = v___y_1400_;
v___y_1366_ = v___y_1401_;
v___y_1367_ = v___y_1402_;
v___y_1368_ = v___y_1403_;
v___y_1369_ = v___y_1404_;
v___y_1370_ = v___y_1405_;
v___y_1371_ = v___y_1406_;
v___y_1372_ = v___y_1407_;
v___y_1373_ = v___y_1408_;
v___y_1374_ = v___y_1409_;
v___y_1375_ = v___y_1410_;
goto v___jp_1353_;
}
else
{
v___y_1163_ = v___y_1411_;
v___y_1164_ = v___y_1393_;
v___y_1165_ = v___y_1395_;
v___y_1166_ = v___y_1394_;
v___y_1167_ = v___y_1396_;
v___y_1168_ = v___y_1397_;
v___y_1169_ = v___y_1398_;
v___y_1170_ = v___y_1399_;
v___y_1171_ = v___y_1400_;
v___y_1172_ = v___y_1401_;
v___y_1173_ = v___y_1402_;
v___y_1174_ = v___y_1403_;
v___y_1175_ = v___y_1405_;
v___y_1176_ = v___y_1404_;
v___y_1177_ = v___y_1406_;
v___y_1178_ = v___y_1407_;
v___y_1179_ = v___y_1409_;
v___y_1180_ = v___y_1410_;
goto v___jp_1162_;
}
}
}
v___jp_1419_:
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_box(0);
v___y_1393_ = v___y_1420_;
v___y_1394_ = v___y_1421_;
v___y_1395_ = v___y_1422_;
v___y_1396_ = v___y_1423_;
v___y_1397_ = v___y_1424_;
v___y_1398_ = v___y_1425_;
v___y_1399_ = v___y_1426_;
v___y_1400_ = v___y_1427_;
v___y_1401_ = v___y_1428_;
v___y_1402_ = v___y_1429_;
v___y_1403_ = v___y_1430_;
v___y_1404_ = v___y_1431_;
v___y_1405_ = v___y_1432_;
v___y_1406_ = v___y_1433_;
v___y_1407_ = v___y_1434_;
v___y_1408_ = v___y_1437_;
v___y_1409_ = v___y_1435_;
v___y_1410_ = v___y_1436_;
v___y_1411_ = v___x_1438_;
goto v___jp_1392_;
}
v___jp_1439_:
{
uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1458_ = 1;
v___x_1459_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1458_, v_line_996_);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_array_get_size(v___x_1459_);
v___x_1462_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__20));
v___x_1463_ = lean_nat_dec_lt(v___x_1460_, v___x_1461_);
if (v___x_1463_ == 0)
{
lean_dec_ref(v___x_1459_);
lean_dec_ref(v___f_997_);
v___y_1420_ = v___y_1440_;
v___y_1421_ = v___y_1441_;
v___y_1422_ = v___y_1442_;
v___y_1423_ = v___y_1443_;
v___y_1424_ = v___y_1444_;
v___y_1425_ = v___y_1446_;
v___y_1426_ = v___y_1447_;
v___y_1427_ = v___y_1448_;
v___y_1428_ = v___y_1449_;
v___y_1429_ = v___y_1450_;
v___y_1430_ = v___y_1451_;
v___y_1431_ = v___y_1453_;
v___y_1432_ = v___y_1452_;
v___y_1433_ = v___y_1454_;
v___y_1434_ = v___y_1455_;
v___y_1435_ = v___y_1456_;
v___y_1436_ = v___y_1457_;
v___y_1437_ = v___x_1463_;
goto v___jp_1419_;
}
else
{
size_t v___x_1464_; size_t v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1464_ = ((size_t)0ULL);
v___x_1465_ = lean_usize_of_nat(v___x_1461_);
v___x_1466_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1462_, v___f_997_, v___x_1459_, v___x_1464_, v___x_1465_);
v___x_1467_ = lean_unbox(v___x_1466_);
if (v___x_1467_ == 0)
{
uint8_t v___x_1468_; 
v___x_1468_ = lean_unbox(v___x_1466_);
lean_dec(v___x_1466_);
v___y_1420_ = v___y_1440_;
v___y_1421_ = v___y_1441_;
v___y_1422_ = v___y_1442_;
v___y_1423_ = v___y_1443_;
v___y_1424_ = v___y_1444_;
v___y_1425_ = v___y_1446_;
v___y_1426_ = v___y_1447_;
v___y_1427_ = v___y_1448_;
v___y_1428_ = v___y_1449_;
v___y_1429_ = v___y_1450_;
v___y_1430_ = v___y_1451_;
v___y_1431_ = v___y_1453_;
v___y_1432_ = v___y_1452_;
v___y_1433_ = v___y_1454_;
v___y_1434_ = v___y_1455_;
v___y_1435_ = v___y_1456_;
v___y_1436_ = v___y_1457_;
v___y_1437_ = v___x_1468_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_1458_, v_line_996_, v___y_1445_);
v___x_1470_ = lean_unbox(v___x_1466_);
lean_dec(v___x_1466_);
v___y_1393_ = v___y_1440_;
v___y_1394_ = v___y_1441_;
v___y_1395_ = v___y_1442_;
v___y_1396_ = v___y_1443_;
v___y_1397_ = v___y_1444_;
v___y_1398_ = v___y_1446_;
v___y_1399_ = v___y_1447_;
v___y_1400_ = v___y_1448_;
v___y_1401_ = v___y_1449_;
v___y_1402_ = v___y_1450_;
v___y_1403_ = v___y_1451_;
v___y_1404_ = v___y_1453_;
v___y_1405_ = v___y_1452_;
v___y_1406_ = v___y_1454_;
v___y_1407_ = v___y_1455_;
v___y_1408_ = v___x_1470_;
v___y_1409_ = v___y_1456_;
v___y_1410_ = v___y_1457_;
v___y_1411_ = v___x_1469_;
goto v___jp_1392_;
}
}
}
v___jp_1471_:
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = lean_box(1);
v___x_1489_ = l_Std_Http_Protocol_H1_Writer_instBEqState_beq(v_state_1476_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_dec(v_date_1485_);
lean_dec(v_error_1484_);
lean_dec_ref(v_events_1483_);
lean_dec_ref(v_config_1482_);
lean_dec(v_userDataBytes_1481_);
lean_dec(v_messageHead_1478_);
lean_dec(v_knownSize_1477_);
lean_dec(v_state_1476_);
lean_dec_ref(v_outputData_1475_);
lean_dec_ref(v_userData_1474_);
lean_dec_ref(v_reader_1473_);
lean_dec_ref(v___f_997_);
lean_dec_ref(v_line_996_);
v___y_1002_ = v___y_1472_;
v_omitBody_1003_ = v_omitBody_1480_;
goto v___jp_1001_;
}
else
{
lean_object* v_status_1490_; uint8_t v___x_1491_; uint8_t v___x_1492_; uint16_t v___x_1493_; uint16_t v___x_1494_; uint8_t v___x_1495_; 
v_status_1490_ = lean_ctor_get(v_line_996_, 0);
v___x_1491_ = 0;
v___x_1492_ = 0;
v___x_1493_ = 100;
v___x_1494_ = l_Std_Http_Status_toCode(v_status_1490_);
v___x_1495_ = lean_uint16_dec_le(v___x_1493_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_dec(v_knownSize_1477_);
v___y_1440_ = v___x_1491_;
v___y_1441_ = v___y_1472_;
v___y_1442_ = v_error_1484_;
v___y_1443_ = v_reader_1473_;
v___y_1444_ = v_state_1476_;
v___y_1445_ = v___x_1495_;
v___y_1446_ = v_userClosedBody_1479_;
v___y_1447_ = v_omitBody_1480_;
v___y_1448_ = v_config_1482_;
v___y_1449_ = v_events_1483_;
v___y_1450_ = v___x_1492_;
v___y_1451_ = v_userDataBytes_1481_;
v___y_1452_ = v_keepAlive_1486_;
v___y_1453_ = v_outputData_1475_;
v___y_1454_ = v_date_1485_;
v___y_1455_ = v_pullBodyStalled_1487_;
v___y_1456_ = v_messageHead_1478_;
v___y_1457_ = v_userData_1474_;
goto v___jp_1439_;
}
else
{
uint16_t v___x_1496_; uint8_t v___x_1497_; 
v___x_1496_ = 200;
v___x_1497_ = lean_uint16_dec_lt(v___x_1494_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_dec(v_knownSize_1477_);
v___y_1440_ = v___x_1491_;
v___y_1441_ = v___y_1472_;
v___y_1442_ = v_error_1484_;
v___y_1443_ = v_reader_1473_;
v___y_1444_ = v_state_1476_;
v___y_1445_ = v___x_1497_;
v___y_1446_ = v_userClosedBody_1479_;
v___y_1447_ = v_omitBody_1480_;
v___y_1448_ = v_config_1482_;
v___y_1449_ = v_events_1483_;
v___y_1450_ = v___x_1492_;
v___y_1451_ = v_userDataBytes_1481_;
v___y_1452_ = v_keepAlive_1486_;
v___y_1453_ = v_outputData_1475_;
v___y_1454_ = v_date_1485_;
v___y_1455_ = v_pullBodyStalled_1487_;
v___y_1456_ = v_messageHead_1478_;
v___y_1457_ = v_userData_1474_;
goto v___jp_1439_;
}
else
{
lean_object* v_messageHead_1498_; uint8_t v___x_1499_; uint8_t v___x_1500_; uint8_t v___x_1501_; 
lean_dec_ref(v___f_997_);
v_messageHead_1498_ = lean_ctor_get(v_reader_1473_, 2);
v___x_1499_ = l_Std_Http_Protocol_H1_Message_Head_version(v___x_1491_, v_messageHead_1498_);
v___x_1500_ = 1;
v___x_1501_ = l_Std_Http_instBEqVersion_beq(v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_dec(v_date_1485_);
lean_dec(v_error_1484_);
lean_dec_ref(v_events_1483_);
lean_dec_ref(v_config_1482_);
lean_dec(v_userDataBytes_1481_);
lean_dec(v_messageHead_1478_);
lean_dec(v_knownSize_1477_);
lean_dec(v_state_1476_);
lean_dec_ref(v_outputData_1475_);
lean_dec_ref(v_userData_1474_);
lean_dec_ref(v_reader_1473_);
lean_dec_ref(v_line_996_);
v___y_1016_ = v___y_1472_;
goto v___jp_1015_;
}
else
{
uint8_t v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
lean_dec_ref(v___y_1472_);
v___x_1502_ = 1;
v___x_1503_ = l_Std_Http_Protocol_H1_Message_Head_headers(v___x_1502_, v_line_996_);
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = lean_array_get_size(v___x_1503_);
v___x_1506_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__20));
v___x_1507_ = lean_nat_dec_lt(v___x_1504_, v___x_1505_);
if (v___x_1507_ == 0)
{
v___y_1314_ = v_error_1484_;
v___y_1315_ = v_reader_1473_;
v___y_1316_ = v_state_1476_;
v___y_1317_ = v_userClosedBody_1479_;
v___y_1318_ = v_omitBody_1480_;
v___y_1319_ = v_config_1482_;
v___y_1320_ = v_events_1483_;
v___y_1321_ = v___x_1492_;
v___y_1322_ = v_knownSize_1477_;
v___y_1323_ = v_userDataBytes_1481_;
v___y_1324_ = v_keepAlive_1486_;
v___y_1325_ = v_outputData_1475_;
v___y_1326_ = v_date_1485_;
v___y_1327_ = v_pullBodyStalled_1487_;
v___y_1328_ = v___x_1502_;
v___y_1329_ = v_messageHead_1478_;
v___y_1330_ = v_userData_1474_;
v___y_1331_ = v___x_1503_;
goto v___jp_1313_;
}
else
{
lean_object* v___f_1508_; size_t v___x_1509_; size_t v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___f_1508_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__24, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__24_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__24);
v___x_1509_ = ((size_t)0ULL);
v___x_1510_ = lean_usize_of_nat(v___x_1505_);
lean_inc_ref(v___x_1503_);
v___x_1511_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_1506_, v___f_1508_, v___x_1503_, v___x_1509_, v___x_1510_);
v___x_1512_ = lean_unbox(v___x_1511_);
lean_dec(v___x_1511_);
if (v___x_1512_ == 0)
{
v___y_1314_ = v_error_1484_;
v___y_1315_ = v_reader_1473_;
v___y_1316_ = v_state_1476_;
v___y_1317_ = v_userClosedBody_1479_;
v___y_1318_ = v_omitBody_1480_;
v___y_1319_ = v_config_1482_;
v___y_1320_ = v_events_1483_;
v___y_1321_ = v___x_1492_;
v___y_1322_ = v_knownSize_1477_;
v___y_1323_ = v_userDataBytes_1481_;
v___y_1324_ = v_keepAlive_1486_;
v___y_1325_ = v_outputData_1475_;
v___y_1326_ = v_date_1485_;
v___y_1327_ = v_pullBodyStalled_1487_;
v___y_1328_ = v___x_1502_;
v___y_1329_ = v_messageHead_1478_;
v___y_1330_ = v_userData_1474_;
v___y_1331_ = v___x_1503_;
goto v___jp_1313_;
}
else
{
lean_object* v___f_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___f_1513_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__25, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__25_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__25);
v___x_1514_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__23));
v___x_1515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1506_, v___f_1513_, v___x_1503_, v___x_1509_, v___x_1510_, v___x_1514_);
v___y_1314_ = v_error_1484_;
v___y_1315_ = v_reader_1473_;
v___y_1316_ = v_state_1476_;
v___y_1317_ = v_userClosedBody_1479_;
v___y_1318_ = v_omitBody_1480_;
v___y_1319_ = v_config_1482_;
v___y_1320_ = v_events_1483_;
v___y_1321_ = v___x_1492_;
v___y_1322_ = v_knownSize_1477_;
v___y_1323_ = v_userDataBytes_1481_;
v___y_1324_ = v_keepAlive_1486_;
v___y_1325_ = v_outputData_1475_;
v___y_1326_ = v_date_1485_;
v___y_1327_ = v_pullBodyStalled_1487_;
v___y_1328_ = v___x_1502_;
v___y_1329_ = v_messageHead_1478_;
v___y_1330_ = v_userData_1474_;
v___y_1331_ = v___x_1515_;
goto v___jp_1313_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed(lean_object* v_body_1572_, lean_object* v_close_1573_, lean_object* v_isClosed_1574_, lean_object* v_line_1575_, lean_object* v___f_1576_, lean_object* v_machine_1577_, lean_object* v_x_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8(v_body_1572_, v_close_1573_, v_isClosed_1574_, v_line_1575_, v___f_1576_, v_machine_1577_, v_x_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(lean_object* v_inst_1582_, lean_object* v_machine_1583_, lean_object* v_res_1584_){
_start:
{
lean_object* v_close_1586_; lean_object* v_isClosed_1587_; lean_object* v_getKnownSize_1588_; lean_object* v_line_1589_; lean_object* v_body_1590_; lean_object* v___f_1591_; lean_object* v___f_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_close_1586_ = lean_ctor_get(v_inst_1582_, 1);
lean_inc_ref(v_close_1586_);
v_isClosed_1587_ = lean_ctor_get(v_inst_1582_, 2);
lean_inc_ref(v_isClosed_1587_);
v_getKnownSize_1588_ = lean_ctor_get(v_inst_1582_, 5);
lean_inc_ref(v_getKnownSize_1588_);
lean_dec_ref(v_inst_1582_);
v_line_1589_ = lean_ctor_get(v_res_1584_, 0);
lean_inc_ref(v_line_1589_);
v_body_1590_ = lean_ctor_get(v_res_1584_, 1);
lean_inc_n(v_body_1590_, 2);
lean_dec_ref(v_res_1584_);
v___f_1591_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___closed__0));
v___f_1592_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___boxed), 8, 6);
lean_closure_set(v___f_1592_, 0, v_body_1590_);
lean_closure_set(v___f_1592_, 1, v_close_1586_);
lean_closure_set(v___f_1592_, 2, v_isClosed_1587_);
lean_closure_set(v___f_1592_, 3, v_line_1589_);
lean_closure_set(v___f_1592_, 4, v___f_1591_);
lean_closure_set(v___f_1592_, 5, v_machine_1583_);
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = 0;
v___x_1595_ = lean_apply_2(v_getKnownSize_1588_, v_body_1590_, lean_box(0));
v___x_1596_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1593_, v___x_1594_, v___x_1595_, v___f_1592_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___boxed(lean_object* v_inst_1597_, lean_object* v_machine_1598_, lean_object* v_res_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1597_, v_machine_1598_, v_res_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(lean_object* v_00_u03b2_1602_, lean_object* v_inst_1603_, lean_object* v_machine_1604_, lean_object* v_res_1605_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_1603_, v_machine_1604_, v_res_1605_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___boxed(lean_object* v_00_u03b2_1608_, lean_object* v_inst_1609_, lean_object* v_machine_1610_, lean_object* v_res_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse(v_00_u03b2_1608_, v_inst_1609_, v_machine_1610_, v_res_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl___redArg(lean_object* v_x_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_obj_tag_nat(v_x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl___redArg___boxed(lean_object* v_x_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl___redArg(v_x_1616_);
lean_dec(v_x_1616_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl(lean_object* v_00_u03b2_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_obj_tag_nat(v_x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl___boxed(lean_object* v_00_u03b2_1621_, lean_object* v_x_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorIdx___impl(v_00_u03b2_1621_, v_x_1622_);
lean_dec(v_x_1622_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(lean_object* v_t_1624_, lean_object* v_k_1625_){
_start:
{
if (lean_obj_tag(v_t_1624_) == 0)
{
return v_k_1625_;
}
else
{
lean_object* v_task_1626_; lean_object* v___x_1627_; 
v_task_1626_ = lean_ctor_get(v_t_1624_, 0);
lean_inc_ref(v_task_1626_);
lean_dec(v_t_1624_);
v___x_1627_ = lean_apply_1(v_k_1625_, v_task_1626_);
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim(lean_object* v_00_u03b2_1628_, lean_object* v_motive_1629_, lean_object* v_ctorIdx_1630_, lean_object* v_t_1631_, lean_object* v_h_1632_, lean_object* v_k_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1631_, v_k_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___boxed(lean_object* v_00_u03b2_1635_, lean_object* v_motive_1636_, lean_object* v_ctorIdx_1637_, lean_object* v_t_1638_, lean_object* v_h_1639_, lean_object* v_k_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim(v_00_u03b2_1635_, v_motive_1636_, v_ctorIdx_1637_, v_t_1638_, v_h_1639_, v_k_1640_);
lean_dec(v_ctorIdx_1637_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_idle_elim___redArg(lean_object* v_t_1642_, lean_object* v_idle_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1642_, v_idle_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_idle_elim(lean_object* v_00_u03b2_1645_, lean_object* v_motive_1646_, lean_object* v_t_1647_, lean_object* v_h_1648_, lean_object* v_idle_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1647_, v_idle_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_running_elim___redArg(lean_object* v_t_1651_, lean_object* v_running_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1651_, v_running_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_running_elim(lean_object* v_00_u03b2_1654_, lean_object* v_motive_1655_, lean_object* v_t_1656_, lean_object* v_h_1657_, lean_object* v_running_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1656_, v_running_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandoned_elim___redArg(lean_object* v_t_1660_, lean_object* v_abandoned_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1660_, v_abandoned_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandoned_elim(lean_object* v_00_u03b2_1663_, lean_object* v_motive_1664_, lean_object* v_t_1665_, lean_object* v_h_1666_, lean_object* v_abandoned_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_ctorElim___redArg(v_t_1665_, v_abandoned_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg(lean_object* v_x_1669_){
_start:
{
if (lean_obj_tag(v_x_1669_) == 1)
{
uint8_t v___x_1670_; 
v___x_1670_ = 1;
return v___x_1670_;
}
else
{
uint8_t v___x_1671_; 
v___x_1671_ = 0;
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg___boxed(lean_object* v_x_1672_){
_start:
{
uint8_t v_res_1673_; lean_object* v_r_1674_; 
v_res_1673_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg(v_x_1672_);
lean_dec(v_x_1672_);
v_r_1674_ = lean_box(v_res_1673_);
return v_r_1674_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning(lean_object* v_00_u03b2_1675_, lean_object* v_x_1676_){
_start:
{
uint8_t v___x_1677_; 
v___x_1677_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg(v_x_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___boxed(lean_object* v_00_u03b2_1678_, lean_object* v_x_1679_){
_start:
{
uint8_t v_res_1680_; lean_object* v_r_1681_; 
v_res_1680_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning(v_00_u03b2_1678_, v_x_1679_);
lean_dec(v_x_1679_);
v_r_1681_ = lean_box(v_res_1680_);
return v_r_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon___redArg(lean_object* v_x_1682_){
_start:
{
if (lean_obj_tag(v_x_1682_) == 1)
{
lean_object* v_task_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_task_1683_ = lean_ctor_get(v_x_1682_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_x_1682_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v_x_1682_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_task_1683_);
lean_dec(v_x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set_tag(v___x_1685_, 2);
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_task_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
return v_x_1682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon(lean_object* v_00_u03b2_1691_, lean_object* v_x_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon___redArg(v_x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_task_x3f___redArg(lean_object* v_x_1694_){
_start:
{
switch(lean_obj_tag(v_x_1694_))
{
case 0:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_box(0);
return v___x_1695_;
}
case 1:
{
lean_object* v_task_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v_task_1696_ = lean_ctor_get(v_x_1694_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_x_1694_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v_x_1694_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_task_1696_);
lean_dec(v_x_1694_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_task_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
default: 
{
lean_object* v_task_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
v_task_1704_ = lean_ctor_get(v_x_1694_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_x_1694_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v_x_1694_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_task_1704_);
lean_dec(v_x_1694_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 1);
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_task_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_task_x3f(lean_object* v_00_u03b2_1712_, lean_object* v_x_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_task_x3f___redArg(v_x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0(lean_object* v_x_1715_, lean_object* v_x_1716_){
_start:
{
if (lean_obj_tag(v_x_1715_) == 0)
{
if (lean_obj_tag(v_x_1716_) == 0)
{
uint8_t v___x_1717_; 
v___x_1717_ = 1;
return v___x_1717_;
}
else
{
uint8_t v___x_1718_; 
v___x_1718_ = 0;
return v___x_1718_;
}
}
else
{
if (lean_obj_tag(v_x_1716_) == 0)
{
uint8_t v___x_1719_; 
v___x_1719_ = 0;
return v___x_1719_;
}
else
{
lean_object* v_val_1720_; lean_object* v_val_1721_; uint8_t v___x_1722_; 
v_val_1720_ = lean_ctor_get(v_x_1715_, 0);
v_val_1721_ = lean_ctor_get(v_x_1716_, 0);
v___x_1722_ = lean_int_dec_eq(v_val_1720_, v_val_1721_);
return v___x_1722_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0___boxed(lean_object* v_x_1723_, lean_object* v_x_1724_){
_start:
{
uint8_t v_res_1725_; lean_object* v_r_1726_; 
v_res_1725_ = l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0(v_x_1723_, v_x_1724_);
lean_dec(v_x_1724_);
lean_dec(v_x_1723_);
v_r_1726_ = lean_box(v_res_1725_);
return v_r_1726_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__2(lean_object* v_a_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_nat_to_int(v_a_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__3(lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Rat_ofInt(v_a_1729_);
return v___x_1730_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_unsigned_to_nat(1000000000u);
v___x_1732_ = lean_nat_to_int(v___x_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0(lean_object* v_tz_1733_, lean_object* v___x_1734_, lean_object* v_second_1735_, lean_object* v_nano_1736_, lean_object* v_x_1737_){
_start:
{
lean_object* v_offset_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v_nanos_1742_; lean_object* v___x_1743_; lean_object* v_nanos_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_offset_1738_ = lean_ctor_get(v_tz_1733_, 0);
v___x_1739_ = lean_nat_to_int(v___x_1734_);
v___x_1740_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___closed__0);
v___x_1741_ = lean_int_mul(v_second_1735_, v___x_1740_);
v_nanos_1742_ = lean_int_add(v___x_1741_, v_nano_1736_);
lean_dec(v___x_1741_);
v___x_1743_ = lean_int_mul(v_offset_1738_, v___x_1740_);
v_nanos_1744_ = lean_int_add(v___x_1743_, v___x_1739_);
lean_dec(v___x_1739_);
lean_dec(v___x_1743_);
v___x_1745_ = lean_int_add(v_nanos_1742_, v_nanos_1744_);
lean_dec(v_nanos_1744_);
lean_dec(v_nanos_1742_);
v___x_1746_ = l_Std_Time_Duration_ofNanoseconds(v___x_1745_);
lean_dec(v___x_1745_);
v___x_1747_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___boxed(lean_object* v_tz_1748_, lean_object* v___x_1749_, lean_object* v_second_1750_, lean_object* v_nano_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0(v_tz_1748_, v___x_1749_, v_second_1750_, v_nano_1751_, v_x_1752_);
lean_dec(v_nano_1751_);
lean_dec(v_second_1750_);
lean_dec_ref(v_tz_1748_);
return v_res_1753_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = lean_nat_to_int(v___x_1754_);
return v___x_1755_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__2));
v___x_1760_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__0);
v___x_1761_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_1760_, v___x_1759_, v___x_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(lean_object* v_config_1762_, lean_object* v_state_1763_){
_start:
{
uint8_t v_generateDate_1765_; 
v_generateDate_1765_ = lean_ctor_get_uint8(v_config_1762_, sizeof(void*)*28 + 1);
if (v_generateDate_1765_ == 0)
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v_state_1763_);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_get_current_time();
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1833_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1833_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1833_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_second_1772_; lean_object* v_nano_1773_; lean_object* v_machine_1774_; lean_object* v_requestStream_1775_; lean_object* v_timer_1776_; lean_object* v_response_1777_; lean_object* v_respStream_1778_; lean_object* v_inputWanted_1779_; lean_object* v_handler_1780_; lean_object* v_pendingHead_1781_; lean_object* v_dateSecond_1782_; uint8_t v_requestEnded_1783_; uint8_t v_aborted_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v_second_1772_ = lean_ctor_get(v_a_1768_, 0);
v_nano_1773_ = lean_ctor_get(v_a_1768_, 1);
v_machine_1774_ = lean_ctor_get(v_state_1763_, 0);
lean_inc_ref(v_machine_1774_);
v_requestStream_1775_ = lean_ctor_get(v_state_1763_, 1);
v_timer_1776_ = lean_ctor_get(v_state_1763_, 2);
v_response_1777_ = lean_ctor_get(v_state_1763_, 3);
v_respStream_1778_ = lean_ctor_get(v_state_1763_, 4);
v_inputWanted_1779_ = lean_ctor_get(v_state_1763_, 5);
v_handler_1780_ = lean_ctor_get(v_state_1763_, 6);
v_pendingHead_1781_ = lean_ctor_get(v_state_1763_, 7);
v_dateSecond_1782_ = lean_ctor_get(v_state_1763_, 8);
v_requestEnded_1783_ = lean_ctor_get_uint8(v_state_1763_, sizeof(void*)*9);
v_aborted_1784_ = lean_ctor_get_uint8(v_state_1763_, sizeof(void*)*9 + 1);
lean_inc(v_second_1772_);
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_second_1772_);
v___x_1786_ = l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__0(v_dateSecond_1782_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1820_; 
lean_inc(v_pendingHead_1781_);
lean_inc(v_handler_1780_);
lean_inc(v_inputWanted_1779_);
lean_inc(v_respStream_1778_);
lean_inc_ref(v_response_1777_);
lean_inc(v_timer_1776_);
lean_inc_ref(v_requestStream_1775_);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_state_1763_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; lean_object* v_unused_1822_; lean_object* v_unused_1823_; lean_object* v_unused_1824_; lean_object* v_unused_1825_; lean_object* v_unused_1826_; lean_object* v_unused_1827_; lean_object* v_unused_1828_; lean_object* v_unused_1829_; 
v_unused_1821_ = lean_ctor_get(v_state_1763_, 8);
lean_dec(v_unused_1821_);
v_unused_1822_ = lean_ctor_get(v_state_1763_, 7);
lean_dec(v_unused_1822_);
v_unused_1823_ = lean_ctor_get(v_state_1763_, 6);
lean_dec(v_unused_1823_);
v_unused_1824_ = lean_ctor_get(v_state_1763_, 5);
lean_dec(v_unused_1824_);
v_unused_1825_ = lean_ctor_get(v_state_1763_, 4);
lean_dec(v_unused_1825_);
v_unused_1826_ = lean_ctor_get(v_state_1763_, 3);
lean_dec(v_unused_1826_);
v_unused_1827_ = lean_ctor_get(v_state_1763_, 2);
lean_dec(v_unused_1827_);
v_unused_1828_ = lean_ctor_get(v_state_1763_, 1);
lean_dec(v_unused_1828_);
v_unused_1829_ = lean_ctor_get(v_state_1763_, 0);
lean_dec(v_unused_1829_);
v___x_1788_ = v_state_1763_;
v_isShared_1789_ = v_isSharedCheck_1820_;
goto v_resetjp_1787_;
}
else
{
lean_dec(v_state_1763_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1820_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v_reader_1792_; lean_object* v_writer_1793_; lean_object* v_config_1794_; lean_object* v_events_1795_; lean_object* v_error_1796_; uint8_t v_keepAlive_1797_; uint8_t v_pullBodyStalled_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1818_; 
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___closed__3);
v_reader_1792_ = lean_ctor_get(v_machine_1774_, 0);
v_writer_1793_ = lean_ctor_get(v_machine_1774_, 1);
v_config_1794_ = lean_ctor_get(v_machine_1774_, 2);
v_events_1795_ = lean_ctor_get(v_machine_1774_, 3);
v_error_1796_ = lean_ctor_get(v_machine_1774_, 4);
v_keepAlive_1797_ = lean_ctor_get_uint8(v_machine_1774_, sizeof(void*)*6);
v_pullBodyStalled_1798_ = lean_ctor_get_uint8(v_machine_1774_, sizeof(void*)*6 + 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_machine_1774_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v_machine_1774_, 5);
lean_dec(v_unused_1819_);
v___x_1800_ = v_machine_1774_;
v_isShared_1801_ = v_isSharedCheck_1818_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_error_1796_);
lean_inc(v_events_1795_);
lean_inc(v_config_1794_);
lean_inc(v_writer_1793_);
lean_inc(v_reader_1792_);
lean_dec(v_machine_1774_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1818_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_tz_1802_; lean_object* v___f_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
v_tz_1802_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_1791_, v_a_1768_);
lean_inc(v_nano_1773_);
lean_inc(v_second_1772_);
lean_inc_ref(v_tz_1802_);
v___f_1803_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1803_, 0, v_tz_1802_);
lean_closure_set(v___f_1803_, 1, v___x_1790_);
lean_closure_set(v___f_1803_, 2, v_second_1772_);
lean_closure_set(v___f_1803_, 3, v_nano_1773_);
v___x_1804_ = lean_mk_thunk(v___f_1803_);
v___x_1805_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v_a_1768_);
lean_ctor_set(v___x_1805_, 2, v___x_1791_);
lean_ctor_set(v___x_1805_, 3, v_tz_1802_);
v___x_1806_ = l_Std_Time_DateTime_toHTTPDateString(v___x_1805_);
v___x_1807_ = l_Std_Http_Header_Value_ofString_x21(v___x_1806_);
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 5, v___x_1808_);
v___x_1810_ = v___x_1800_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_reader_1792_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_writer_1793_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_config_1794_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_events_1795_);
lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_error_1796_);
lean_ctor_set(v_reuseFailAlloc_1817_, 5, v___x_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*6, v_keepAlive_1797_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*6 + 1, v_pullBodyStalled_1798_);
v___x_1810_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 8, v___x_1785_);
lean_ctor_set(v___x_1788_, 0, v___x_1810_);
v___x_1812_ = v___x_1788_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_requestStream_1775_);
lean_ctor_set(v_reuseFailAlloc_1816_, 2, v_timer_1776_);
lean_ctor_set(v_reuseFailAlloc_1816_, 3, v_response_1777_);
lean_ctor_set(v_reuseFailAlloc_1816_, 4, v_respStream_1778_);
lean_ctor_set(v_reuseFailAlloc_1816_, 5, v_inputWanted_1779_);
lean_ctor_set(v_reuseFailAlloc_1816_, 6, v_handler_1780_);
lean_ctor_set(v_reuseFailAlloc_1816_, 7, v_pendingHead_1781_);
lean_ctor_set(v_reuseFailAlloc_1816_, 8, v___x_1785_);
lean_ctor_set_uint8(v_reuseFailAlloc_1816_, sizeof(void*)*9, v_requestEnded_1783_);
lean_ctor_set_uint8(v_reuseFailAlloc_1816_, sizeof(void*)*9 + 1, v_aborted_1784_);
v___x_1812_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1812_);
v___x_1814_ = v___x_1770_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
}
else
{
lean_object* v___x_1831_; 
lean_dec_ref_known(v___x_1785_, 1);
lean_dec_ref(v_machine_1774_);
lean_dec(v_a_1768_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v_state_1763_);
v___x_1831_ = v___x_1770_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_state_1763_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v_state_1763_);
v_a_1834_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1767_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1767_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
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
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg___boxed(lean_object* v_config_1842_, lean_object* v_state_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(v_config_1842_, v_state_1843_);
lean_dec_ref(v_config_1842_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate(lean_object* v_00_u03b2_1846_, lean_object* v_config_1847_, lean_object* v_state_1848_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(v_config_1847_, v_state_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___boxed(lean_object* v_00_u03b2_1851_, lean_object* v_config_1852_, lean_object* v_state_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate(v_00_u03b2_1851_, v_config_1852_, v_state_1853_);
lean_dec_ref(v_config_1852_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate_spec__1(lean_object* v_a_1856_){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_nat_to_int(v_a_1856_);
v___x_1858_ = l_Rat_ofInt(v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0(lean_object* v_x_1859_, lean_object* v_x_1860_){
_start:
{
if (lean_obj_tag(v_x_1859_) == 0)
{
if (lean_obj_tag(v_x_1860_) == 0)
{
uint8_t v___x_1861_; 
v___x_1861_ = 1;
return v___x_1861_;
}
else
{
uint8_t v___x_1862_; 
v___x_1862_ = 0;
return v___x_1862_;
}
}
else
{
if (lean_obj_tag(v_x_1860_) == 0)
{
uint8_t v___x_1863_; 
v___x_1863_ = 0;
return v___x_1863_;
}
else
{
lean_object* v_val_1864_; lean_object* v_val_1865_; uint8_t v___x_1866_; 
v_val_1864_ = lean_ctor_get(v_x_1859_, 0);
v_val_1865_ = lean_ctor_get(v_x_1860_, 0);
v___x_1866_ = l_Std_Http_Body_instBEqLength_beq(v_val_1864_, v_val_1865_);
return v___x_1866_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0___boxed(lean_object* v_x_1867_, lean_object* v_x_1868_){
_start:
{
uint8_t v_res_1869_; lean_object* v_r_1870_; 
v_res_1869_ = l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0(v_x_1867_, v_x_1868_);
lean_dec(v_x_1868_);
lean_dec(v_x_1867_);
v_r_1870_ = lean_box(v_res_1869_);
return v_r_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__0(lean_object* v___y_1871_){
_start:
{
if (lean_obj_tag(v___y_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
v_a_1872_ = lean_ctor_get(v___y_1871_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___y_1871_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___y_1871_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___y_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1888_; 
v_a_1880_ = lean_ctor_get(v___y_1871_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___y_1871_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1882_ = v___y_1871_;
v_isShared_1883_ = v_isSharedCheck_1888_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___y_1871_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1888_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v_fst_1884_; lean_object* v___x_1886_; 
v_fst_1884_ = lean_ctor_get(v_a_1880_, 0);
lean_inc(v_fst_1884_);
lean_dec(v_a_1880_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v_fst_1884_);
v___x_1886_ = v___x_1882_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_fst_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1(lean_object* v_mutex_1889_, lean_object* v_x_1890_){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_io_basemutex_unlock(v_mutex_1889_);
v___x_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1___boxed(lean_object* v_mutex_1895_, lean_object* v_x_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1(v_mutex_1895_, v_x_1896_);
lean_dec(v_x_1896_);
lean_dec(v_mutex_1895_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2(lean_object* v_k_1899_, lean_object* v_ref_1900_, lean_object* v_x_1901_){
_start:
{
if (lean_obj_tag(v_x_1901_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_ref_1900_);
lean_dec_ref(v_k_1899_);
v_a_1903_ = lean_ctor_get(v_x_1901_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_x_1901_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1905_ = v_x_1901_;
v_isShared_1906_ = v_isSharedCheck_1911_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v_x_1901_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1911_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
return v___x_1909_;
}
}
}
else
{
lean_object* v___x_1912_; 
lean_dec_ref_known(v_x_1901_, 1);
v___x_1912_ = lean_apply_2(v_k_1899_, v_ref_1900_, lean_box(0));
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2___boxed(lean_object* v_k_1913_, lean_object* v_ref_1914_, lean_object* v_x_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2(v_k_1913_, v_ref_1914_, v_x_1915_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3(lean_object* v_mutex_1918_, lean_object* v___f_1919_){
_start:
{
lean_object* v___x_1921_; uint8_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1921_ = lean_unsigned_to_nat(0u);
v___x_1922_ = 0;
v___x_1923_ = lean_io_basemutex_lock(v_mutex_1918_);
v___x_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
v___x_1926_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1921_, v___x_1922_, v___x_1925_, v___f_1919_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3___boxed(lean_object* v_mutex_1927_, lean_object* v___f_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3(v_mutex_1927_, v___f_1928_);
lean_dec(v_mutex_1927_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(lean_object* v_mutex_1932_, lean_object* v_k_1933_){
_start:
{
lean_object* v_ref_1935_; lean_object* v_mutex_1936_; lean_object* v___f_1937_; lean_object* v___f_1938_; lean_object* v___f_1939_; lean_object* v___f_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___y_1945_; 
v_ref_1935_ = lean_ctor_get(v_mutex_1932_, 0);
lean_inc(v_ref_1935_);
v_mutex_1936_ = lean_ctor_get(v_mutex_1932_, 1);
lean_inc_n(v_mutex_1936_, 2);
lean_dec_ref(v_mutex_1932_);
v___f_1937_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___closed__0));
v___f_1938_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_1938_, 0, v_mutex_1936_);
v___f_1939_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1939_, 0, v_k_1933_);
lean_closure_set(v___f_1939_, 1, v_ref_1935_);
v___f_1940_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_1940_, 0, v_mutex_1936_);
lean_closure_set(v___f_1940_, 1, v___f_1939_);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = 0;
v___x_1943_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_1940_, v___f_1938_, v___x_1941_, v___x_1942_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1947_; 
v_a_1947_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1943_, 1);
if (lean_obj_tag(v_a_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v_a_1948_ = lean_ctor_get(v_a_1947_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_a_1947_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v_a_1947_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v_a_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
v___y_1945_ = v___x_1953_;
goto v___jp_1944_;
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1964_; 
v_a_1956_ = lean_ctor_get(v_a_1947_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_a_1947_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1958_ = v_a_1947_;
v_isShared_1959_ = v_isSharedCheck_1964_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v_a_1947_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1964_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v_fst_1960_; lean_object* v___x_1962_; 
v_fst_1960_ = lean_ctor_get(v_a_1956_, 0);
lean_inc(v_fst_1960_);
lean_dec(v_a_1956_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v_fst_1960_);
v___x_1962_ = v___x_1958_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_fst_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
v___y_1945_ = v___x_1962_;
goto v___jp_1944_;
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_a_1965_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1967_ = v___x_1943_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1943_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = lean_task_map(v___f_1937_, v_a_1965_, v___x_1941_, v___x_1942_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v___x_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
v___jp_1944_:
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1946_, 0, v___y_1945_);
return v___x_1946_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg___boxed(lean_object* v_mutex_1974_, lean_object* v_k_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(v_mutex_1974_, v_k_1975_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1(lean_object* v_00_u03b1_1978_, lean_object* v_00_u03b2_1979_, lean_object* v_mutex_1980_, lean_object* v_k_1981_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(v_mutex_1980_, v_k_1981_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___boxed(lean_object* v_00_u03b1_1984_, lean_object* v_00_u03b2_1985_, lean_object* v_mutex_1986_, lean_object* v_k_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1(v_00_u03b1_1984_, v_00_u03b2_1985_, v_mutex_1986_, v_k_1987_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0(lean_object* v_x_1990_){
_start:
{
if (lean_obj_tag(v_x_1990_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2000_; 
v_a_1992_ = lean_ctor_get(v_x_1990_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_x_1990_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1994_ = v_x_1990_;
v_isShared_1995_ = v_isSharedCheck_2000_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v_x_1990_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2000_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
return v___x_1998_;
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2010_; 
v_a_2001_ = lean_ctor_get(v_x_1990_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_x_1990_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2003_ = v_x_1990_;
v_isShared_2004_ = v_isSharedCheck_2010_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v_x_1990_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2010_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v_knownSize_2005_; lean_object* v___x_2007_; 
v_knownSize_2005_ = lean_ctor_get(v_a_2001_, 4);
lean_inc(v_knownSize_2005_);
lean_dec(v_a_2001_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v_knownSize_2005_);
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_knownSize_2005_);
v___x_2007_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
return v___x_2008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0___boxed(lean_object* v_x_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__0(v_x_2011_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1(lean_object* v_reason_2018_, lean_object* v_requestStream_2019_, lean_object* v_x_2020_){
_start:
{
if (lean_obj_tag(v_x_2020_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2030_; 
lean_dec_ref(v_requestStream_2019_);
lean_dec_ref(v_reason_2018_);
v_a_2022_ = lean_ctor_get(v_x_2020_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_x_2020_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2024_ = v_x_2020_;
v_isShared_2025_ = v_isSharedCheck_2030_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v_x_2020_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2030_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
return v___x_2028_;
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_a_2031_ = lean_ctor_get(v_x_2020_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v_x_2020_, 1);
v___x_2032_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___closed__1));
v___x_2033_ = l_instBEqOption_beq___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__0(v_a_2031_, v___x_2032_);
lean_dec(v_a_2031_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2034_, 0, v_reason_2018_);
v___x_2035_ = l_Std_Http_Body_Stream_closeWithError(v_requestStream_2019_, v___x_2034_);
return v___x_2035_;
}
else
{
lean_object* v___x_2036_; 
lean_dec_ref(v_reason_2018_);
v___x_2036_ = l_Std_Http_Body_Stream_close(v_requestStream_2019_);
return v___x_2036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___boxed(lean_object* v_reason_2037_, lean_object* v_requestStream_2038_, lean_object* v_x_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1(v_reason_2037_, v_requestStream_2038_, v_x_2039_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2(lean_object* v___x_2042_, uint8_t v_a_2043_, lean_object* v___f_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2047_ = lean_st_ref_get(v___y_2045_);
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
v___x_2050_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2042_, v_a_2043_, v___x_2049_, v___f_2044_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___boxed(lean_object* v___x_2051_, lean_object* v_a_2052_, lean_object* v___f_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
uint8_t v_a_2006__boxed_2056_; lean_object* v_res_2057_; 
v_a_2006__boxed_2056_ = lean_unbox(v_a_2052_);
v_res_2057_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2(v___x_2051_, v_a_2006__boxed_2056_, v___f_2053_, v___y_2054_);
lean_dec(v___y_2054_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3(lean_object* v___f_2058_, lean_object* v_requestStream_2059_, lean_object* v___f_2060_, lean_object* v_x_2061_){
_start:
{
if (lean_obj_tag(v_x_2061_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v___f_2060_);
lean_dec_ref(v_requestStream_2059_);
lean_dec_ref(v___f_2058_);
v_a_2063_ = lean_ctor_get(v_x_2061_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_x_2061_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2065_ = v_x_2061_;
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v_x_2061_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
}
else
{
lean_object* v_a_2072_; uint8_t v___x_2073_; 
v_a_2072_ = lean_ctor_get(v_x_2061_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v_x_2061_, 1);
v___x_2073_ = lean_unbox(v_a_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; lean_object* v___f_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2074_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_2072_);
v___f_2075_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__2___boxed), 5, 3);
lean_closure_set(v___f_2075_, 0, v___x_2074_);
lean_closure_set(v___f_2075_, 1, v_a_2072_);
lean_closure_set(v___f_2075_, 2, v___f_2058_);
v___x_2076_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(v_requestStream_2059_, v___f_2075_);
v___x_2077_ = lean_unbox(v_a_2072_);
lean_dec(v_a_2072_);
v___x_2078_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2074_, v___x_2077_, v___x_2076_, v___f_2060_);
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; 
lean_dec(v_a_2072_);
lean_dec_ref(v___f_2060_);
lean_dec_ref(v_requestStream_2059_);
lean_dec_ref(v___f_2058_);
v___x_2079_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_2079_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3___boxed(lean_object* v___f_2080_, lean_object* v_requestStream_2081_, lean_object* v___f_2082_, lean_object* v_x_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3(v___f_2080_, v_requestStream_2081_, v___f_2082_, v_x_2083_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4(uint8_t v___x_2086_, lean_object* v_x_2087_){
_start:
{
uint8_t v___y_2090_; 
if (lean_obj_tag(v_x_2087_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2102_; 
v_a_2094_ = lean_ctor_get(v_x_2087_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_x_2087_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2096_ = v_x_2087_;
v_isShared_2097_ = v_isSharedCheck_2102_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v_x_2087_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2102_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; 
v___x_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
return v___x_2100_;
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v_ended_2104_; 
v_a_2103_ = lean_ctor_get(v_x_2087_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v_x_2087_, 1);
v_ended_2104_ = lean_ctor_get(v_a_2103_, 3);
lean_inc(v_ended_2104_);
lean_dec(v_a_2103_);
if (lean_obj_tag(v_ended_2104_) == 0)
{
v___y_2090_ = v___x_2086_;
goto v___jp_2089_;
}
else
{
uint8_t v___x_2105_; 
lean_dec_ref_known(v_ended_2104_, 1);
v___x_2105_ = 1;
v___y_2090_ = v___x_2105_;
goto v___jp_2089_;
}
}
v___jp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_box(v___y_2090_);
v___x_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4___boxed(lean_object* v___x_2106_, lean_object* v_x_2107_, lean_object* v___y_2108_){
_start:
{
uint8_t v___x_2080__boxed_2109_; lean_object* v_res_2110_; 
v___x_2080__boxed_2109_ = lean_unbox(v___x_2106_);
v_res_2110_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__4(v___x_2080__boxed_2109_, v_x_2107_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5(lean_object* v___x_2111_, uint8_t v___x_2112_, lean_object* v___f_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2116_ = lean_st_ref_get(v___y_2114_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
v___x_2119_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2111_, v___x_2112_, v___x_2118_, v___f_2113_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5___boxed(lean_object* v___x_2120_, lean_object* v___x_2121_, lean_object* v___f_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v___x_2123__boxed_2125_; lean_object* v_res_2126_; 
v___x_2123__boxed_2125_ = lean_unbox(v___x_2121_);
v_res_2126_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__5(v___x_2120_, v___x_2123__boxed_2125_, v___f_2122_, v___y_2123_);
lean_dec(v___y_2123_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(lean_object* v_state_2136_, lean_object* v_reason_2137_){
_start:
{
lean_object* v_requestStream_2139_; lean_object* v___f_2140_; lean_object* v___f_2141_; lean_object* v___f_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___f_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_requestStream_2139_ = lean_ctor_get(v_state_2136_, 1);
lean_inc_ref_n(v_requestStream_2139_, 3);
lean_dec_ref(v_state_2136_);
v___f_2140_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__0));
v___f_2141_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2141_, 0, v_reason_2137_);
lean_closure_set(v___f_2141_, 1, v_requestStream_2139_);
v___f_2142_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2142_, 0, v___f_2140_);
lean_closure_set(v___f_2142_, 1, v_requestStream_2139_);
lean_closure_set(v___f_2142_, 2, v___f_2141_);
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = 0;
v___f_2145_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___closed__2));
v___x_2146_ = l_Std_Mutex_atomically___at___00__private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream_spec__1___redArg(v_requestStream_2139_, v___f_2145_);
v___x_2147_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2143_, v___x_2144_, v___x_2146_, v___f_2142_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg___boxed(lean_object* v_state_2148_, lean_object* v_reason_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v_state_2148_, v_reason_2149_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream(lean_object* v_00_u03b2_2152_, lean_object* v_state_2153_, lean_object* v_reason_2154_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v_state_2153_, v_reason_2154_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___boxed(lean_object* v_00_u03b2_2157_, lean_object* v_state_2158_, lean_object* v_reason_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream(v_00_u03b2_2157_, v_state_2158_, v_reason_2159_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(lean_object* v___x_2162_, lean_object* v_x_2163_){
_start:
{
if (lean_obj_tag(v_x_2163_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref(v___x_2162_);
v_a_2165_ = lean_ctor_get(v_x_2163_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_x_2163_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2167_ = v_x_2163_;
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v_x_2163_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2173_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
return v___x_2171_;
}
}
}
else
{
lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2182_; 
v_isSharedCheck_2182_ = !lean_is_exclusive(v_x_2163_);
if (v_isSharedCheck_2182_ == 0)
{
lean_object* v_unused_2183_; 
v_unused_2183_ = lean_ctor_get(v_x_2163_, 0);
lean_dec(v_unused_2183_);
v___x_2175_ = v_x_2163_;
v_isShared_2176_ = v_isSharedCheck_2182_;
goto v_resetjp_2174_;
}
else
{
lean_dec(v_x_2163_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2182_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2162_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2177_);
v___x_2179_ = v___x_2175_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
return v___x_2180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed(lean_object* v___x_2184_, lean_object* v_x_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0(v___x_2184_, v_x_2185_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(lean_object* v___x_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; lean_object* v_pendingProducer_2192_; lean_object* v_pendingConsumer_2193_; lean_object* v_interestWaiter_2194_; lean_object* v_ended_2195_; lean_object* v_pendingIncomplete_2196_; uint8_t v_closeAfterProducer_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2206_; 
v___x_2191_ = lean_st_ref_take(v___y_2189_);
v_pendingProducer_2192_ = lean_ctor_get(v___x_2191_, 0);
v_pendingConsumer_2193_ = lean_ctor_get(v___x_2191_, 1);
v_interestWaiter_2194_ = lean_ctor_get(v___x_2191_, 2);
v_ended_2195_ = lean_ctor_get(v___x_2191_, 3);
v_pendingIncomplete_2196_ = lean_ctor_get(v___x_2191_, 5);
v_closeAfterProducer_2197_ = lean_ctor_get_uint8(v___x_2191_, sizeof(void*)*6);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v___x_2191_, 4);
lean_dec(v_unused_2207_);
v___x_2199_ = v___x_2191_;
v_isShared_2200_ = v_isSharedCheck_2206_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_pendingIncomplete_2196_);
lean_inc(v_ended_2195_);
lean_inc(v_interestWaiter_2194_);
lean_inc(v_pendingConsumer_2193_);
lean_inc(v_pendingProducer_2192_);
lean_dec(v___x_2191_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2206_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 4, v___x_2188_);
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_pendingProducer_2192_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_pendingConsumer_2193_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_interestWaiter_2194_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_ended_2195_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2205_, 5, v_pendingIncomplete_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*6, v_closeAfterProducer_2197_);
v___x_2202_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_st_ref_put(v___y_2189_, v___x_2202_);
v___x_2204_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_2204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed(lean_object* v___x_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1(v___x_2208_, v___y_2209_);
lean_dec(v___y_2209_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(lean_object* v_machine_2212_, lean_object* v_requestStream_2213_, lean_object* v_timer_2214_, lean_object* v_response_2215_, lean_object* v_respStream_2216_, lean_object* v_handler_2217_, lean_object* v_dateSecond_2218_, uint8_t v_requestEnded_2219_, uint8_t v_aborted_2220_, lean_object* v_x_2221_){
_start:
{
if (lean_obj_tag(v_x_2221_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_dateSecond_2218_);
lean_dec(v_handler_2217_);
lean_dec(v_respStream_2216_);
lean_dec_ref(v_response_2215_);
lean_dec(v_timer_2214_);
lean_dec_ref(v_requestStream_2213_);
lean_dec_ref(v_machine_2212_);
v_a_2223_ = lean_ctor_get(v_x_2221_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_x_2221_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2225_ = v_x_2221_;
v_isShared_2226_ = v_isSharedCheck_2231_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v_x_2221_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2231_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
return v___x_2229_;
}
}
}
else
{
lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2242_; 
v_isSharedCheck_2242_ = !lean_is_exclusive(v_x_2221_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; 
v_unused_2243_ = lean_ctor_get(v_x_2221_, 0);
lean_dec(v_unused_2243_);
v___x_2233_ = v_x_2221_;
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
else
{
lean_dec(v_x_2221_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2235_ = lean_box(0);
v___x_2236_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2236_, 0, v_machine_2212_);
lean_ctor_set(v___x_2236_, 1, v_requestStream_2213_);
lean_ctor_set(v___x_2236_, 2, v_timer_2214_);
lean_ctor_set(v___x_2236_, 3, v_response_2215_);
lean_ctor_set(v___x_2236_, 4, v_respStream_2216_);
lean_ctor_set(v___x_2236_, 5, v___x_2235_);
lean_ctor_set(v___x_2236_, 6, v_handler_2217_);
lean_ctor_set(v___x_2236_, 7, v___x_2235_);
lean_ctor_set(v___x_2236_, 8, v_dateSecond_2218_);
lean_ctor_set_uint8(v___x_2236_, sizeof(void*)*9, v_requestEnded_2219_);
lean_ctor_set_uint8(v___x_2236_, sizeof(void*)*9 + 1, v_aborted_2220_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2237_);
v___x_2239_ = v___x_2233_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
return v___x_2240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed(lean_object* v_machine_2244_, lean_object* v_requestStream_2245_, lean_object* v_timer_2246_, lean_object* v_response_2247_, lean_object* v_respStream_2248_, lean_object* v_handler_2249_, lean_object* v_dateSecond_2250_, lean_object* v_requestEnded_2251_, lean_object* v_aborted_2252_, lean_object* v_x_2253_, lean_object* v___y_2254_){
_start:
{
uint8_t v_requestEnded_boxed_2255_; uint8_t v_aborted_boxed_2256_; lean_object* v_res_2257_; 
v_requestEnded_boxed_2255_ = lean_unbox(v_requestEnded_2251_);
v_aborted_boxed_2256_ = lean_unbox(v_aborted_2252_);
v_res_2257_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2(v_machine_2244_, v_requestStream_2245_, v_timer_2246_, v_response_2247_, v_respStream_2248_, v_handler_2249_, v_dateSecond_2250_, v_requestEnded_boxed_2255_, v_aborted_boxed_2256_, v_x_2253_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(lean_object* v___y_2273_, lean_object* v___f_2274_, lean_object* v_err_2275_, lean_object* v_____r_2276_){
_start:
{
lean_object* v___x_2278_; lean_object* v___y_2280_; 
v___x_2278_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__0));
switch(lean_obj_tag(v_err_2275_))
{
case 0:
{
lean_object* v___x_2286_; 
v___x_2286_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1));
v___y_2280_ = v___x_2286_;
goto v___jp_2279_;
}
case 1:
{
lean_object* v___x_2287_; 
v___x_2287_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__2));
v___y_2280_ = v___x_2287_;
goto v___jp_2279_;
}
case 2:
{
lean_object* v___x_2288_; 
v___x_2288_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__3));
v___y_2280_ = v___x_2288_;
goto v___jp_2279_;
}
case 3:
{
lean_object* v___x_2289_; 
v___x_2289_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__4));
v___y_2280_ = v___x_2289_;
goto v___jp_2279_;
}
case 4:
{
lean_object* v___x_2290_; 
v___x_2290_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__5));
v___y_2280_ = v___x_2290_;
goto v___jp_2279_;
}
case 5:
{
lean_object* v___x_2291_; 
v___x_2291_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__6));
v___y_2280_ = v___x_2291_;
goto v___jp_2279_;
}
case 6:
{
lean_object* v___x_2292_; 
v___x_2292_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__7));
v___y_2280_ = v___x_2292_;
goto v___jp_2279_;
}
case 7:
{
lean_object* v___x_2293_; 
v___x_2293_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__8));
v___y_2280_ = v___x_2293_;
goto v___jp_2279_;
}
case 8:
{
lean_object* v___x_2294_; 
v___x_2294_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__9));
v___y_2280_ = v___x_2294_;
goto v___jp_2279_;
}
case 9:
{
lean_object* v___x_2295_; 
v___x_2295_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__10));
v___y_2280_ = v___x_2295_;
goto v___jp_2279_;
}
case 10:
{
lean_object* v___x_2296_; 
v___x_2296_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__11));
v___y_2280_ = v___x_2296_;
goto v___jp_2279_;
}
case 11:
{
lean_object* v___x_2297_; 
v___x_2297_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__12));
v___y_2280_ = v___x_2297_;
goto v___jp_2279_;
}
case 12:
{
lean_object* v___x_2298_; 
v___x_2298_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__13));
v___y_2280_ = v___x_2298_;
goto v___jp_2279_;
}
default: 
{
lean_object* v_message_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v_message_2299_ = lean_ctor_get(v_err_2275_, 0);
v___x_2300_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__14));
v___x_2301_ = lean_string_append(v___x_2300_, v_message_2299_);
v___y_2280_ = v___x_2301_;
goto v___jp_2279_;
}
}
v___jp_2279_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2281_ = lean_string_append(v___x_2278_, v___y_2280_);
lean_dec_ref(v___y_2280_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = 0;
v___x_2284_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v___y_2273_, v___x_2281_);
v___x_2285_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2282_, v___x_2283_, v___x_2284_, v___f_2274_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed(lean_object* v___y_2302_, lean_object* v___f_2303_, lean_object* v_err_2304_, lean_object* v_____r_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___y_2302_, v___f_2303_, v_err_2304_, v_____r_2305_);
lean_dec(v_err_2304_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(lean_object* v___f_2308_, lean_object* v_x_2309_){
_start:
{
if (lean_obj_tag(v_x_2309_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v___f_2308_);
v_a_2311_ = lean_ctor_get(v_x_2309_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_x_2309_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2313_ = v_x_2309_;
v_isShared_2314_ = v_isSharedCheck_2319_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v_x_2309_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2319_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
return v___x_2317_;
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2321_; 
v_a_2320_ = lean_ctor_get(v_x_2309_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v_x_2309_, 1);
v___x_2321_ = lean_apply_2(v___f_2308_, v_a_2320_, lean_box(0));
return v___x_2321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed(lean_object* v___f_2322_, lean_object* v_x_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4(v___f_2322_, v_x_2323_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(lean_object* v___y_2326_, lean_object* v_x_2327_){
_start:
{
if (lean_obj_tag(v_x_2327_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2337_; 
lean_dec_ref(v___y_2326_);
v_a_2329_ = lean_ctor_get(v_x_2327_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_x_2327_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2331_ = v_x_2327_;
v_isShared_2332_ = v_isSharedCheck_2337_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v_x_2327_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2337_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2335_; 
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
return v___x_2335_;
}
}
}
else
{
lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2364_; 
v_isSharedCheck_2364_ = !lean_is_exclusive(v_x_2327_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; 
v_unused_2365_ = lean_ctor_get(v_x_2327_, 0);
lean_dec(v_unused_2365_);
v___x_2339_ = v_x_2327_;
v_isShared_2340_ = v_isSharedCheck_2364_;
goto v_resetjp_2338_;
}
else
{
lean_dec(v_x_2327_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2364_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v_machine_2341_; lean_object* v_requestStream_2342_; lean_object* v_timer_2343_; lean_object* v_response_2344_; lean_object* v_respStream_2345_; lean_object* v_inputWanted_2346_; lean_object* v_handler_2347_; lean_object* v_pendingHead_2348_; lean_object* v_dateSecond_2349_; uint8_t v_aborted_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2363_; 
v_machine_2341_ = lean_ctor_get(v___y_2326_, 0);
v_requestStream_2342_ = lean_ctor_get(v___y_2326_, 1);
v_timer_2343_ = lean_ctor_get(v___y_2326_, 2);
v_response_2344_ = lean_ctor_get(v___y_2326_, 3);
v_respStream_2345_ = lean_ctor_get(v___y_2326_, 4);
v_inputWanted_2346_ = lean_ctor_get(v___y_2326_, 5);
v_handler_2347_ = lean_ctor_get(v___y_2326_, 6);
v_pendingHead_2348_ = lean_ctor_get(v___y_2326_, 7);
v_dateSecond_2349_ = lean_ctor_get(v___y_2326_, 8);
v_aborted_2350_ = lean_ctor_get_uint8(v___y_2326_, sizeof(void*)*9 + 1);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___y_2326_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2352_ = v___y_2326_;
v_isShared_2353_ = v_isSharedCheck_2363_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_dateSecond_2349_);
lean_inc(v_pendingHead_2348_);
lean_inc(v_handler_2347_);
lean_inc(v_inputWanted_2346_);
lean_inc(v_respStream_2345_);
lean_inc(v_response_2344_);
lean_inc(v_timer_2343_);
lean_inc(v_requestStream_2342_);
lean_inc(v_machine_2341_);
lean_dec(v___y_2326_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2363_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
uint8_t v___x_2354_; lean_object* v___x_2356_; 
v___x_2354_ = 1;
if (v_isShared_2353_ == 0)
{
v___x_2356_ = v___x_2352_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_machine_2341_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_requestStream_2342_);
lean_ctor_set(v_reuseFailAlloc_2362_, 2, v_timer_2343_);
lean_ctor_set(v_reuseFailAlloc_2362_, 3, v_response_2344_);
lean_ctor_set(v_reuseFailAlloc_2362_, 4, v_respStream_2345_);
lean_ctor_set(v_reuseFailAlloc_2362_, 5, v_inputWanted_2346_);
lean_ctor_set(v_reuseFailAlloc_2362_, 6, v_handler_2347_);
lean_ctor_set(v_reuseFailAlloc_2362_, 7, v_pendingHead_2348_);
lean_ctor_set(v_reuseFailAlloc_2362_, 8, v_dateSecond_2349_);
lean_ctor_set_uint8(v_reuseFailAlloc_2362_, sizeof(void*)*9 + 1, v_aborted_2350_);
v___x_2356_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*9, v___x_2354_);
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2357_);
v___x_2359_ = v___x_2339_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed(lean_object* v___y_2366_, lean_object* v_x_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5(v___y_2366_, v_x_2367_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(lean_object* v_handler_2370_, lean_object* v_machine_2371_, lean_object* v_a_2372_, lean_object* v_timer_2373_, lean_object* v_inputWanted_2374_, lean_object* v_pendingHead_2375_, lean_object* v_dateSecond_2376_, uint8_t v_requestEnded_2377_, uint8_t v_aborted_2378_, lean_object* v_x_2379_){
_start:
{
if (lean_obj_tag(v_x_2379_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2389_; 
lean_dec(v_dateSecond_2376_);
lean_dec(v_pendingHead_2375_);
lean_dec(v_inputWanted_2374_);
lean_dec(v_timer_2373_);
lean_dec_ref(v_a_2372_);
lean_dec_ref(v_machine_2371_);
lean_dec(v_handler_2370_);
v_a_2381_ = lean_ctor_get(v_x_2379_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_x_2379_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2383_ = v_x_2379_;
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v_x_2379_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
return v___x_2387_;
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2402_; 
v_a_2390_ = lean_ctor_get(v_x_2379_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_x_2379_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2392_ = v_x_2379_;
v_isShared_2393_ = v_isSharedCheck_2402_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v_x_2379_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2402_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
v___x_2394_ = lean_box(0);
v___x_2395_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon___redArg(v_handler_2370_);
v___x_2396_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2396_, 0, v_machine_2371_);
lean_ctor_set(v___x_2396_, 1, v_a_2372_);
lean_ctor_set(v___x_2396_, 2, v_timer_2373_);
lean_ctor_set(v___x_2396_, 3, v_a_2390_);
lean_ctor_set(v___x_2396_, 4, v___x_2394_);
lean_ctor_set(v___x_2396_, 5, v_inputWanted_2374_);
lean_ctor_set(v___x_2396_, 6, v___x_2395_);
lean_ctor_set(v___x_2396_, 7, v_pendingHead_2375_);
lean_ctor_set(v___x_2396_, 8, v_dateSecond_2376_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*9, v_requestEnded_2377_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*9 + 1, v_aborted_2378_);
v___x_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2397_);
v___x_2399_ = v___x_2392_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed(lean_object* v_handler_2403_, lean_object* v_machine_2404_, lean_object* v_a_2405_, lean_object* v_timer_2406_, lean_object* v_inputWanted_2407_, lean_object* v_pendingHead_2408_, lean_object* v_dateSecond_2409_, lean_object* v_requestEnded_2410_, lean_object* v_aborted_2411_, lean_object* v_x_2412_, lean_object* v___y_2413_){
_start:
{
uint8_t v_requestEnded_boxed_2414_; uint8_t v_aborted_boxed_2415_; lean_object* v_res_2416_; 
v_requestEnded_boxed_2414_ = lean_unbox(v_requestEnded_2410_);
v_aborted_boxed_2415_ = lean_unbox(v_aborted_2411_);
v_res_2416_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6(v_handler_2403_, v_machine_2404_, v_a_2405_, v_timer_2406_, v_inputWanted_2407_, v_pendingHead_2408_, v_dateSecond_2409_, v_requestEnded_boxed_2414_, v_aborted_boxed_2415_, v_x_2412_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(lean_object* v_handler_2417_, lean_object* v_machine_2418_, lean_object* v_a_2419_, lean_object* v_inputWanted_2420_, lean_object* v_pendingHead_2421_, lean_object* v_dateSecond_2422_, uint8_t v_requestEnded_2423_, uint8_t v_aborted_2424_, lean_object* v_timer_2425_){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___f_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2427_ = lean_box(v_requestEnded_2423_);
v___x_2428_ = lean_box(v_aborted_2424_);
v___f_2429_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__6___boxed), 11, 9);
lean_closure_set(v___f_2429_, 0, v_handler_2417_);
lean_closure_set(v___f_2429_, 1, v_machine_2418_);
lean_closure_set(v___f_2429_, 2, v_a_2419_);
lean_closure_set(v___f_2429_, 3, v_timer_2425_);
lean_closure_set(v___f_2429_, 4, v_inputWanted_2420_);
lean_closure_set(v___f_2429_, 5, v_pendingHead_2421_);
lean_closure_set(v___f_2429_, 6, v_dateSecond_2422_);
lean_closure_set(v___f_2429_, 7, v___x_2427_);
lean_closure_set(v___f_2429_, 8, v___x_2428_);
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_unsigned_to_nat(0u);
v___x_2432_ = 0;
v___x_2433_ = l_Std_CloseableChannel_new___redArg(v___x_2430_);
v___x_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
v___x_2436_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2431_, v___x_2432_, v___x_2435_, v___f_2429_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed(lean_object* v_handler_2437_, lean_object* v_machine_2438_, lean_object* v_a_2439_, lean_object* v_inputWanted_2440_, lean_object* v_pendingHead_2441_, lean_object* v_dateSecond_2442_, lean_object* v_requestEnded_2443_, lean_object* v_aborted_2444_, lean_object* v_timer_2445_, lean_object* v___y_2446_){
_start:
{
uint8_t v_requestEnded_boxed_2447_; uint8_t v_aborted_boxed_2448_; lean_object* v_res_2449_; 
v_requestEnded_boxed_2447_ = lean_unbox(v_requestEnded_2443_);
v_aborted_boxed_2448_ = lean_unbox(v_aborted_2444_);
v_res_2449_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7(v_handler_2437_, v_machine_2438_, v_a_2439_, v_inputWanted_2440_, v_pendingHead_2441_, v_dateSecond_2442_, v_requestEnded_boxed_2447_, v_aborted_boxed_2448_, v_timer_2445_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(lean_object* v___f_2450_, lean_object* v_x_2451_){
_start:
{
if (lean_obj_tag(v_x_2451_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2461_; 
lean_dec_ref(v___f_2450_);
v_a_2453_ = lean_ctor_get(v_x_2451_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_x_2451_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2455_ = v_x_2451_;
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v_x_2451_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2461_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
return v___x_2459_;
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2463_; 
v_a_2462_ = lean_ctor_get(v_x_2451_, 0);
lean_inc(v_a_2462_);
lean_dec_ref_known(v_x_2451_, 1);
v___x_2463_ = lean_apply_2(v___f_2450_, v_a_2462_, lean_box(0));
return v___x_2463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed(lean_object* v___f_2464_, lean_object* v_x_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8(v___f_2464_, v_x_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(lean_object* v_config_2468_, lean_object* v___f_2469_, lean_object* v_x_2470_){
_start:
{
if (lean_obj_tag(v_x_2470_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v___f_2469_);
v_a_2472_ = lean_ctor_get(v_x_2470_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_x_2470_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2474_ = v_x_2470_;
v_isShared_2475_ = v_isSharedCheck_2480_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v_x_2470_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2480_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
return v___x_2478_;
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2496_; 
v_a_2481_ = lean_ctor_get(v_x_2470_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_x_2470_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2483_ = v_x_2470_;
v_isShared_2484_ = v_isSharedCheck_2496_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v_x_2470_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2496_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v_headerTimeout_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; lean_object* v___x_2492_; 
v_headerTimeout_2485_ = lean_ctor_get(v_config_2468_, 6);
v___x_2486_ = l_Int_toNat(v_headerTimeout_2485_);
v___x_2487_ = lean_nat_add(v_a_2481_, v___x_2486_);
lean_dec(v___x_2486_);
lean_dec(v_a_2481_);
v___x_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
v___x_2489_ = lean_unsigned_to_nat(0u);
v___x_2490_ = 0;
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v___x_2488_);
v___x_2492_ = v___x_2483_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2488_);
v___x_2492_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
v___x_2494_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2489_, v___x_2490_, v___x_2493_, v___f_2469_);
return v___x_2494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed(lean_object* v_config_2497_, lean_object* v___f_2498_, lean_object* v_x_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10(v_config_2497_, v___f_2498_, v_x_2499_);
lean_dec_ref(v_config_2497_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(lean_object* v___y_2506_, lean_object* v_config_2507_, lean_object* v_x_2508_){
_start:
{
if (lean_obj_tag(v_x_2508_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2518_; 
lean_dec_ref(v_config_2507_);
lean_dec_ref(v___y_2506_);
v_a_2510_ = lean_ctor_get(v_x_2508_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v_x_2508_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2512_ = v_x_2508_;
v_isShared_2513_ = v_isSharedCheck_2518_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v_x_2508_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2518_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
lean_object* v___x_2516_; 
v___x_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
return v___x_2516_;
}
}
}
else
{
lean_object* v_machine_2519_; lean_object* v_reader_2520_; lean_object* v_input_2521_; lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2553_; 
v_machine_2519_ = lean_ctor_get(v___y_2506_, 0);
lean_inc_ref(v_machine_2519_);
v_reader_2520_ = lean_ctor_get(v_machine_2519_, 0);
v_input_2521_ = lean_ctor_get(v_reader_2520_, 1);
v_a_2522_ = lean_ctor_get(v_x_2508_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_x_2508_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2524_ = v_x_2508_;
v_isShared_2525_ = v_isSharedCheck_2553_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v_x_2508_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2553_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v_inputWanted_2526_; lean_object* v_handler_2527_; lean_object* v_pendingHead_2528_; lean_object* v_dateSecond_2529_; uint8_t v_requestEnded_2530_; uint8_t v_aborted_2531_; lean_object* v_array_2532_; lean_object* v_idx_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___f_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v_inputWanted_2526_ = lean_ctor_get(v___y_2506_, 5);
lean_inc(v_inputWanted_2526_);
v_handler_2527_ = lean_ctor_get(v___y_2506_, 6);
lean_inc(v_handler_2527_);
v_pendingHead_2528_ = lean_ctor_get(v___y_2506_, 7);
lean_inc(v_pendingHead_2528_);
v_dateSecond_2529_ = lean_ctor_get(v___y_2506_, 8);
lean_inc(v_dateSecond_2529_);
v_requestEnded_2530_ = lean_ctor_get_uint8(v___y_2506_, sizeof(void*)*9);
v_aborted_2531_ = lean_ctor_get_uint8(v___y_2506_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2506_);
v_array_2532_ = lean_ctor_get(v_input_2521_, 0);
lean_inc_ref(v_array_2532_);
v_idx_2533_ = lean_ctor_get(v_input_2521_, 1);
lean_inc(v_idx_2533_);
v___x_2534_ = lean_box(v_requestEnded_2530_);
v___x_2535_ = lean_box(v_aborted_2531_);
v___f_2536_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_2536_, 0, v_handler_2527_);
lean_closure_set(v___f_2536_, 1, v_machine_2519_);
lean_closure_set(v___f_2536_, 2, v_a_2522_);
lean_closure_set(v___f_2536_, 3, v_inputWanted_2526_);
lean_closure_set(v___f_2536_, 4, v_pendingHead_2528_);
lean_closure_set(v___f_2536_, 5, v_dateSecond_2529_);
lean_closure_set(v___f_2536_, 6, v___x_2534_);
lean_closure_set(v___f_2536_, 7, v___x_2535_);
v___x_2537_ = lean_unsigned_to_nat(0u);
v___x_2538_ = lean_byte_array_size(v_array_2532_);
lean_dec_ref(v_array_2532_);
v___x_2539_ = lean_nat_sub(v___x_2538_, v_idx_2533_);
lean_dec(v_idx_2533_);
v___x_2540_ = lean_nat_dec_lt(v___x_2537_, v___x_2539_);
lean_dec(v___x_2539_);
if (v___x_2540_ == 0)
{
lean_object* v___f_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_del_object(v___x_2524_);
lean_dec_ref(v_config_2507_);
v___f_2541_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_2541_, 0, v___f_2536_);
v___x_2542_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___closed__1));
v___x_2543_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2537_, v___x_2540_, v___x_2542_, v___f_2541_);
return v___x_2543_;
}
else
{
lean_object* v___f_2544_; lean_object* v___f_2545_; uint8_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
v___f_2544_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__8___boxed), 3, 1);
lean_closure_set(v___f_2544_, 0, v___f_2536_);
v___f_2545_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__10___boxed), 4, 2);
lean_closure_set(v___f_2545_, 0, v_config_2507_);
lean_closure_set(v___f_2545_, 1, v___f_2544_);
v___x_2546_ = 0;
v___x_2547_ = lean_io_mono_ms_now();
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2547_);
v___x_2549_ = v___x_2524_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
v___x_2551_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2537_, v___x_2546_, v___x_2550_, v___f_2545_);
return v___x_2551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed(lean_object* v___y_2554_, lean_object* v_config_2555_, lean_object* v_x_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9(v___y_2554_, v_config_2555_, v_x_2556_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(lean_object* v___f_2559_, lean_object* v_____r_2560_){
_start:
{
lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2562_ = lean_unsigned_to_nat(0u);
v___x_2563_ = 0;
v___x_2564_ = l_Std_Http_Body_mkStream();
v___x_2565_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2562_, v___x_2563_, v___x_2564_, v___f_2559_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed(lean_object* v___f_2566_, lean_object* v_____r_2567_, lean_object* v___y_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11(v___f_2566_, v_____r_2567_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(lean_object* v_close_2570_, lean_object* v_val_2571_, lean_object* v___f_2572_, lean_object* v___f_2573_, lean_object* v_x_2574_){
_start:
{
if (lean_obj_tag(v_x_2574_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2584_; 
lean_dec_ref(v___f_2573_);
lean_dec_ref(v___f_2572_);
lean_dec(v_val_2571_);
lean_dec_ref(v_close_2570_);
v_a_2576_ = lean_ctor_get(v_x_2574_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_x_2574_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2578_ = v_x_2574_;
v_isShared_2579_ = v_isSharedCheck_2584_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v_x_2574_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2584_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
return v___x_2582_;
}
}
}
else
{
lean_object* v_a_2585_; uint8_t v___x_2586_; 
v_a_2585_ = lean_ctor_get(v_x_2574_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v_x_2574_, 1);
v___x_2586_ = lean_unbox(v_a_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; lean_object* v___x_2590_; 
lean_dec_ref(v___f_2573_);
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = lean_apply_2(v_close_2570_, v_val_2571_, lean_box(0));
v___x_2589_ = lean_unbox(v_a_2585_);
lean_dec(v_a_2585_);
v___x_2590_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2587_, v___x_2589_, v___x_2588_, v___f_2572_);
return v___x_2590_;
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec(v_a_2585_);
lean_dec_ref(v___f_2572_);
lean_dec(v_val_2571_);
lean_dec_ref(v_close_2570_);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_apply_2(v___f_2573_, v___x_2591_, lean_box(0));
return v___x_2592_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed(lean_object* v_close_2593_, lean_object* v_val_2594_, lean_object* v___f_2595_, lean_object* v___f_2596_, lean_object* v_x_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13(v_close_2593_, v_val_2594_, v___f_2595_, v___f_2596_, v_x_2597_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(lean_object* v___y_2600_, lean_object* v_inst_2601_, lean_object* v___f_2602_, lean_object* v___f_2603_, lean_object* v_x_2604_){
_start:
{
if (lean_obj_tag(v_x_2604_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref(v___f_2603_);
lean_dec_ref(v___f_2602_);
lean_dec_ref(v_inst_2601_);
lean_dec_ref(v___y_2600_);
v_a_2606_ = lean_ctor_get(v_x_2604_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_x_2604_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2608_ = v_x_2604_;
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v_x_2604_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
return v___x_2612_;
}
}
}
else
{
lean_object* v_respStream_2615_; 
lean_dec_ref_known(v_x_2604_, 1);
v_respStream_2615_ = lean_ctor_get(v___y_2600_, 4);
lean_inc(v_respStream_2615_);
lean_dec_ref(v___y_2600_);
if (lean_obj_tag(v_respStream_2615_) == 1)
{
lean_object* v_val_2616_; lean_object* v_close_2617_; lean_object* v_isClosed_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v_val_2616_ = lean_ctor_get(v_respStream_2615_, 0);
lean_inc_n(v_val_2616_, 2);
lean_dec_ref_known(v_respStream_2615_, 1);
v_close_2617_ = lean_ctor_get(v_inst_2601_, 1);
lean_inc_ref(v_close_2617_);
v_isClosed_2618_ = lean_ctor_get(v_inst_2601_, 2);
lean_inc_ref(v_isClosed_2618_);
lean_dec_ref(v_inst_2601_);
v___f_2619_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__13___boxed), 6, 4);
lean_closure_set(v___f_2619_, 0, v_close_2617_);
lean_closure_set(v___f_2619_, 1, v_val_2616_);
lean_closure_set(v___f_2619_, 2, v___f_2602_);
lean_closure_set(v___f_2619_, 3, v___f_2603_);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = 0;
v___x_2622_ = lean_apply_2(v_isClosed_2618_, v_val_2616_, lean_box(0));
v___x_2623_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2620_, v___x_2621_, v___x_2622_, v___f_2619_);
return v___x_2623_;
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
lean_dec(v_respStream_2615_);
lean_dec_ref(v___f_2602_);
lean_dec_ref(v_inst_2601_);
v___x_2624_ = lean_box(0);
v___x_2625_ = lean_apply_2(v___f_2603_, v___x_2624_, lean_box(0));
return v___x_2625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed(lean_object* v___y_2626_, lean_object* v_inst_2627_, lean_object* v___f_2628_, lean_object* v___f_2629_, lean_object* v_x_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12(v___y_2626_, v_inst_2627_, v___f_2628_, v___f_2629_, v_x_2630_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(lean_object* v_requestStream_2633_, lean_object* v_timer_2634_, lean_object* v_response_2635_, lean_object* v_respStream_2636_, lean_object* v_inputWanted_2637_, lean_object* v_handler_2638_, lean_object* v_pendingHead_2639_, lean_object* v_dateSecond_2640_, uint8_t v_requestEnded_2641_, uint8_t v_aborted_2642_, lean_object* v_x_2643_){
_start:
{
if (lean_obj_tag(v_x_2643_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_dateSecond_2640_);
lean_dec(v_pendingHead_2639_);
lean_dec(v_handler_2638_);
lean_dec(v_inputWanted_2637_);
lean_dec(v_respStream_2636_);
lean_dec_ref(v_response_2635_);
lean_dec(v_timer_2634_);
lean_dec_ref(v_requestStream_2633_);
v_a_2645_ = lean_ctor_get(v_x_2643_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_x_2643_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2647_ = v_x_2643_;
v_isShared_2648_ = v_isSharedCheck_2653_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v_x_2643_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2653_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
return v___x_2651_;
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2675_; 
v_a_2654_ = lean_ctor_get(v_x_2643_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_x_2643_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2656_ = v_x_2643_;
v_isShared_2657_ = v_isSharedCheck_2675_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v_x_2643_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2675_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_snd_2658_; uint8_t v___x_2659_; 
v_snd_2658_ = lean_ctor_get(v_a_2654_, 1);
v___x_2659_ = lean_unbox(v_snd_2658_);
if (v___x_2659_ == 0)
{
lean_object* v_fst_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v_fst_2660_ = lean_ctor_get(v_a_2654_, 0);
lean_inc(v_fst_2660_);
lean_dec(v_a_2654_);
v___x_2661_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2661_, 0, v_fst_2660_);
lean_ctor_set(v___x_2661_, 1, v_requestStream_2633_);
lean_ctor_set(v___x_2661_, 2, v_timer_2634_);
lean_ctor_set(v___x_2661_, 3, v_response_2635_);
lean_ctor_set(v___x_2661_, 4, v_respStream_2636_);
lean_ctor_set(v___x_2661_, 5, v_inputWanted_2637_);
lean_ctor_set(v___x_2661_, 6, v_handler_2638_);
lean_ctor_set(v___x_2661_, 7, v_pendingHead_2639_);
lean_ctor_set(v___x_2661_, 8, v_dateSecond_2640_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*9, v_requestEnded_2641_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*9 + 1, v_aborted_2642_);
v___x_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2662_);
v___x_2664_ = v___x_2656_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
return v___x_2665_;
}
}
else
{
lean_object* v_fst_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
lean_dec(v_pendingHead_2639_);
v_fst_2667_ = lean_ctor_get(v_a_2654_, 0);
lean_inc(v_fst_2667_);
lean_dec(v_a_2654_);
v___x_2668_ = lean_box(0);
v___x_2669_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2669_, 0, v_fst_2667_);
lean_ctor_set(v___x_2669_, 1, v_requestStream_2633_);
lean_ctor_set(v___x_2669_, 2, v_timer_2634_);
lean_ctor_set(v___x_2669_, 3, v_response_2635_);
lean_ctor_set(v___x_2669_, 4, v_respStream_2636_);
lean_ctor_set(v___x_2669_, 5, v_inputWanted_2637_);
lean_ctor_set(v___x_2669_, 6, v_handler_2638_);
lean_ctor_set(v___x_2669_, 7, v___x_2668_);
lean_ctor_set(v___x_2669_, 8, v_dateSecond_2640_);
lean_ctor_set_uint8(v___x_2669_, sizeof(void*)*9, v_requestEnded_2641_);
lean_ctor_set_uint8(v___x_2669_, sizeof(void*)*9 + 1, v_aborted_2642_);
v___x_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2670_);
v___x_2672_ = v___x_2656_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
return v___x_2673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed(lean_object* v_requestStream_2676_, lean_object* v_timer_2677_, lean_object* v_response_2678_, lean_object* v_respStream_2679_, lean_object* v_inputWanted_2680_, lean_object* v_handler_2681_, lean_object* v_pendingHead_2682_, lean_object* v_dateSecond_2683_, lean_object* v_requestEnded_2684_, lean_object* v_aborted_2685_, lean_object* v_x_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v_requestEnded_boxed_2688_; uint8_t v_aborted_boxed_2689_; lean_object* v_res_2690_; 
v_requestEnded_boxed_2688_ = lean_unbox(v_requestEnded_2684_);
v_aborted_boxed_2689_ = lean_unbox(v_aborted_2685_);
v_res_2690_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14(v_requestStream_2676_, v_timer_2677_, v_response_2678_, v_respStream_2679_, v_inputWanted_2680_, v_handler_2681_, v_pendingHead_2682_, v_dateSecond_2683_, v_requestEnded_boxed_2688_, v_aborted_boxed_2689_, v_x_2686_);
return v_res_2690_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__0(void){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_2691_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__1(void){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___redArg();
return v___x_2692_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__5(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___f_2699_; lean_object* v___f_2700_; 
v___x_2698_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__1);
v___f_2699_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__4));
v___f_2700_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_2700_, 0, v___f_2699_);
lean_closure_set(v___f_2700_, 1, v___x_2698_);
return v___f_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(lean_object* v_config_2703_, lean_object* v_inst_2704_, lean_object* v_handler_2705_, lean_object* v_inst_2706_, lean_object* v_connectionContext_2707_, lean_object* v_a_2708_, lean_object* v_x_2709_, lean_object* v___y_2710_){
_start:
{
switch(lean_obj_tag(v_a_2708_))
{
case 0:
{
lean_object* v_head_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2754_; 
lean_dec_ref(v_connectionContext_2707_);
lean_dec_ref(v_inst_2706_);
lean_dec(v_handler_2705_);
lean_dec_ref(v_inst_2704_);
v_head_2712_ = lean_ctor_get(v_a_2708_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_a_2708_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2714_ = v_a_2708_;
v_isShared_2715_ = v_isSharedCheck_2754_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_head_2712_);
lean_dec(v_a_2708_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2754_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v_machine_2716_; lean_object* v_requestStream_2717_; lean_object* v_response_2718_; lean_object* v_respStream_2719_; lean_object* v_inputWanted_2720_; lean_object* v_handler_2721_; lean_object* v_dateSecond_2722_; uint8_t v_aborted_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2751_; 
v_machine_2716_ = lean_ctor_get(v___y_2710_, 0);
v_requestStream_2717_ = lean_ctor_get(v___y_2710_, 1);
v_response_2718_ = lean_ctor_get(v___y_2710_, 3);
v_respStream_2719_ = lean_ctor_get(v___y_2710_, 4);
v_inputWanted_2720_ = lean_ctor_get(v___y_2710_, 5);
v_handler_2721_ = lean_ctor_get(v___y_2710_, 6);
v_dateSecond_2722_ = lean_ctor_get(v___y_2710_, 8);
v_aborted_2723_ = lean_ctor_get_uint8(v___y_2710_, sizeof(void*)*9 + 1);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___y_2710_);
if (v_isSharedCheck_2751_ == 0)
{
lean_object* v_unused_2752_; lean_object* v_unused_2753_; 
v_unused_2752_ = lean_ctor_get(v___y_2710_, 7);
lean_dec(v_unused_2752_);
v_unused_2753_ = lean_ctor_get(v___y_2710_, 2);
lean_dec(v_unused_2753_);
v___x_2725_ = v___y_2710_;
v_isShared_2726_ = v_isSharedCheck_2751_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_dateSecond_2722_);
lean_inc(v_handler_2721_);
lean_inc(v_inputWanted_2720_);
lean_inc(v_respStream_2719_);
lean_inc(v_response_2718_);
lean_inc(v_requestStream_2717_);
lean_inc(v_machine_2716_);
lean_dec(v___y_2710_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2751_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v_lingeringTimeout_2727_; lean_object* v___x_2729_; 
v_lingeringTimeout_2727_ = lean_ctor_get(v_config_2703_, 4);
lean_inc(v_lingeringTimeout_2727_);
lean_dec_ref(v_config_2703_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set_tag(v___x_2714_, 2);
lean_ctor_set(v___x_2714_, 0, v_lingeringTimeout_2727_);
v___x_2729_ = v___x_2714_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_lingeringTimeout_2727_);
v___x_2729_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_object* v___x_2730_; uint8_t v___x_2731_; lean_object* v___x_2733_; 
lean_inc(v_head_2712_);
v___x_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_head_2712_);
v___x_2731_ = 0;
lean_inc_ref(v_requestStream_2717_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 7, v___x_2730_);
lean_ctor_set(v___x_2725_, 2, v___x_2729_);
v___x_2733_ = v___x_2725_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_machine_2716_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v_requestStream_2717_);
lean_ctor_set(v_reuseFailAlloc_2749_, 2, v___x_2729_);
lean_ctor_set(v_reuseFailAlloc_2749_, 3, v_response_2718_);
lean_ctor_set(v_reuseFailAlloc_2749_, 4, v_respStream_2719_);
lean_ctor_set(v_reuseFailAlloc_2749_, 5, v_inputWanted_2720_);
lean_ctor_set(v_reuseFailAlloc_2749_, 6, v_handler_2721_);
lean_ctor_set(v_reuseFailAlloc_2749_, 7, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2749_, 8, v_dateSecond_2722_);
lean_ctor_set_uint8(v_reuseFailAlloc_2749_, sizeof(void*)*9 + 1, v_aborted_2723_);
v___x_2733_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
uint8_t v___x_2734_; uint8_t v___x_2735_; lean_object* v___x_2736_; 
lean_ctor_set_uint8(v___x_2733_, sizeof(void*)*9, v___x_2731_);
v___x_2734_ = 0;
v___x_2735_ = 1;
v___x_2736_ = l_Std_Http_Protocol_H1_Message_Head_getSize(v___x_2734_, v_head_2712_, v___x_2735_);
lean_dec(v_head_2712_);
if (lean_obj_tag(v___x_2736_) == 1)
{
lean_object* v___f_2737_; lean_object* v___f_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___f_2741_; lean_object* v___f_2742_; lean_object* v___x_4951__overap_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___f_2737_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2737_, 0, v___x_2733_);
v___f_2738_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2738_, 0, v___x_2736_);
v___x_2739_ = lean_unsigned_to_nat(0u);
v___x_2740_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__0);
v___f_2741_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__5);
v___f_2742_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__6));
v___x_4951__overap_2743_ = l_Std_Mutex_atomically___redArg(v___x_2740_, v___f_2741_, v___f_2742_, v_requestStream_2717_, v___f_2738_);
v___x_2744_ = lean_apply_1(v___x_4951__overap_2743_, lean_box(0));
v___x_2745_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2739_, v___x_2731_, v___x_2744_, v___f_2737_);
return v___x_2745_;
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_dec(v___x_2736_);
lean_dec_ref(v_requestStream_2717_);
v___x_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2733_);
v___x_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
v___x_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
return v___x_2748_;
}
}
}
}
}
}
case 1:
{
lean_object* v_size_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2783_; 
lean_dec_ref(v_connectionContext_2707_);
lean_dec_ref(v_inst_2706_);
lean_dec(v_handler_2705_);
lean_dec_ref(v_inst_2704_);
lean_dec_ref(v_config_2703_);
v_size_2755_ = lean_ctor_get(v_a_2708_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_a_2708_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2757_ = v_a_2708_;
v_isShared_2758_ = v_isSharedCheck_2783_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_size_2755_);
lean_dec(v_a_2708_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2783_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v_machine_2759_; lean_object* v_requestStream_2760_; lean_object* v_timer_2761_; lean_object* v_response_2762_; lean_object* v_respStream_2763_; lean_object* v_handler_2764_; lean_object* v_pendingHead_2765_; lean_object* v_dateSecond_2766_; uint8_t v_requestEnded_2767_; uint8_t v_aborted_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2781_; 
v_machine_2759_ = lean_ctor_get(v___y_2710_, 0);
v_requestStream_2760_ = lean_ctor_get(v___y_2710_, 1);
v_timer_2761_ = lean_ctor_get(v___y_2710_, 2);
v_response_2762_ = lean_ctor_get(v___y_2710_, 3);
v_respStream_2763_ = lean_ctor_get(v___y_2710_, 4);
v_handler_2764_ = lean_ctor_get(v___y_2710_, 6);
v_pendingHead_2765_ = lean_ctor_get(v___y_2710_, 7);
v_dateSecond_2766_ = lean_ctor_get(v___y_2710_, 8);
v_requestEnded_2767_ = lean_ctor_get_uint8(v___y_2710_, sizeof(void*)*9);
v_aborted_2768_ = lean_ctor_get_uint8(v___y_2710_, sizeof(void*)*9 + 1);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___y_2710_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; 
v_unused_2782_ = lean_ctor_get(v___y_2710_, 5);
lean_dec(v_unused_2782_);
v___x_2770_ = v___y_2710_;
v_isShared_2771_ = v_isSharedCheck_2781_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_dateSecond_2766_);
lean_inc(v_pendingHead_2765_);
lean_inc(v_handler_2764_);
lean_inc(v_respStream_2763_);
lean_inc(v_response_2762_);
lean_inc(v_timer_2761_);
lean_inc(v_requestStream_2760_);
lean_inc(v_machine_2759_);
lean_dec(v___y_2710_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2781_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2758_ == 0)
{
v___x_2773_ = v___x_2757_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_size_2755_);
v___x_2773_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2775_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 5, v___x_2773_);
v___x_2775_ = v___x_2770_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_machine_2759_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_requestStream_2760_);
lean_ctor_set(v_reuseFailAlloc_2779_, 2, v_timer_2761_);
lean_ctor_set(v_reuseFailAlloc_2779_, 3, v_response_2762_);
lean_ctor_set(v_reuseFailAlloc_2779_, 4, v_respStream_2763_);
lean_ctor_set(v_reuseFailAlloc_2779_, 5, v___x_2773_);
lean_ctor_set(v_reuseFailAlloc_2779_, 6, v_handler_2764_);
lean_ctor_set(v_reuseFailAlloc_2779_, 7, v_pendingHead_2765_);
lean_ctor_set(v_reuseFailAlloc_2779_, 8, v_dateSecond_2766_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, sizeof(void*)*9, v_requestEnded_2767_);
lean_ctor_set_uint8(v_reuseFailAlloc_2779_, sizeof(void*)*9 + 1, v_aborted_2768_);
v___x_2775_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2775_);
v___x_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
v___x_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
return v___x_2778_;
}
}
}
}
}
case 2:
{
lean_object* v_err_2784_; lean_object* v_machine_2785_; lean_object* v_requestStream_2786_; lean_object* v_timer_2787_; lean_object* v_response_2788_; lean_object* v_respStream_2789_; lean_object* v_handler_2790_; lean_object* v_dateSecond_2791_; uint8_t v_requestEnded_2792_; uint8_t v_aborted_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___f_2796_; lean_object* v___f_2797_; 
lean_dec_ref(v_connectionContext_2707_);
lean_dec_ref(v_inst_2706_);
lean_dec_ref(v_config_2703_);
v_err_2784_ = lean_ctor_get(v_a_2708_, 0);
lean_inc_n(v_err_2784_, 2);
lean_dec_ref_known(v_a_2708_, 1);
v_machine_2785_ = lean_ctor_get(v___y_2710_, 0);
v_requestStream_2786_ = lean_ctor_get(v___y_2710_, 1);
v_timer_2787_ = lean_ctor_get(v___y_2710_, 2);
v_response_2788_ = lean_ctor_get(v___y_2710_, 3);
v_respStream_2789_ = lean_ctor_get(v___y_2710_, 4);
v_handler_2790_ = lean_ctor_get(v___y_2710_, 6);
v_dateSecond_2791_ = lean_ctor_get(v___y_2710_, 8);
v_requestEnded_2792_ = lean_ctor_get_uint8(v___y_2710_, sizeof(void*)*9);
v_aborted_2793_ = lean_ctor_get_uint8(v___y_2710_, sizeof(void*)*9 + 1);
v___x_2794_ = lean_box(v_requestEnded_2792_);
v___x_2795_ = lean_box(v_aborted_2793_);
lean_inc(v_dateSecond_2791_);
lean_inc(v_handler_2790_);
lean_inc(v_respStream_2789_);
lean_inc_ref(v_response_2788_);
lean_inc(v_timer_2787_);
lean_inc_ref(v_requestStream_2786_);
lean_inc_ref(v_machine_2785_);
v___f_2796_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__2___boxed), 11, 9);
lean_closure_set(v___f_2796_, 0, v_machine_2785_);
lean_closure_set(v___f_2796_, 1, v_requestStream_2786_);
lean_closure_set(v___f_2796_, 2, v_timer_2787_);
lean_closure_set(v___f_2796_, 3, v_response_2788_);
lean_closure_set(v___f_2796_, 4, v_respStream_2789_);
lean_closure_set(v___f_2796_, 5, v_handler_2790_);
lean_closure_set(v___f_2796_, 6, v_dateSecond_2791_);
lean_closure_set(v___f_2796_, 7, v___x_2794_);
lean_closure_set(v___f_2796_, 8, v___x_2795_);
lean_inc_ref(v___f_2796_);
lean_inc_ref(v___y_2710_);
v___f_2797_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___boxed), 5, 3);
lean_closure_set(v___f_2797_, 0, v___y_2710_);
lean_closure_set(v___f_2797_, 1, v___f_2796_);
lean_closure_set(v___f_2797_, 2, v_err_2784_);
if (v_aborted_2793_ == 0)
{
lean_object* v___f_2798_; lean_object* v___y_2800_; 
lean_dec_ref(v___f_2796_);
lean_dec_ref(v___y_2710_);
v___f_2798_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2798_, 0, v___f_2797_);
switch(lean_obj_tag(v_err_2784_))
{
case 0:
{
lean_object* v___x_2805_; 
v___x_2805_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__1));
v___y_2800_ = v___x_2805_;
goto v___jp_2799_;
}
case 1:
{
lean_object* v___x_2806_; 
v___x_2806_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__2));
v___y_2800_ = v___x_2806_;
goto v___jp_2799_;
}
case 2:
{
lean_object* v___x_2807_; 
v___x_2807_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__3));
v___y_2800_ = v___x_2807_;
goto v___jp_2799_;
}
case 3:
{
lean_object* v___x_2808_; 
v___x_2808_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__4));
v___y_2800_ = v___x_2808_;
goto v___jp_2799_;
}
case 4:
{
lean_object* v___x_2809_; 
v___x_2809_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__5));
v___y_2800_ = v___x_2809_;
goto v___jp_2799_;
}
case 5:
{
lean_object* v___x_2810_; 
v___x_2810_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__6));
v___y_2800_ = v___x_2810_;
goto v___jp_2799_;
}
case 6:
{
lean_object* v___x_2811_; 
v___x_2811_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__7));
v___y_2800_ = v___x_2811_;
goto v___jp_2799_;
}
case 7:
{
lean_object* v___x_2812_; 
v___x_2812_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__8));
v___y_2800_ = v___x_2812_;
goto v___jp_2799_;
}
case 8:
{
lean_object* v___x_2813_; 
v___x_2813_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__9));
v___y_2800_ = v___x_2813_;
goto v___jp_2799_;
}
case 9:
{
lean_object* v___x_2814_; 
v___x_2814_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__10));
v___y_2800_ = v___x_2814_;
goto v___jp_2799_;
}
case 10:
{
lean_object* v___x_2815_; 
v___x_2815_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__11));
v___y_2800_ = v___x_2815_;
goto v___jp_2799_;
}
case 11:
{
lean_object* v___x_2816_; 
v___x_2816_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__12));
v___y_2800_ = v___x_2816_;
goto v___jp_2799_;
}
case 12:
{
lean_object* v___x_2817_; 
v___x_2817_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__13));
v___y_2800_ = v___x_2817_;
goto v___jp_2799_;
}
default: 
{
lean_object* v_message_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_message_2818_ = lean_ctor_get(v_err_2784_, 0);
lean_inc_ref(v_message_2818_);
lean_dec_ref_known(v_err_2784_, 1);
v___x_2819_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3___closed__14));
v___x_2820_ = lean_string_append(v___x_2819_, v_message_2818_);
lean_dec_ref(v_message_2818_);
v___y_2800_ = v___x_2820_;
goto v___jp_2799_;
}
}
v___jp_2799_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2801_ = lean_mk_io_user_error(v___y_2800_);
v___x_2802_ = lean_unsigned_to_nat(0u);
v___x_2803_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_2704_, v_handler_2705_, v___x_2801_);
v___x_2804_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2802_, v_aborted_2793_, v___x_2803_, v___f_2798_);
return v___x_2804_;
}
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
lean_dec_ref(v___f_2797_);
lean_dec(v_handler_2705_);
lean_dec_ref(v_inst_2704_);
v___x_2821_ = lean_box(0);
v___x_2822_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__3(v___y_2710_, v___f_2796_, v_err_2784_, v___x_2821_);
lean_dec(v_err_2784_);
return v___x_2822_;
}
}
case 4:
{
lean_object* v___f_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec_ref(v_connectionContext_2707_);
lean_dec_ref(v_inst_2706_);
lean_dec(v_handler_2705_);
lean_dec_ref(v_inst_2704_);
lean_dec_ref(v_config_2703_);
lean_inc_ref(v___y_2710_);
v___f_2823_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_2823_, 0, v___y_2710_);
v___x_2824_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__7));
v___x_2825_ = lean_unsigned_to_nat(0u);
v___x_2826_ = 0;
v___x_2827_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v___y_2710_, v___x_2824_);
v___x_2828_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2825_, v___x_2826_, v___x_2827_, v___f_2823_);
return v___x_2828_;
}
case 6:
{
lean_object* v___f_2829_; lean_object* v___f_2830_; lean_object* v___f_2831_; lean_object* v___f_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_dec_ref(v_connectionContext_2707_);
lean_dec(v_handler_2705_);
lean_dec_ref(v_inst_2704_);
lean_inc_ref_n(v___y_2710_, 2);
v___f_2829_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_2829_, 0, v___y_2710_);
lean_closure_set(v___f_2829_, 1, v_config_2703_);
v___f_2830_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_2830_, 0, v___f_2829_);
lean_inc_ref(v___f_2830_);
v___f_2831_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_2831_, 0, v___f_2830_);
v___f_2832_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_2832_, 0, v___y_2710_);
lean_closure_set(v___f_2832_, 1, v_inst_2706_);
lean_closure_set(v___f_2832_, 2, v___f_2831_);
lean_closure_set(v___f_2832_, 3, v___f_2830_);
v___x_2833_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__7));
v___x_2834_ = lean_unsigned_to_nat(0u);
v___x_2835_ = 0;
v___x_2836_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___redArg(v___y_2710_, v___x_2833_);
v___x_2837_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2834_, v___x_2835_, v___x_2836_, v___f_2832_);
return v___x_2837_;
}
case 7:
{
lean_object* v_pendingHead_2838_; 
lean_dec_ref(v_inst_2706_);
v_pendingHead_2838_ = lean_ctor_get(v___y_2710_, 7);
if (lean_obj_tag(v_pendingHead_2838_) == 1)
{
lean_object* v_machine_2839_; lean_object* v_requestStream_2840_; lean_object* v_timer_2841_; lean_object* v_response_2842_; lean_object* v_respStream_2843_; lean_object* v_inputWanted_2844_; lean_object* v_handler_2845_; lean_object* v_dateSecond_2846_; uint8_t v_requestEnded_2847_; uint8_t v_aborted_2848_; lean_object* v_val_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___f_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_inc_ref(v_pendingHead_2838_);
v_machine_2839_ = lean_ctor_get(v___y_2710_, 0);
lean_inc_ref(v_machine_2839_);
v_requestStream_2840_ = lean_ctor_get(v___y_2710_, 1);
lean_inc_ref(v_requestStream_2840_);
v_timer_2841_ = lean_ctor_get(v___y_2710_, 2);
lean_inc(v_timer_2841_);
v_response_2842_ = lean_ctor_get(v___y_2710_, 3);
lean_inc_ref(v_response_2842_);
v_respStream_2843_ = lean_ctor_get(v___y_2710_, 4);
lean_inc(v_respStream_2843_);
v_inputWanted_2844_ = lean_ctor_get(v___y_2710_, 5);
lean_inc(v_inputWanted_2844_);
v_handler_2845_ = lean_ctor_get(v___y_2710_, 6);
lean_inc(v_handler_2845_);
v_dateSecond_2846_ = lean_ctor_get(v___y_2710_, 8);
lean_inc(v_dateSecond_2846_);
v_requestEnded_2847_ = lean_ctor_get_uint8(v___y_2710_, sizeof(void*)*9);
v_aborted_2848_ = lean_ctor_get_uint8(v___y_2710_, sizeof(void*)*9 + 1);
lean_dec_ref(v___y_2710_);
v_val_2849_ = lean_ctor_get(v_pendingHead_2838_, 0);
lean_inc(v_val_2849_);
v___x_2850_ = lean_box(v_requestEnded_2847_);
v___x_2851_ = lean_box(v_aborted_2848_);
v___f_2852_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__14___boxed), 12, 10);
lean_closure_set(v___f_2852_, 0, v_requestStream_2840_);
lean_closure_set(v___f_2852_, 1, v_timer_2841_);
lean_closure_set(v___f_2852_, 2, v_response_2842_);
lean_closure_set(v___f_2852_, 3, v_respStream_2843_);
lean_closure_set(v___f_2852_, 4, v_inputWanted_2844_);
lean_closure_set(v___f_2852_, 5, v_handler_2845_);
lean_closure_set(v___f_2852_, 6, v_pendingHead_2838_);
lean_closure_set(v___f_2852_, 7, v_dateSecond_2846_);
lean_closure_set(v___f_2852_, 8, v___x_2850_);
lean_closure_set(v___f_2852_, 9, v___x_2851_);
v___x_2853_ = lean_unsigned_to_nat(0u);
v___x_2854_ = 0;
v___x_2855_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg(v_inst_2704_, v_handler_2705_, v_machine_2839_, v_val_2849_, v_config_2703_, v_connectionContext_2707_);
v___x_2856_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2853_, v___x_2854_, v___x_2855_, v___f_2852_);
return v___x_2856_;
}
else
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_dec_ref(v_connectionContext_2707_);
lean_dec(v_handler_2705_);
lean_dec_ref(v_inst_2704_);
lean_dec_ref(v_config_2703_);
v___x_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___y_2710_);
v___x_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
v___x_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
return v___x_2859_;
}
}
default: 
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
lean_dec(v_a_2708_);
lean_dec_ref(v_connectionContext_2707_);
lean_dec_ref(v_inst_2706_);
lean_dec(v_handler_2705_);
lean_dec_ref(v_inst_2704_);
lean_dec_ref(v_config_2703_);
v___x_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___y_2710_);
v___x_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
v___x_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
return v___x_2862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed(lean_object* v_config_2863_, lean_object* v_inst_2864_, lean_object* v_handler_2865_, lean_object* v_inst_2866_, lean_object* v_connectionContext_2867_, lean_object* v_a_2868_, lean_object* v_x_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15(v_config_2863_, v_inst_2864_, v_handler_2865_, v_inst_2866_, v_connectionContext_2867_, v_a_2868_, v_x_2869_, v___y_2870_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(lean_object* v_x_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v_x_2873_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16___boxed(lean_object* v_x_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__16(v_x_2876_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(lean_object* v_inst_2880_, lean_object* v_inst_2881_, lean_object* v_handler_2882_, lean_object* v_config_2883_, lean_object* v_connectionContext_2884_, lean_object* v_events_2885_, lean_object* v_state_2886_){
_start:
{
lean_object* v___f_2888_; lean_object* v___f_2889_; lean_object* v___x_2890_; size_t v_sz_2891_; size_t v___x_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; lean_object* v___x_4172__overap_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___f_2888_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___boxed), 9, 5);
lean_closure_set(v___f_2888_, 0, v_config_2883_);
lean_closure_set(v___f_2888_, 1, v_inst_2880_);
lean_closure_set(v___f_2888_, 2, v_handler_2882_);
lean_closure_set(v___f_2888_, 3, v_inst_2881_);
lean_closure_set(v___f_2888_, 4, v_connectionContext_2884_);
v___f_2889_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___closed__0));
v___x_2890_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__0);
v_sz_2891_ = lean_array_size(v_events_2885_);
v___x_2892_ = ((size_t)0ULL);
v___x_2893_ = lean_unsigned_to_nat(0u);
v___x_2894_ = 0;
v___x_4172__overap_2895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2890_, v_events_2885_, v___f_2888_, v_sz_2891_, v___x_2892_, v_state_2886_);
v___x_2896_ = lean_apply_1(v___x_4172__overap_2895_, lean_box(0));
v___x_2897_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2893_, v___x_2894_, v___x_2896_, v___f_2889_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___boxed(lean_object* v_inst_2898_, lean_object* v_inst_2899_, lean_object* v_handler_2900_, lean_object* v_config_2901_, lean_object* v_connectionContext_2902_, lean_object* v_events_2903_, lean_object* v_state_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2898_, v_inst_2899_, v_handler_2900_, v_config_2901_, v_connectionContext_2902_, v_events_2903_, v_state_2904_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(lean_object* v_00_u03c3_2907_, lean_object* v_00_u03b2_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_handler_2911_, lean_object* v_config_2912_, lean_object* v_connectionContext_2913_, lean_object* v_events_2914_, lean_object* v_state_2915_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_inst_2909_, v_inst_2910_, v_handler_2911_, v_config_2912_, v_connectionContext_2913_, v_events_2914_, v_state_2915_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___boxed(lean_object* v_00_u03c3_2918_, lean_object* v_00_u03b2_2919_, lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_handler_2922_, lean_object* v_config_2923_, lean_object* v_connectionContext_2924_, lean_object* v_events_2925_, lean_object* v_state_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events(v_00_u03c3_2918_, v_00_u03b2_2919_, v_inst_2920_, v_inst_2921_, v_handler_2922_, v_config_2923_, v_connectionContext_2924_, v_events_2925_, v_state_2926_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__0(lean_object* v_x_2929_){
_start:
{
if (lean_obj_tag(v_x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2931_; 
v_a_2930_ = lean_ctor_get(v_x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref_known(v_x_2929_, 1);
v___x_2931_ = lean_task_pure(v_a_2930_);
return v___x_2931_;
}
else
{
lean_object* v_a_2932_; 
v_a_2932_ = lean_ctor_get(v_x_2929_, 0);
lean_inc_ref(v_a_2932_);
lean_dec_ref_known(v_x_2929_, 1);
return v_a_2932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(lean_object* v_a_2933_, lean_object* v_machine_2934_, lean_object* v_requestStream_2935_, lean_object* v_timer_2936_, lean_object* v_response_2937_, lean_object* v_respStream_2938_, lean_object* v_inputWanted_2939_, lean_object* v_dateSecond_2940_, uint8_t v_requestEnded_2941_, uint8_t v_aborted_2942_, lean_object* v_x_2943_){
_start:
{
if (lean_obj_tag(v_x_2943_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2953_; 
lean_dec(v_dateSecond_2940_);
lean_dec(v_inputWanted_2939_);
lean_dec(v_respStream_2938_);
lean_dec_ref(v_response_2937_);
lean_dec(v_timer_2936_);
lean_dec_ref(v_requestStream_2935_);
lean_dec_ref(v_machine_2934_);
lean_dec_ref(v_a_2933_);
v_a_2945_ = lean_ctor_get(v_x_2943_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v_x_2943_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2947_ = v_x_2943_;
v_isShared_2948_ = v_isSharedCheck_2953_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v_x_2943_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2953_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2951_; 
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
return v___x_2951_;
}
}
}
else
{
lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2964_; 
v_isSharedCheck_2964_ = !lean_is_exclusive(v_x_2943_);
if (v_isSharedCheck_2964_ == 0)
{
lean_object* v_unused_2965_; 
v_unused_2965_ = lean_ctor_get(v_x_2943_, 0);
lean_dec(v_unused_2965_);
v___x_2955_ = v_x_2943_;
v_isShared_2956_ = v_isSharedCheck_2964_;
goto v_resetjp_2954_;
}
else
{
lean_dec(v_x_2943_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2964_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2957_, 0, v_a_2933_);
v___x_2958_ = lean_box(0);
v___x_2959_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_2959_, 0, v_machine_2934_);
lean_ctor_set(v___x_2959_, 1, v_requestStream_2935_);
lean_ctor_set(v___x_2959_, 2, v_timer_2936_);
lean_ctor_set(v___x_2959_, 3, v_response_2937_);
lean_ctor_set(v___x_2959_, 4, v_respStream_2938_);
lean_ctor_set(v___x_2959_, 5, v_inputWanted_2939_);
lean_ctor_set(v___x_2959_, 6, v___x_2957_);
lean_ctor_set(v___x_2959_, 7, v___x_2958_);
lean_ctor_set(v___x_2959_, 8, v_dateSecond_2940_);
lean_ctor_set_uint8(v___x_2959_, sizeof(void*)*9, v_requestEnded_2941_);
lean_ctor_set_uint8(v___x_2959_, sizeof(void*)*9 + 1, v_aborted_2942_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2959_);
v___x_2961_ = v___x_2955_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed(lean_object* v_a_2966_, lean_object* v_machine_2967_, lean_object* v_requestStream_2968_, lean_object* v_timer_2969_, lean_object* v_response_2970_, lean_object* v_respStream_2971_, lean_object* v_inputWanted_2972_, lean_object* v_dateSecond_2973_, lean_object* v_requestEnded_2974_, lean_object* v_aborted_2975_, lean_object* v_x_2976_, lean_object* v___y_2977_){
_start:
{
uint8_t v_requestEnded_boxed_2978_; uint8_t v_aborted_boxed_2979_; lean_object* v_res_2980_; 
v_requestEnded_boxed_2978_ = lean_unbox(v_requestEnded_2974_);
v_aborted_boxed_2979_ = lean_unbox(v_aborted_2975_);
v_res_2980_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1(v_a_2966_, v_machine_2967_, v_requestStream_2968_, v_timer_2969_, v_response_2970_, v_respStream_2971_, v_inputWanted_2972_, v_dateSecond_2973_, v_requestEnded_boxed_2978_, v_aborted_boxed_2979_, v_x_2976_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(lean_object* v_machine_2981_, lean_object* v_requestStream_2982_, lean_object* v_timer_2983_, lean_object* v_response_2984_, lean_object* v_respStream_2985_, lean_object* v_inputWanted_2986_, lean_object* v_dateSecond_2987_, uint8_t v_requestEnded_2988_, uint8_t v_aborted_2989_, lean_object* v_toFunctor_2990_, lean_object* v___x_2991_, lean_object* v_x_2992_){
_start:
{
if (lean_obj_tag(v_x_2992_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v___x_2991_);
lean_dec_ref(v_toFunctor_2990_);
lean_dec(v_dateSecond_2987_);
lean_dec(v_inputWanted_2986_);
lean_dec(v_respStream_2985_);
lean_dec_ref(v_response_2984_);
lean_dec(v_timer_2983_);
lean_dec_ref(v_requestStream_2982_);
lean_dec_ref(v_machine_2981_);
v_a_2994_ = lean_ctor_get(v_x_2992_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_x_2992_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2996_ = v_x_2992_;
v_isShared_2997_ = v_isSharedCheck_3002_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v_x_2992_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3002_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3000_; 
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
return v___x_3000_;
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3020_; 
v_a_3003_ = lean_ctor_get(v_x_2992_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_x_2992_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3005_ = v_x_2992_;
v_isShared_3006_ = v_isSharedCheck_3020_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v_x_2992_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3020_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___f_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3007_ = lean_box(v_requestEnded_2988_);
v___x_3008_ = lean_box(v_aborted_2989_);
lean_inc_ref(v_response_2984_);
lean_inc(v_a_3003_);
v___f_3009_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__1___boxed), 12, 10);
lean_closure_set(v___f_3009_, 0, v_a_3003_);
lean_closure_set(v___f_3009_, 1, v_machine_2981_);
lean_closure_set(v___f_3009_, 2, v_requestStream_2982_);
lean_closure_set(v___f_3009_, 3, v_timer_2983_);
lean_closure_set(v___f_3009_, 4, v_response_2984_);
lean_closure_set(v___f_3009_, 5, v_respStream_2985_);
lean_closure_set(v___f_3009_, 6, v_inputWanted_2986_);
lean_closure_set(v___f_3009_, 7, v_dateSecond_2987_);
lean_closure_set(v___f_3009_, 8, v___x_3007_);
lean_closure_set(v___f_3009_, 9, v___x_3008_);
v___x_3010_ = lean_alloc_closure((void*)(l_Functor_discard), 4, 3);
lean_closure_set(v___x_3010_, 0, lean_box(0));
lean_closure_set(v___x_3010_, 1, lean_box(0));
lean_closure_set(v___x_3010_, 2, v_toFunctor_2990_);
v___x_3011_ = lean_alloc_closure((void*)(l_Std_Channel_send___boxed), 4, 2);
lean_closure_set(v___x_3011_, 0, lean_box(0));
lean_closure_set(v___x_3011_, 1, v_response_2984_);
v___x_3012_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_3012_, 0, lean_box(0));
lean_closure_set(v___x_3012_, 1, lean_box(0));
lean_closure_set(v___x_3012_, 2, lean_box(0));
lean_closure_set(v___x_3012_, 3, v___x_3010_);
lean_closure_set(v___x_3012_, 4, v___x_3011_);
v___x_3013_ = 0;
lean_inc(v___x_2991_);
v___x_3014_ = l_BaseIO_chainTask___redArg(v_a_3003_, v___x_3012_, v___x_2991_, v___x_3013_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3014_);
v___x_3016_ = v___x_3005_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
v___x_3018_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_2991_, v___x_3013_, v___x_3017_, v___f_3009_);
return v___x_3018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed(lean_object* v_machine_3021_, lean_object* v_requestStream_3022_, lean_object* v_timer_3023_, lean_object* v_response_3024_, lean_object* v_respStream_3025_, lean_object* v_inputWanted_3026_, lean_object* v_dateSecond_3027_, lean_object* v_requestEnded_3028_, lean_object* v_aborted_3029_, lean_object* v_toFunctor_3030_, lean_object* v___x_3031_, lean_object* v_x_3032_, lean_object* v___y_3033_){
_start:
{
uint8_t v_requestEnded_boxed_3034_; uint8_t v_aborted_boxed_3035_; lean_object* v_res_3036_; 
v_requestEnded_boxed_3034_ = lean_unbox(v_requestEnded_3028_);
v_aborted_boxed_3035_ = lean_unbox(v_aborted_3029_);
v_res_3036_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2(v_machine_3021_, v_requestStream_3022_, v_timer_3023_, v_response_3024_, v_respStream_3025_, v_inputWanted_3026_, v_dateSecond_3027_, v_requestEnded_boxed_3034_, v_aborted_boxed_3035_, v_toFunctor_3030_, v___x_3031_, v_x_3032_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(lean_object* v_inst_3038_, lean_object* v_handler_3039_, lean_object* v_extensions_3040_, lean_object* v_connectionContext_3041_, lean_object* v_state_3042_){
_start:
{
lean_object* v___x_3044_; lean_object* v_toApplicative_3045_; lean_object* v_pendingHead_3046_; 
v___x_3044_ = l_instMonadBaseIO;
v_toApplicative_3045_ = lean_ctor_get(v___x_3044_, 0);
v_pendingHead_3046_ = lean_ctor_get(v_state_3042_, 7);
lean_inc(v_pendingHead_3046_);
if (lean_obj_tag(v_pendingHead_3046_) == 1)
{
lean_object* v_toFunctor_3047_; lean_object* v_machine_3048_; lean_object* v_requestStream_3049_; lean_object* v_timer_3050_; lean_object* v_response_3051_; lean_object* v_respStream_3052_; lean_object* v_inputWanted_3053_; lean_object* v_dateSecond_3054_; uint8_t v_requestEnded_3055_; uint8_t v_aborted_3056_; lean_object* v_val_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3079_; 
v_toFunctor_3047_ = lean_ctor_get(v_toApplicative_3045_, 0);
v_machine_3048_ = lean_ctor_get(v_state_3042_, 0);
lean_inc_ref(v_machine_3048_);
v_requestStream_3049_ = lean_ctor_get(v_state_3042_, 1);
lean_inc_ref(v_requestStream_3049_);
v_timer_3050_ = lean_ctor_get(v_state_3042_, 2);
lean_inc(v_timer_3050_);
v_response_3051_ = lean_ctor_get(v_state_3042_, 3);
lean_inc_ref(v_response_3051_);
v_respStream_3052_ = lean_ctor_get(v_state_3042_, 4);
lean_inc(v_respStream_3052_);
v_inputWanted_3053_ = lean_ctor_get(v_state_3042_, 5);
lean_inc(v_inputWanted_3053_);
v_dateSecond_3054_ = lean_ctor_get(v_state_3042_, 8);
lean_inc(v_dateSecond_3054_);
v_requestEnded_3055_ = lean_ctor_get_uint8(v_state_3042_, sizeof(void*)*9);
v_aborted_3056_ = lean_ctor_get_uint8(v_state_3042_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_3042_);
v_val_3057_ = lean_ctor_get(v_pendingHead_3046_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_pendingHead_3046_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3059_ = v_pendingHead_3046_;
v_isShared_3060_ = v_isSharedCheck_3079_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_val_3057_);
lean_dec(v_pendingHead_3046_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3079_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v_onRequest_3061_; lean_object* v___f_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___f_3068_; uint8_t v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; uint8_t v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
v_onRequest_3061_ = lean_ctor_get(v_inst_3038_, 1);
lean_inc_ref(v_onRequest_3061_);
lean_dec_ref(v_inst_3038_);
v___f_3062_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___closed__0));
lean_inc_ref(v_requestStream_3049_);
v___x_3063_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3063_, 0, v_val_3057_);
lean_ctor_set(v___x_3063_, 1, v_requestStream_3049_);
lean_ctor_set(v___x_3063_, 2, v_extensions_3040_);
v___x_3064_ = lean_apply_3(v_onRequest_3061_, v_handler_3039_, v___x_3063_, v_connectionContext_3041_);
v___x_3065_ = lean_unsigned_to_nat(0u);
v___x_3066_ = lean_box(v_requestEnded_3055_);
v___x_3067_ = lean_box(v_aborted_3056_);
lean_inc_ref(v_toFunctor_3047_);
v___f_3068_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___lam__2___boxed), 13, 11);
lean_closure_set(v___f_3068_, 0, v_machine_3048_);
lean_closure_set(v___f_3068_, 1, v_requestStream_3049_);
lean_closure_set(v___f_3068_, 2, v_timer_3050_);
lean_closure_set(v___f_3068_, 3, v_response_3051_);
lean_closure_set(v___f_3068_, 4, v_respStream_3052_);
lean_closure_set(v___f_3068_, 5, v_inputWanted_3053_);
lean_closure_set(v___f_3068_, 6, v_dateSecond_3054_);
lean_closure_set(v___f_3068_, 7, v___x_3066_);
lean_closure_set(v___f_3068_, 8, v___x_3067_);
lean_closure_set(v___f_3068_, 9, v_toFunctor_3047_);
lean_closure_set(v___f_3068_, 10, v___x_3065_);
v___x_3069_ = 0;
v___x_3070_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_3070_, 0, lean_box(0));
lean_closure_set(v___x_3070_, 1, v___x_3064_);
v___x_3071_ = lean_io_as_task(v___x_3070_, v___x_3065_);
v___x_3072_ = 1;
v___x_3073_ = lean_task_bind(v___x_3071_, v___f_3062_, v___x_3065_, v___x_3072_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3073_);
v___x_3075_ = v___x_3059_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
v___x_3077_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3065_, v___x_3069_, v___x_3076_, v___f_3068_);
return v___x_3077_;
}
}
}
else
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec(v_pendingHead_3046_);
lean_dec_ref(v_connectionContext_3041_);
lean_dec(v_extensions_3040_);
lean_dec(v_handler_3039_);
lean_dec_ref(v_inst_3038_);
v___x_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3080_, 0, v_state_3042_);
v___x_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
return v___x_3081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg___boxed(lean_object* v_inst_3082_, lean_object* v_handler_3083_, lean_object* v_extensions_3084_, lean_object* v_connectionContext_3085_, lean_object* v_state_3086_, lean_object* v_a_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_3082_, v_handler_3083_, v_extensions_3084_, v_connectionContext_3085_, v_state_3086_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(lean_object* v_00_u03c3_3089_, lean_object* v_inst_3090_, lean_object* v_handler_3091_, lean_object* v_extensions_3092_, lean_object* v_connectionContext_3093_, lean_object* v_state_3094_){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_inst_3090_, v_handler_3091_, v_extensions_3092_, v_connectionContext_3093_, v_state_3094_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___boxed(lean_object* v_00_u03c3_3097_, lean_object* v_inst_3098_, lean_object* v_handler_3099_, lean_object* v_extensions_3100_, lean_object* v_connectionContext_3101_, lean_object* v_state_3102_, lean_object* v_a_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest(v_00_u03c3_3097_, v_inst_3098_, v_handler_3099_, v_extensions_3100_, v_connectionContext_3101_, v_state_3102_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(lean_object* v_machine_3105_, lean_object* v_____r_3106_){
_start:
{
lean_object* v_writer_3108_; lean_object* v_reader_3109_; lean_object* v_config_3110_; lean_object* v_events_3111_; lean_object* v_error_3112_; lean_object* v_date_3113_; uint8_t v_keepAlive_3114_; uint8_t v_pullBodyStalled_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3141_; 
v_writer_3108_ = lean_ctor_get(v_machine_3105_, 1);
v_reader_3109_ = lean_ctor_get(v_machine_3105_, 0);
v_config_3110_ = lean_ctor_get(v_machine_3105_, 2);
v_events_3111_ = lean_ctor_get(v_machine_3105_, 3);
v_error_3112_ = lean_ctor_get(v_machine_3105_, 4);
v_date_3113_ = lean_ctor_get(v_machine_3105_, 5);
v_keepAlive_3114_ = lean_ctor_get_uint8(v_machine_3105_, sizeof(void*)*6);
v_pullBodyStalled_3115_ = lean_ctor_get_uint8(v_machine_3105_, sizeof(void*)*6 + 1);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_machine_3105_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3117_ = v_machine_3105_;
v_isShared_3118_ = v_isSharedCheck_3141_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_date_3113_);
lean_inc(v_error_3112_);
lean_inc(v_events_3111_);
lean_inc(v_config_3110_);
lean_inc(v_writer_3108_);
lean_inc(v_reader_3109_);
lean_dec(v_machine_3105_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3141_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v_userData_3119_; lean_object* v_outputData_3120_; lean_object* v_state_3121_; lean_object* v_knownSize_3122_; lean_object* v_messageHead_3123_; uint8_t v_omitBody_3124_; lean_object* v_userDataBytes_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3140_; 
v_userData_3119_ = lean_ctor_get(v_writer_3108_, 0);
v_outputData_3120_ = lean_ctor_get(v_writer_3108_, 1);
v_state_3121_ = lean_ctor_get(v_writer_3108_, 2);
v_knownSize_3122_ = lean_ctor_get(v_writer_3108_, 3);
v_messageHead_3123_ = lean_ctor_get(v_writer_3108_, 4);
v_omitBody_3124_ = lean_ctor_get_uint8(v_writer_3108_, sizeof(void*)*6 + 1);
v_userDataBytes_3125_ = lean_ctor_get(v_writer_3108_, 5);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_writer_3108_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3127_ = v_writer_3108_;
v_isShared_3128_ = v_isSharedCheck_3140_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_userDataBytes_3125_);
lean_inc(v_messageHead_3123_);
lean_inc(v_knownSize_3122_);
lean_inc(v_state_3121_);
lean_inc(v_outputData_3120_);
lean_inc(v_userData_3119_);
lean_dec(v_writer_3108_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3140_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
uint8_t v___x_3129_; lean_object* v___x_3131_; 
v___x_3129_ = 1;
if (v_isShared_3128_ == 0)
{
v___x_3131_ = v___x_3127_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_userData_3119_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_outputData_3120_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_state_3121_);
lean_ctor_set(v_reuseFailAlloc_3139_, 3, v_knownSize_3122_);
lean_ctor_set(v_reuseFailAlloc_3139_, 4, v_messageHead_3123_);
lean_ctor_set(v_reuseFailAlloc_3139_, 5, v_userDataBytes_3125_);
lean_ctor_set_uint8(v_reuseFailAlloc_3139_, sizeof(void*)*6 + 1, v_omitBody_3124_);
v___x_3131_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3133_; 
lean_ctor_set_uint8(v___x_3131_, sizeof(void*)*6, v___x_3129_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v___x_3131_);
v___x_3133_ = v___x_3117_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_reader_3109_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v___x_3131_);
lean_ctor_set(v_reuseFailAlloc_3138_, 2, v_config_3110_);
lean_ctor_set(v_reuseFailAlloc_3138_, 3, v_events_3111_);
lean_ctor_set(v_reuseFailAlloc_3138_, 4, v_error_3112_);
lean_ctor_set(v_reuseFailAlloc_3138_, 5, v_date_3113_);
lean_ctor_set_uint8(v_reuseFailAlloc_3138_, sizeof(void*)*6, v_keepAlive_3114_);
lean_ctor_set_uint8(v_reuseFailAlloc_3138_, sizeof(void*)*6 + 1, v_pullBodyStalled_3115_);
v___x_3133_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3134_ = lean_box(0);
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3133_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
v___x_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
return v___x_3137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed(lean_object* v_machine_3142_, lean_object* v_____r_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0(v_machine_3142_, v_____r_3143_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(lean_object* v_x1_3146_, lean_object* v_x2_3147_){
_start:
{
lean_object* v_data_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v_data_3148_ = lean_ctor_get(v_x2_3147_, 0);
v___x_3149_ = lean_byte_array_size(v_data_3148_);
v___x_3150_ = lean_nat_add(v_x1_3146_, v___x_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3___boxed(lean_object* v_x1_3151_, lean_object* v_x2_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__3(v_x1_3151_, v_x2_3152_);
lean_dec_ref(v_x2_3152_);
lean_dec(v_x1_3151_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(lean_object* v_body_3154_, lean_object* v_machine_3155_, lean_object* v_isClosed_3156_, lean_object* v___f_3157_, lean_object* v___f_3158_, lean_object* v_x_3159_){
_start:
{
lean_object* v___y_3162_; 
if (lean_obj_tag(v_x_3159_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref(v___f_3158_);
lean_dec_ref(v___f_3157_);
lean_dec_ref(v_isClosed_3156_);
lean_dec_ref(v_machine_3155_);
lean_dec(v_body_3154_);
v_a_3167_ = lean_ctor_get(v_x_3159_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_x_3159_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3169_ = v_x_3159_;
v_isShared_3170_ = v_isSharedCheck_3175_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v_x_3159_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3175_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3173_; 
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3237_; 
v_a_3176_ = lean_ctor_get(v_x_3159_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_x_3159_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3178_ = v_x_3159_;
v_isShared_3179_ = v_isSharedCheck_3237_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v_x_3159_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3237_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
if (lean_obj_tag(v_a_3176_) == 0)
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3183_; 
lean_dec_ref(v___f_3158_);
lean_dec_ref(v___f_3157_);
lean_dec_ref(v_isClosed_3156_);
v___x_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3180_, 0, v_body_3154_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v_machine_3155_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3181_);
v___x_3183_ = v___x_3178_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3184_; 
v___x_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
return v___x_3184_;
}
}
else
{
lean_object* v_val_3186_; 
lean_del_object(v___x_3178_);
v_val_3186_ = lean_ctor_get(v_a_3176_, 0);
lean_inc(v_val_3186_);
lean_dec_ref_known(v_a_3176_, 1);
if (lean_obj_tag(v_val_3186_) == 0)
{
lean_object* v___x_3187_; uint8_t v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
lean_dec_ref(v___f_3158_);
lean_dec_ref(v_machine_3155_);
v___x_3187_ = lean_unsigned_to_nat(0u);
v___x_3188_ = 0;
v___x_3189_ = lean_apply_2(v_isClosed_3156_, v_body_3154_, lean_box(0));
v___x_3190_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3187_, v___x_3188_, v___x_3189_, v___f_3157_);
return v___x_3190_;
}
else
{
lean_object* v_val_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; uint8_t v___x_3197_; 
lean_dec_ref(v___f_3157_);
lean_dec_ref(v_isClosed_3156_);
v_val_3191_ = lean_ctor_get(v_val_3186_, 0);
lean_inc(v_val_3191_);
lean_dec_ref_known(v_val_3186_, 1);
v___x_3192_ = lean_unsigned_to_nat(1u);
v___x_3193_ = lean_mk_empty_array_with_capacity(v___x_3192_);
v___x_3194_ = lean_array_push(v___x_3193_, v_val_3191_);
v___x_3195_ = lean_array_get_size(v___x_3194_);
v___x_3196_ = lean_unsigned_to_nat(0u);
v___x_3197_ = lean_nat_dec_eq(v___x_3195_, v___x_3196_);
if (v___x_3197_ == 0)
{
lean_object* v_reader_3198_; lean_object* v_writer_3199_; lean_object* v_config_3200_; lean_object* v_events_3201_; lean_object* v_error_3202_; lean_object* v_date_3203_; uint8_t v_keepAlive_3204_; uint8_t v_pullBodyStalled_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3236_; 
v_reader_3198_ = lean_ctor_get(v_machine_3155_, 0);
v_writer_3199_ = lean_ctor_get(v_machine_3155_, 1);
v_config_3200_ = lean_ctor_get(v_machine_3155_, 2);
v_events_3201_ = lean_ctor_get(v_machine_3155_, 3);
v_error_3202_ = lean_ctor_get(v_machine_3155_, 4);
v_date_3203_ = lean_ctor_get(v_machine_3155_, 5);
v_keepAlive_3204_ = lean_ctor_get_uint8(v_machine_3155_, sizeof(void*)*6);
v_pullBodyStalled_3205_ = lean_ctor_get_uint8(v_machine_3155_, sizeof(void*)*6 + 1);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_machine_3155_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3207_ = v_machine_3155_;
v_isShared_3208_ = v_isSharedCheck_3236_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_date_3203_);
lean_inc(v_error_3202_);
lean_inc(v_events_3201_);
lean_inc(v_config_3200_);
lean_inc(v_writer_3199_);
lean_inc(v_reader_3198_);
lean_dec(v_machine_3155_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3236_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___y_3210_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3231_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__20));
v___x_3232_ = lean_nat_dec_lt(v___x_3196_, v___x_3195_);
if (v___x_3232_ == 0)
{
lean_dec_ref(v___f_3158_);
v___y_3210_ = v___x_3196_;
goto v___jp_3209_;
}
else
{
size_t v___x_3233_; size_t v___x_3234_; lean_object* v___x_3235_; 
v___x_3233_ = ((size_t)0ULL);
v___x_3234_ = lean_usize_of_nat(v___x_3195_);
lean_inc_ref(v___x_3194_);
v___x_3235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3231_, v___f_3158_, v___x_3194_, v___x_3233_, v___x_3234_, v___x_3196_);
v___y_3210_ = v___x_3235_;
goto v___jp_3209_;
}
v___jp_3209_:
{
lean_object* v_userData_3211_; lean_object* v_outputData_3212_; lean_object* v_state_3213_; lean_object* v_knownSize_3214_; lean_object* v_messageHead_3215_; uint8_t v_userClosedBody_3216_; uint8_t v_omitBody_3217_; lean_object* v_userDataBytes_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3230_; 
v_userData_3211_ = lean_ctor_get(v_writer_3199_, 0);
v_outputData_3212_ = lean_ctor_get(v_writer_3199_, 1);
v_state_3213_ = lean_ctor_get(v_writer_3199_, 2);
v_knownSize_3214_ = lean_ctor_get(v_writer_3199_, 3);
v_messageHead_3215_ = lean_ctor_get(v_writer_3199_, 4);
v_userClosedBody_3216_ = lean_ctor_get_uint8(v_writer_3199_, sizeof(void*)*6);
v_omitBody_3217_ = lean_ctor_get_uint8(v_writer_3199_, sizeof(void*)*6 + 1);
v_userDataBytes_3218_ = lean_ctor_get(v_writer_3199_, 5);
v_isSharedCheck_3230_ = !lean_is_exclusive(v_writer_3199_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3220_ = v_writer_3199_;
v_isShared_3221_ = v_isSharedCheck_3230_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_userDataBytes_3218_);
lean_inc(v_messageHead_3215_);
lean_inc(v_knownSize_3214_);
lean_inc(v_state_3213_);
lean_inc(v_outputData_3212_);
lean_inc(v_userData_3211_);
lean_dec(v_writer_3199_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3230_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3222_ = l_Array_append___redArg(v_userData_3211_, v___x_3194_);
lean_dec_ref(v___x_3194_);
v___x_3223_ = lean_nat_add(v_userDataBytes_3218_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec(v_userDataBytes_3218_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 5, v___x_3223_);
lean_ctor_set(v___x_3220_, 0, v___x_3222_);
v___x_3225_ = v___x_3220_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_outputData_3212_);
lean_ctor_set(v_reuseFailAlloc_3229_, 2, v_state_3213_);
lean_ctor_set(v_reuseFailAlloc_3229_, 3, v_knownSize_3214_);
lean_ctor_set(v_reuseFailAlloc_3229_, 4, v_messageHead_3215_);
lean_ctor_set(v_reuseFailAlloc_3229_, 5, v___x_3223_);
lean_ctor_set_uint8(v_reuseFailAlloc_3229_, sizeof(void*)*6, v_userClosedBody_3216_);
lean_ctor_set_uint8(v_reuseFailAlloc_3229_, sizeof(void*)*6 + 1, v_omitBody_3217_);
v___x_3225_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3227_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 1, v___x_3225_);
v___x_3227_ = v___x_3207_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_reader_3198_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_config_3200_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_events_3201_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_error_3202_);
lean_ctor_set(v_reuseFailAlloc_3228_, 5, v_date_3203_);
lean_ctor_set_uint8(v_reuseFailAlloc_3228_, sizeof(void*)*6, v_keepAlive_3204_);
lean_ctor_set_uint8(v_reuseFailAlloc_3228_, sizeof(void*)*6 + 1, v_pullBodyStalled_3205_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
v___y_3162_ = v___x_3227_;
goto v___jp_3161_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3194_);
lean_dec_ref(v___f_3158_);
v___y_3162_ = v_machine_3155_;
goto v___jp_3161_;
}
}
}
}
}
v___jp_3161_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3163_, 0, v_body_3154_);
v___x_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___y_3162_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
return v___x_3166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed(lean_object* v_body_3238_, lean_object* v_machine_3239_, lean_object* v_isClosed_3240_, lean_object* v___f_3241_, lean_object* v___f_3242_, lean_object* v_x_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1(v_body_3238_, v_machine_3239_, v_isClosed_3240_, v___f_3241_, v___f_3242_, v_x_3243_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(lean_object* v_inst_3247_, lean_object* v_machine_3248_, lean_object* v_body_3249_){
_start:
{
lean_object* v_close_3251_; lean_object* v_isClosed_3252_; lean_object* v_tryRecv_3253_; lean_object* v___f_3254_; lean_object* v___f_3255_; lean_object* v___f_3256_; lean_object* v___f_3257_; lean_object* v___f_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_close_3251_ = lean_ctor_get(v_inst_3247_, 1);
lean_inc_ref(v_close_3251_);
v_isClosed_3252_ = lean_ctor_get(v_inst_3247_, 2);
lean_inc_ref(v_isClosed_3252_);
v_tryRecv_3253_ = lean_ctor_get(v_inst_3247_, 4);
lean_inc_ref(v_tryRecv_3253_);
lean_dec_ref(v_inst_3247_);
lean_inc_ref(v_machine_3248_);
v___f_3254_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3254_, 0, v_machine_3248_);
lean_inc_ref(v___f_3254_);
v___f_3255_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3255_, 0, v___f_3254_);
lean_inc_n(v_body_3249_, 2);
v___f_3256_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3256_, 0, v_close_3251_);
lean_closure_set(v___f_3256_, 1, v_body_3249_);
lean_closure_set(v___f_3256_, 2, v___f_3255_);
lean_closure_set(v___f_3256_, 3, v___f_3254_);
v___f_3257_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___f_3258_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___lam__1___boxed), 7, 5);
lean_closure_set(v___f_3258_, 0, v_body_3249_);
lean_closure_set(v___f_3258_, 1, v_machine_3248_);
lean_closure_set(v___f_3258_, 2, v_isClosed_3252_);
lean_closure_set(v___f_3258_, 3, v___f_3256_);
lean_closure_set(v___f_3258_, 4, v___f_3257_);
v___x_3259_ = lean_unsigned_to_nat(0u);
v___x_3260_ = 0;
v___x_3261_ = lean_apply_2(v_tryRecv_3253_, v_body_3249_, lean_box(0));
v___x_3262_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3259_, v___x_3260_, v___x_3261_, v___f_3258_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___boxed(lean_object* v_inst_3263_, lean_object* v_machine_3264_, lean_object* v_body_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3263_, v_machine_3264_, v_body_3265_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(lean_object* v_00_u03b2_3268_, lean_object* v_inst_3269_, lean_object* v_machine_3270_, lean_object* v_body_3271_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3269_, v_machine_3270_, v_body_3271_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___boxed(lean_object* v_00_u03b2_3274_, lean_object* v_inst_3275_, lean_object* v_machine_3276_, lean_object* v_body_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody(v_00_u03b2_3274_, v_inst_3275_, v_machine_3276_, v_body_3277_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__0(lean_object* v_machine_3280_, lean_object* v_status_3281_, lean_object* v_handler_3282_, lean_object* v_requestStream_3283_, lean_object* v_timer_3284_, lean_object* v_response_3285_, lean_object* v_inputWanted_3286_, lean_object* v_pendingHead_3287_, lean_object* v_dateSecond_3288_, uint8_t v_requestEnded_3289_, lean_object* v_____r_3290_){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3292_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_3280_, v_status_3281_);
v___x_3293_ = lean_box(0);
v___x_3294_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_abandon___redArg(v_handler_3282_);
v___x_3295_ = 1;
v___x_3296_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3296_, 0, v___x_3292_);
lean_ctor_set(v___x_3296_, 1, v_requestStream_3283_);
lean_ctor_set(v___x_3296_, 2, v_timer_3284_);
lean_ctor_set(v___x_3296_, 3, v_response_3285_);
lean_ctor_set(v___x_3296_, 4, v___x_3293_);
lean_ctor_set(v___x_3296_, 5, v_inputWanted_3286_);
lean_ctor_set(v___x_3296_, 6, v___x_3294_);
lean_ctor_set(v___x_3296_, 7, v_pendingHead_3287_);
lean_ctor_set(v___x_3296_, 8, v_dateSecond_3288_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*9, v_requestEnded_3289_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*9 + 1, v___x_3295_);
v___x_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
v___x_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__0___boxed(lean_object* v_machine_3299_, lean_object* v_status_3300_, lean_object* v_handler_3301_, lean_object* v_requestStream_3302_, lean_object* v_timer_3303_, lean_object* v_response_3304_, lean_object* v_inputWanted_3305_, lean_object* v_pendingHead_3306_, lean_object* v_dateSecond_3307_, lean_object* v_requestEnded_3308_, lean_object* v_____r_3309_, lean_object* v___y_3310_){
_start:
{
uint8_t v_requestEnded_boxed_3311_; lean_object* v_res_3312_; 
v_requestEnded_boxed_3311_ = lean_unbox(v_requestEnded_3308_);
v_res_3312_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__0(v_machine_3299_, v_status_3300_, v_handler_3301_, v_requestStream_3302_, v_timer_3303_, v_response_3304_, v_inputWanted_3305_, v_pendingHead_3306_, v_dateSecond_3307_, v_requestEnded_boxed_3311_, v_____r_3309_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__1(lean_object* v___f_3313_, lean_object* v_x_3314_){
_start:
{
if (lean_obj_tag(v_x_3314_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3324_; 
lean_dec_ref(v___f_3313_);
v_a_3316_ = lean_ctor_get(v_x_3314_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v_x_3314_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3318_ = v_x_3314_;
v_isShared_3319_ = v_isSharedCheck_3324_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v_x_3314_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3324_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
lean_object* v___x_3322_; 
v___x_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
return v___x_3322_;
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3326_; 
v_a_3325_ = lean_ctor_get(v_x_3314_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v_x_3314_, 1);
v___x_3326_ = lean_apply_2(v___f_3313_, v_a_3325_, lean_box(0));
return v___x_3326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__1___boxed(lean_object* v___f_3327_, lean_object* v_x_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__1(v___f_3327_, v_x_3328_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__2(lean_object* v_close_3331_, lean_object* v_val_3332_, lean_object* v___f_3333_, lean_object* v___f_3334_, lean_object* v_x_3335_){
_start:
{
if (lean_obj_tag(v_x_3335_) == 0)
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3345_; 
lean_dec_ref(v___f_3334_);
lean_dec_ref(v___f_3333_);
lean_dec(v_val_3332_);
lean_dec_ref(v_close_3331_);
v_a_3337_ = lean_ctor_get(v_x_3335_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v_x_3335_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3339_ = v_x_3335_;
v_isShared_3340_ = v_isSharedCheck_3345_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v_x_3335_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3345_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3343_; 
v___x_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
return v___x_3343_;
}
}
}
else
{
lean_object* v_a_3346_; uint8_t v___x_3347_; 
v_a_3346_ = lean_ctor_get(v_x_3335_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v_x_3335_, 1);
v___x_3347_ = lean_unbox(v_a_3346_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; lean_object* v___x_3351_; 
lean_dec_ref(v___f_3334_);
v___x_3348_ = lean_unsigned_to_nat(0u);
v___x_3349_ = lean_apply_2(v_close_3331_, v_val_3332_, lean_box(0));
v___x_3350_ = lean_unbox(v_a_3346_);
lean_dec(v_a_3346_);
v___x_3351_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3348_, v___x_3350_, v___x_3349_, v___f_3333_);
return v___x_3351_;
}
else
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
lean_dec(v_a_3346_);
lean_dec_ref(v___f_3333_);
lean_dec(v_val_3332_);
lean_dec_ref(v_close_3331_);
v___x_3352_ = lean_box(0);
v___x_3353_ = lean_apply_2(v___f_3334_, v___x_3352_, lean_box(0));
return v___x_3353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__2___boxed(lean_object* v_close_3354_, lean_object* v_val_3355_, lean_object* v___f_3356_, lean_object* v___f_3357_, lean_object* v_x_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__2(v_close_3354_, v_val_3355_, v___f_3356_, v___f_3357_, v_x_3358_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg(lean_object* v_inst_3361_, lean_object* v_state_3362_, lean_object* v_status_3363_){
_start:
{
lean_object* v_machine_3365_; lean_object* v_requestStream_3366_; lean_object* v_timer_3367_; lean_object* v_response_3368_; lean_object* v_respStream_3369_; lean_object* v_inputWanted_3370_; lean_object* v_handler_3371_; lean_object* v_pendingHead_3372_; lean_object* v_dateSecond_3373_; uint8_t v_requestEnded_3374_; lean_object* v___x_3375_; lean_object* v___f_3376_; 
v_machine_3365_ = lean_ctor_get(v_state_3362_, 0);
lean_inc_ref_n(v_machine_3365_, 2);
v_requestStream_3366_ = lean_ctor_get(v_state_3362_, 1);
lean_inc_ref_n(v_requestStream_3366_, 2);
v_timer_3367_ = lean_ctor_get(v_state_3362_, 2);
lean_inc_n(v_timer_3367_, 2);
v_response_3368_ = lean_ctor_get(v_state_3362_, 3);
lean_inc_ref_n(v_response_3368_, 2);
v_respStream_3369_ = lean_ctor_get(v_state_3362_, 4);
lean_inc(v_respStream_3369_);
v_inputWanted_3370_ = lean_ctor_get(v_state_3362_, 5);
lean_inc_n(v_inputWanted_3370_, 2);
v_handler_3371_ = lean_ctor_get(v_state_3362_, 6);
lean_inc_n(v_handler_3371_, 2);
v_pendingHead_3372_ = lean_ctor_get(v_state_3362_, 7);
lean_inc_n(v_pendingHead_3372_, 2);
v_dateSecond_3373_ = lean_ctor_get(v_state_3362_, 8);
lean_inc_n(v_dateSecond_3373_, 2);
v_requestEnded_3374_ = lean_ctor_get_uint8(v_state_3362_, sizeof(void*)*9);
lean_dec_ref(v_state_3362_);
v___x_3375_ = lean_box(v_requestEnded_3374_);
lean_inc(v_status_3363_);
v___f_3376_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__0___boxed), 12, 10);
lean_closure_set(v___f_3376_, 0, v_machine_3365_);
lean_closure_set(v___f_3376_, 1, v_status_3363_);
lean_closure_set(v___f_3376_, 2, v_handler_3371_);
lean_closure_set(v___f_3376_, 3, v_requestStream_3366_);
lean_closure_set(v___f_3376_, 4, v_timer_3367_);
lean_closure_set(v___f_3376_, 5, v_response_3368_);
lean_closure_set(v___f_3376_, 6, v_inputWanted_3370_);
lean_closure_set(v___f_3376_, 7, v_pendingHead_3372_);
lean_closure_set(v___f_3376_, 8, v_dateSecond_3373_);
lean_closure_set(v___f_3376_, 9, v___x_3375_);
if (lean_obj_tag(v_respStream_3369_) == 1)
{
lean_object* v_val_3377_; lean_object* v_close_3378_; lean_object* v_isClosed_3379_; lean_object* v___f_3380_; lean_object* v___f_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_dec(v_dateSecond_3373_);
lean_dec(v_pendingHead_3372_);
lean_dec(v_handler_3371_);
lean_dec(v_inputWanted_3370_);
lean_dec_ref(v_response_3368_);
lean_dec(v_timer_3367_);
lean_dec_ref(v_requestStream_3366_);
lean_dec_ref(v_machine_3365_);
lean_dec(v_status_3363_);
v_val_3377_ = lean_ctor_get(v_respStream_3369_, 0);
lean_inc_n(v_val_3377_, 2);
lean_dec_ref_known(v_respStream_3369_, 1);
v_close_3378_ = lean_ctor_get(v_inst_3361_, 1);
lean_inc_ref(v_close_3378_);
v_isClosed_3379_ = lean_ctor_get(v_inst_3361_, 2);
lean_inc_ref(v_isClosed_3379_);
lean_dec_ref(v_inst_3361_);
lean_inc_ref(v___f_3376_);
v___f_3380_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_3380_, 0, v___f_3376_);
v___f_3381_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__2___boxed), 6, 4);
lean_closure_set(v___f_3381_, 0, v_close_3378_);
lean_closure_set(v___f_3381_, 1, v_val_3377_);
lean_closure_set(v___f_3381_, 2, v___f_3380_);
lean_closure_set(v___f_3381_, 3, v___f_3376_);
v___x_3382_ = lean_unsigned_to_nat(0u);
v___x_3383_ = 0;
v___x_3384_ = lean_apply_2(v_isClosed_3379_, v_val_3377_, lean_box(0));
v___x_3385_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3382_, v___x_3383_, v___x_3384_, v___f_3381_);
return v___x_3385_;
}
else
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
lean_dec_ref(v___f_3376_);
lean_dec(v_respStream_3369_);
lean_dec_ref(v_inst_3361_);
v___x_3386_ = lean_box(0);
v___x_3387_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___lam__0(v_machine_3365_, v_status_3363_, v_handler_3371_, v_requestStream_3366_, v_timer_3367_, v_response_3368_, v_inputWanted_3370_, v_pendingHead_3372_, v_dateSecond_3373_, v_requestEnded_3374_, v___x_3386_);
return v___x_3387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg___boxed(lean_object* v_inst_3388_, lean_object* v_state_3389_, lean_object* v_status_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg(v_inst_3388_, v_state_3389_, v_status_3390_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith(lean_object* v_00_u03b2_3393_, lean_object* v_inst_3394_, lean_object* v_state_3395_, lean_object* v_status_3396_){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg(v_inst_3394_, v_state_3395_, v_status_3396_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___boxed(lean_object* v_00_u03b2_3399_, lean_object* v_inst_3400_, lean_object* v_state_3401_, lean_object* v_status_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith(v_00_u03b2_3399_, v_inst_3400_, v_state_3401_, v_status_3402_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(lean_object* v_val_3409_, lean_object* v_____r_3410_, lean_object* v_st_3411_){
_start:
{
lean_object* v_machine_3413_; lean_object* v_requestStream_3414_; lean_object* v_timer_3415_; lean_object* v_response_3416_; lean_object* v_respStream_3417_; lean_object* v_inputWanted_3418_; lean_object* v_handler_3419_; lean_object* v_pendingHead_3420_; lean_object* v_dateSecond_3421_; uint8_t v_requestEnded_3422_; uint8_t v_aborted_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3506_; 
v_machine_3413_ = lean_ctor_get(v_st_3411_, 0);
v_requestStream_3414_ = lean_ctor_get(v_st_3411_, 1);
v_timer_3415_ = lean_ctor_get(v_st_3411_, 2);
v_response_3416_ = lean_ctor_get(v_st_3411_, 3);
v_respStream_3417_ = lean_ctor_get(v_st_3411_, 4);
v_inputWanted_3418_ = lean_ctor_get(v_st_3411_, 5);
v_handler_3419_ = lean_ctor_get(v_st_3411_, 6);
v_pendingHead_3420_ = lean_ctor_get(v_st_3411_, 7);
v_dateSecond_3421_ = lean_ctor_get(v_st_3411_, 8);
v_requestEnded_3422_ = lean_ctor_get_uint8(v_st_3411_, sizeof(void*)*9);
v_aborted_3423_ = lean_ctor_get_uint8(v_st_3411_, sizeof(void*)*9 + 1);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_st_3411_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3425_ = v_st_3411_;
v_isShared_3426_ = v_isSharedCheck_3506_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_dateSecond_3421_);
lean_inc(v_pendingHead_3420_);
lean_inc(v_handler_3419_);
lean_inc(v_inputWanted_3418_);
lean_inc(v_respStream_3417_);
lean_inc(v_response_3416_);
lean_inc(v_timer_3415_);
lean_inc(v_requestStream_3414_);
lean_inc(v_machine_3413_);
lean_dec(v_st_3411_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3506_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___y_3428_; lean_object* v_reader_3437_; lean_object* v_state_3438_; 
v_reader_3437_ = lean_ctor_get(v_machine_3413_, 0);
lean_inc_ref(v_reader_3437_);
v_state_3438_ = lean_ctor_get(v_reader_3437_, 0);
lean_inc(v_state_3438_);
if (lean_obj_tag(v_state_3438_) == 6)
{
lean_dec_ref(v_reader_3437_);
lean_dec_ref(v_val_3409_);
v___y_3428_ = v_machine_3413_;
goto v___jp_3427_;
}
else
{
lean_object* v_error_3439_; 
v_error_3439_ = lean_ctor_get(v_machine_3413_, 4);
if (lean_obj_tag(v_error_3439_) == 0)
{
lean_object* v_input_3440_; lean_object* v_writer_3441_; lean_object* v_config_3442_; lean_object* v_events_3443_; lean_object* v_date_3444_; uint8_t v_keepAlive_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3503_; 
lean_inc(v_error_3439_);
v_input_3440_ = lean_ctor_get(v_reader_3437_, 1);
lean_inc_ref(v_input_3440_);
v_writer_3441_ = lean_ctor_get(v_machine_3413_, 1);
v_config_3442_ = lean_ctor_get(v_machine_3413_, 2);
v_events_3443_ = lean_ctor_get(v_machine_3413_, 3);
v_date_3444_ = lean_ctor_get(v_machine_3413_, 5);
v_keepAlive_3445_ = lean_ctor_get_uint8(v_machine_3413_, sizeof(void*)*6);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_machine_3413_);
if (v_isSharedCheck_3503_ == 0)
{
lean_object* v_unused_3504_; lean_object* v_unused_3505_; 
v_unused_3504_ = lean_ctor_get(v_machine_3413_, 4);
lean_dec(v_unused_3504_);
v_unused_3505_ = lean_ctor_get(v_machine_3413_, 0);
lean_dec(v_unused_3505_);
v___x_3447_ = v_machine_3413_;
v_isShared_3448_ = v_isSharedCheck_3503_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_date_3444_);
lean_inc(v_events_3443_);
lean_inc(v_config_3442_);
lean_inc(v_writer_3441_);
lean_dec(v_machine_3413_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3503_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v_messageHead_3449_; lean_object* v_messageCount_3450_; lean_object* v_bodyBytesRead_3451_; lean_object* v_headerBytesRead_3452_; uint8_t v_peerClosed_3453_; uint8_t v_inputStopped_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3500_; 
v_messageHead_3449_ = lean_ctor_get(v_reader_3437_, 2);
v_messageCount_3450_ = lean_ctor_get(v_reader_3437_, 3);
v_bodyBytesRead_3451_ = lean_ctor_get(v_reader_3437_, 4);
v_headerBytesRead_3452_ = lean_ctor_get(v_reader_3437_, 5);
v_peerClosed_3453_ = lean_ctor_get_uint8(v_reader_3437_, sizeof(void*)*6);
v_inputStopped_3454_ = lean_ctor_get_uint8(v_reader_3437_, sizeof(void*)*6 + 1);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_reader_3437_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; lean_object* v_unused_3502_; 
v_unused_3501_ = lean_ctor_get(v_reader_3437_, 1);
lean_dec(v_unused_3501_);
v_unused_3502_ = lean_ctor_get(v_reader_3437_, 0);
lean_dec(v_unused_3502_);
v___x_3456_ = v_reader_3437_;
v_isShared_3457_ = v_isSharedCheck_3500_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_headerBytesRead_3452_);
lean_inc(v_bodyBytesRead_3451_);
lean_inc(v_messageCount_3450_);
lean_inc(v_messageHead_3449_);
lean_dec(v_reader_3437_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3500_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v_array_3458_; lean_object* v_idx_3459_; uint8_t v___x_3460_; lean_object* v___y_3462_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v_array_3458_ = lean_ctor_get(v_input_3440_, 0);
lean_inc_ref(v_array_3458_);
v_idx_3459_ = lean_ctor_get(v_input_3440_, 1);
lean_inc(v_idx_3459_);
lean_dec_ref(v_input_3440_);
v___x_3460_ = 0;
v___x_3491_ = lean_byte_array_size(v_array_3458_);
v___x_3492_ = lean_nat_dec_le(v___x_3491_, v_idx_3459_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3493_ = l_ByteArray_extract(v_array_3458_, v_idx_3459_, v___x_3491_);
lean_dec_ref(v_array_3458_);
v___x_3494_ = lean_unsigned_to_nat(0u);
v___x_3495_ = lean_byte_array_size(v___x_3493_);
v___x_3496_ = lean_byte_array_size(v_val_3409_);
v___x_3497_ = lean_byte_array_copy_slice(v_val_3409_, v___x_3494_, v___x_3493_, v___x_3495_, v___x_3496_, v___x_3492_);
lean_dec_ref(v_val_3409_);
v___x_3498_ = l_ByteArray_mkIterator(v___x_3497_);
v___y_3462_ = v___x_3498_;
goto v___jp_3461_;
}
else
{
lean_object* v___x_3499_; 
lean_dec(v_idx_3459_);
lean_dec_ref(v_array_3458_);
v___x_3499_ = l_ByteArray_mkIterator(v_val_3409_);
v___y_3462_ = v___x_3499_;
goto v___jp_3461_;
}
v___jp_3461_:
{
lean_object* v_maxHeaderBytes_3463_; lean_object* v_maxStartLineLength_3464_; lean_object* v_maxChunkLineLength_3465_; lean_object* v_maxBodySize_3466_; lean_object* v_array_3467_; lean_object* v_idx_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v_maxHeaderBytes_3463_ = lean_ctor_get(v_config_3442_, 2);
v_maxStartLineLength_3464_ = lean_ctor_get(v_config_3442_, 5);
v_maxChunkLineLength_3465_ = lean_ctor_get(v_config_3442_, 15);
v_maxBodySize_3466_ = lean_ctor_get(v_config_3442_, 17);
v_array_3467_ = lean_ctor_get(v___y_3462_, 0);
v_idx_3468_ = lean_ctor_get(v___y_3462_, 1);
v___x_3469_ = lean_nat_add(v_maxBodySize_3466_, v_maxHeaderBytes_3463_);
v___x_3470_ = lean_nat_add(v___x_3469_, v_maxStartLineLength_3464_);
lean_dec(v___x_3469_);
v___x_3471_ = lean_nat_add(v___x_3470_, v_maxChunkLineLength_3465_);
lean_dec(v___x_3470_);
v___x_3472_ = lean_byte_array_size(v_array_3467_);
v___x_3473_ = lean_nat_sub(v___x_3472_, v_idx_3468_);
v___x_3474_ = lean_nat_dec_lt(v___x_3471_, v___x_3473_);
lean_dec(v___x_3473_);
lean_dec(v___x_3471_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3476_; 
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 1, v___y_3462_);
v___x_3476_ = v___x_3456_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_state_3438_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v___y_3462_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_messageHead_3449_);
lean_ctor_set(v_reuseFailAlloc_3480_, 3, v_messageCount_3450_);
lean_ctor_set(v_reuseFailAlloc_3480_, 4, v_bodyBytesRead_3451_);
lean_ctor_set(v_reuseFailAlloc_3480_, 5, v_headerBytesRead_3452_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, sizeof(void*)*6, v_peerClosed_3453_);
lean_ctor_set_uint8(v_reuseFailAlloc_3480_, sizeof(void*)*6 + 1, v_inputStopped_3454_);
v___x_3476_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v_machine_3478_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3476_);
v_machine_3478_ = v___x_3447_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_writer_3441_);
lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_config_3442_);
lean_ctor_set(v_reuseFailAlloc_3479_, 3, v_events_3443_);
lean_ctor_set(v_reuseFailAlloc_3479_, 4, v_error_3439_);
lean_ctor_set(v_reuseFailAlloc_3479_, 5, v_date_3444_);
lean_ctor_set_uint8(v_reuseFailAlloc_3479_, sizeof(void*)*6, v_keepAlive_3445_);
v_machine_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_ctor_set_uint8(v_machine_3478_, sizeof(void*)*6 + 1, v___x_3460_);
v___y_3428_ = v_machine_3478_;
goto v___jp_3427_;
}
}
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3485_; 
lean_dec(v_state_3438_);
v___x_3481_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__0));
v___x_3482_ = lean_array_push(v_events_3443_, v___x_3481_);
v___x_3483_ = lean_box(6);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 1, v___y_3462_);
lean_ctor_set(v___x_3456_, 0, v___x_3483_);
v___x_3485_ = v___x_3456_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3483_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v___y_3462_);
lean_ctor_set(v_reuseFailAlloc_3490_, 2, v_messageHead_3449_);
lean_ctor_set(v_reuseFailAlloc_3490_, 3, v_messageCount_3450_);
lean_ctor_set(v_reuseFailAlloc_3490_, 4, v_bodyBytesRead_3451_);
lean_ctor_set(v_reuseFailAlloc_3490_, 5, v_headerBytesRead_3452_);
lean_ctor_set_uint8(v_reuseFailAlloc_3490_, sizeof(void*)*6, v_peerClosed_3453_);
lean_ctor_set_uint8(v_reuseFailAlloc_3490_, sizeof(void*)*6 + 1, v_inputStopped_3454_);
v___x_3485_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3486_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___closed__1));
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 4, v___x_3486_);
lean_ctor_set(v___x_3447_, 3, v___x_3482_);
lean_ctor_set(v___x_3447_, 0, v___x_3485_);
v___x_3488_ = v___x_3447_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_writer_3441_);
lean_ctor_set(v_reuseFailAlloc_3489_, 2, v_config_3442_);
lean_ctor_set(v_reuseFailAlloc_3489_, 3, v___x_3482_);
lean_ctor_set(v_reuseFailAlloc_3489_, 4, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3489_, 5, v_date_3444_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_ctor_set_uint8(v___x_3488_, sizeof(void*)*6, v___x_3460_);
lean_ctor_set_uint8(v___x_3488_, sizeof(void*)*6 + 1, v___x_3460_);
v___y_3428_ = v___x_3488_;
goto v___jp_3427_;
}
}
}
}
}
}
}
else
{
lean_dec(v_state_3438_);
lean_dec_ref(v_reader_3437_);
lean_dec_ref(v_val_3409_);
v___y_3428_ = v_machine_3413_;
goto v___jp_3427_;
}
}
v___jp_3427_:
{
lean_object* v___x_3430_; 
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___y_3428_);
v___x_3430_ = v___x_3425_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___y_3428_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v_requestStream_3414_);
lean_ctor_set(v_reuseFailAlloc_3436_, 2, v_timer_3415_);
lean_ctor_set(v_reuseFailAlloc_3436_, 3, v_response_3416_);
lean_ctor_set(v_reuseFailAlloc_3436_, 4, v_respStream_3417_);
lean_ctor_set(v_reuseFailAlloc_3436_, 5, v_inputWanted_3418_);
lean_ctor_set(v_reuseFailAlloc_3436_, 6, v_handler_3419_);
lean_ctor_set(v_reuseFailAlloc_3436_, 7, v_pendingHead_3420_);
lean_ctor_set(v_reuseFailAlloc_3436_, 8, v_dateSecond_3421_);
lean_ctor_set_uint8(v_reuseFailAlloc_3436_, sizeof(void*)*9, v_requestEnded_3422_);
lean_ctor_set_uint8(v_reuseFailAlloc_3436_, sizeof(void*)*9 + 1, v_aborted_3423_);
v___x_3430_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
uint8_t v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3431_ = 0;
v___x_3432_ = lean_box(v___x_3431_);
v___x_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3430_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
v___x_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
return v___x_3435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed(lean_object* v_val_3507_, lean_object* v_____r_3508_, lean_object* v_st_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_3507_, v_____r_3508_, v_st_3509_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(lean_object* v_config_3512_, lean_object* v_machine_3513_, lean_object* v_requestStream_3514_, lean_object* v_response_3515_, lean_object* v_respStream_3516_, lean_object* v_inputWanted_3517_, lean_object* v_handler_3518_, lean_object* v_pendingHead_3519_, lean_object* v_dateSecond_3520_, uint8_t v_requestEnded_3521_, uint8_t v_aborted_3522_, lean_object* v___f_3523_, lean_object* v_x_3524_){
_start:
{
if (lean_obj_tag(v_x_3524_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3534_; 
lean_dec_ref(v___f_3523_);
lean_dec(v_dateSecond_3520_);
lean_dec(v_pendingHead_3519_);
lean_dec(v_handler_3518_);
lean_dec(v_inputWanted_3517_);
lean_dec(v_respStream_3516_);
lean_dec_ref(v_response_3515_);
lean_dec_ref(v_requestStream_3514_);
lean_dec_ref(v_machine_3513_);
v_a_3526_ = lean_ctor_get(v_x_3524_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_x_3524_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3528_ = v_x_3524_;
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v_x_3524_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; 
v___x_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
return v___x_3532_;
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v_headerTimeout_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v_a_3535_ = lean_ctor_get(v_x_3524_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v_x_3524_, 1);
v_headerTimeout_3536_ = lean_ctor_get(v_config_3512_, 6);
v___x_3537_ = l_Int_toNat(v_headerTimeout_3536_);
v___x_3538_ = lean_nat_add(v_a_3535_, v___x_3537_);
lean_dec(v___x_3537_);
lean_dec(v_a_3535_);
v___x_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3538_);
v___x_3540_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3540_, 0, v_machine_3513_);
lean_ctor_set(v___x_3540_, 1, v_requestStream_3514_);
lean_ctor_set(v___x_3540_, 2, v___x_3539_);
lean_ctor_set(v___x_3540_, 3, v_response_3515_);
lean_ctor_set(v___x_3540_, 4, v_respStream_3516_);
lean_ctor_set(v___x_3540_, 5, v_inputWanted_3517_);
lean_ctor_set(v___x_3540_, 6, v_handler_3518_);
lean_ctor_set(v___x_3540_, 7, v_pendingHead_3519_);
lean_ctor_set(v___x_3540_, 8, v_dateSecond_3520_);
lean_ctor_set_uint8(v___x_3540_, sizeof(void*)*9, v_requestEnded_3521_);
lean_ctor_set_uint8(v___x_3540_, sizeof(void*)*9 + 1, v_aborted_3522_);
v___x_3541_ = lean_box(0);
v___x_3542_ = lean_apply_3(v___f_3523_, v___x_3541_, v___x_3540_, lean_box(0));
return v___x_3542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed(lean_object* v_config_3543_, lean_object* v_machine_3544_, lean_object* v_requestStream_3545_, lean_object* v_response_3546_, lean_object* v_respStream_3547_, lean_object* v_inputWanted_3548_, lean_object* v_handler_3549_, lean_object* v_pendingHead_3550_, lean_object* v_dateSecond_3551_, lean_object* v_requestEnded_3552_, lean_object* v_aborted_3553_, lean_object* v___f_3554_, lean_object* v_x_3555_, lean_object* v___y_3556_){
_start:
{
uint8_t v_requestEnded_boxed_3557_; uint8_t v_aborted_boxed_3558_; lean_object* v_res_3559_; 
v_requestEnded_boxed_3557_ = lean_unbox(v_requestEnded_3552_);
v_aborted_boxed_3558_ = lean_unbox(v_aborted_3553_);
v_res_3559_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1(v_config_3543_, v_machine_3544_, v_requestStream_3545_, v_response_3546_, v_respStream_3547_, v_inputWanted_3548_, v_handler_3549_, v_pendingHead_3550_, v_dateSecond_3551_, v_requestEnded_boxed_3557_, v_aborted_boxed_3558_, v___f_3554_, v_x_3555_);
lean_dec_ref(v_config_3543_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(lean_object* v_machine_3560_, lean_object* v_requestStream_3561_, lean_object* v_timer_3562_, lean_object* v_response_3563_, lean_object* v_inputWanted_3564_, lean_object* v_handler_3565_, lean_object* v_pendingHead_3566_, lean_object* v_dateSecond_3567_, uint8_t v_requestEnded_3568_, uint8_t v_aborted_3569_, lean_object* v_____r_3570_){
_start:
{
lean_object* v_writer_3572_; lean_object* v_reader_3573_; lean_object* v_config_3574_; lean_object* v_events_3575_; lean_object* v_error_3576_; lean_object* v_date_3577_; uint8_t v_keepAlive_3578_; uint8_t v_pullBodyStalled_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3608_; 
v_writer_3572_ = lean_ctor_get(v_machine_3560_, 1);
v_reader_3573_ = lean_ctor_get(v_machine_3560_, 0);
v_config_3574_ = lean_ctor_get(v_machine_3560_, 2);
v_events_3575_ = lean_ctor_get(v_machine_3560_, 3);
v_error_3576_ = lean_ctor_get(v_machine_3560_, 4);
v_date_3577_ = lean_ctor_get(v_machine_3560_, 5);
v_keepAlive_3578_ = lean_ctor_get_uint8(v_machine_3560_, sizeof(void*)*6);
v_pullBodyStalled_3579_ = lean_ctor_get_uint8(v_machine_3560_, sizeof(void*)*6 + 1);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_machine_3560_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3581_ = v_machine_3560_;
v_isShared_3582_ = v_isSharedCheck_3608_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_date_3577_);
lean_inc(v_error_3576_);
lean_inc(v_events_3575_);
lean_inc(v_config_3574_);
lean_inc(v_writer_3572_);
lean_inc(v_reader_3573_);
lean_dec(v_machine_3560_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3608_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v_userData_3583_; lean_object* v_outputData_3584_; lean_object* v_state_3585_; lean_object* v_knownSize_3586_; lean_object* v_messageHead_3587_; uint8_t v_omitBody_3588_; lean_object* v_userDataBytes_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3607_; 
v_userData_3583_ = lean_ctor_get(v_writer_3572_, 0);
v_outputData_3584_ = lean_ctor_get(v_writer_3572_, 1);
v_state_3585_ = lean_ctor_get(v_writer_3572_, 2);
v_knownSize_3586_ = lean_ctor_get(v_writer_3572_, 3);
v_messageHead_3587_ = lean_ctor_get(v_writer_3572_, 4);
v_omitBody_3588_ = lean_ctor_get_uint8(v_writer_3572_, sizeof(void*)*6 + 1);
v_userDataBytes_3589_ = lean_ctor_get(v_writer_3572_, 5);
v_isSharedCheck_3607_ = !lean_is_exclusive(v_writer_3572_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3591_ = v_writer_3572_;
v_isShared_3592_ = v_isSharedCheck_3607_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_userDataBytes_3589_);
lean_inc(v_messageHead_3587_);
lean_inc(v_knownSize_3586_);
lean_inc(v_state_3585_);
lean_inc(v_outputData_3584_);
lean_inc(v_userData_3583_);
lean_dec(v_writer_3572_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3607_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
uint8_t v___x_3593_; lean_object* v___x_3595_; 
v___x_3593_ = 1;
if (v_isShared_3592_ == 0)
{
v___x_3595_ = v___x_3591_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_userData_3583_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v_outputData_3584_);
lean_ctor_set(v_reuseFailAlloc_3606_, 2, v_state_3585_);
lean_ctor_set(v_reuseFailAlloc_3606_, 3, v_knownSize_3586_);
lean_ctor_set(v_reuseFailAlloc_3606_, 4, v_messageHead_3587_);
lean_ctor_set(v_reuseFailAlloc_3606_, 5, v_userDataBytes_3589_);
lean_ctor_set_uint8(v_reuseFailAlloc_3606_, sizeof(void*)*6 + 1, v_omitBody_3588_);
v___x_3595_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3597_; 
lean_ctor_set_uint8(v___x_3595_, sizeof(void*)*6, v___x_3593_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 1, v___x_3595_);
v___x_3597_ = v___x_3581_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_reader_3573_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3605_, 2, v_config_3574_);
lean_ctor_set(v_reuseFailAlloc_3605_, 3, v_events_3575_);
lean_ctor_set(v_reuseFailAlloc_3605_, 4, v_error_3576_);
lean_ctor_set(v_reuseFailAlloc_3605_, 5, v_date_3577_);
lean_ctor_set_uint8(v_reuseFailAlloc_3605_, sizeof(void*)*6, v_keepAlive_3578_);
lean_ctor_set_uint8(v_reuseFailAlloc_3605_, sizeof(void*)*6 + 1, v_pullBodyStalled_3579_);
v___x_3597_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3598_ = lean_box(0);
v___x_3599_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3599_, 0, v___x_3597_);
lean_ctor_set(v___x_3599_, 1, v_requestStream_3561_);
lean_ctor_set(v___x_3599_, 2, v_timer_3562_);
lean_ctor_set(v___x_3599_, 3, v_response_3563_);
lean_ctor_set(v___x_3599_, 4, v___x_3598_);
lean_ctor_set(v___x_3599_, 5, v_inputWanted_3564_);
lean_ctor_set(v___x_3599_, 6, v_handler_3565_);
lean_ctor_set(v___x_3599_, 7, v_pendingHead_3566_);
lean_ctor_set(v___x_3599_, 8, v_dateSecond_3567_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*9, v_requestEnded_3568_);
lean_ctor_set_uint8(v___x_3599_, sizeof(void*)*9 + 1, v_aborted_3569_);
v___x_3600_ = 0;
v___x_3601_ = lean_box(v___x_3600_);
v___x_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3599_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
v___x_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3603_);
return v___x_3604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed(lean_object* v_machine_3609_, lean_object* v_requestStream_3610_, lean_object* v_timer_3611_, lean_object* v_response_3612_, lean_object* v_inputWanted_3613_, lean_object* v_handler_3614_, lean_object* v_pendingHead_3615_, lean_object* v_dateSecond_3616_, lean_object* v_requestEnded_3617_, lean_object* v_aborted_3618_, lean_object* v_____r_3619_, lean_object* v___y_3620_){
_start:
{
uint8_t v_requestEnded_boxed_3621_; uint8_t v_aborted_boxed_3622_; lean_object* v_res_3623_; 
v_requestEnded_boxed_3621_ = lean_unbox(v_requestEnded_3617_);
v_aborted_boxed_3622_ = lean_unbox(v_aborted_3618_);
v_res_3623_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_3609_, v_requestStream_3610_, v_timer_3611_, v_response_3612_, v_inputWanted_3613_, v_handler_3614_, v_pendingHead_3615_, v_dateSecond_3616_, v_requestEnded_boxed_3621_, v_aborted_boxed_3622_, v_____r_3619_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(lean_object* v___f_3624_, lean_object* v_x_3625_){
_start:
{
if (lean_obj_tag(v_x_3625_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v___f_3624_);
v_a_3627_ = lean_ctor_get(v_x_3625_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_x_3625_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3629_ = v_x_3625_;
v_isShared_3630_ = v_isSharedCheck_3635_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v_x_3625_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3635_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3633_; 
v___x_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
return v___x_3633_;
}
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3637_; 
v_a_3636_ = lean_ctor_get(v_x_3625_, 0);
lean_inc(v_a_3636_);
lean_dec_ref_known(v_x_3625_, 1);
v___x_3637_ = lean_apply_2(v___f_3624_, v_a_3636_, lean_box(0));
return v___x_3637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed(lean_object* v___f_3638_, lean_object* v_x_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3(v___f_3638_, v_x_3639_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(lean_object* v_close_3642_, lean_object* v_val_3643_, lean_object* v___f_3644_, lean_object* v___f_3645_, lean_object* v_x_3646_){
_start:
{
if (lean_obj_tag(v_x_3646_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3656_; 
lean_dec_ref(v___f_3645_);
lean_dec_ref(v___f_3644_);
lean_dec(v_val_3643_);
lean_dec_ref(v_close_3642_);
v_a_3648_ = lean_ctor_get(v_x_3646_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_x_3646_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3650_ = v_x_3646_;
v_isShared_3651_ = v_isSharedCheck_3656_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v_x_3646_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3656_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
lean_object* v___x_3654_; 
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
return v___x_3654_;
}
}
}
else
{
lean_object* v_a_3657_; uint8_t v___x_3658_; 
v_a_3657_ = lean_ctor_get(v_x_3646_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v_x_3646_, 1);
v___x_3658_ = lean_unbox(v_a_3657_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; lean_object* v___x_3662_; 
lean_dec_ref(v___f_3645_);
v___x_3659_ = lean_unsigned_to_nat(0u);
v___x_3660_ = lean_apply_2(v_close_3642_, v_val_3643_, lean_box(0));
v___x_3661_ = lean_unbox(v_a_3657_);
lean_dec(v_a_3657_);
v___x_3662_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3659_, v___x_3661_, v___x_3660_, v___f_3644_);
return v___x_3662_;
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
lean_dec(v_a_3657_);
lean_dec_ref(v___f_3644_);
lean_dec(v_val_3643_);
lean_dec_ref(v_close_3642_);
v___x_3663_ = lean_box(0);
v___x_3664_ = lean_apply_2(v___f_3645_, v___x_3663_, lean_box(0));
return v___x_3664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed(lean_object* v_close_3665_, lean_object* v_val_3666_, lean_object* v___f_3667_, lean_object* v___f_3668_, lean_object* v_x_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4(v_close_3665_, v_val_3666_, v___f_3667_, v___f_3668_, v_x_3669_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(lean_object* v_inst_3672_, lean_object* v_handler_3673_, lean_object* v_x_3674_){
_start:
{
if (lean_obj_tag(v_x_3674_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3677_; 
v_a_3676_ = lean_ctor_get(v_x_3674_, 0);
lean_inc(v_a_3676_);
lean_dec_ref_known(v_x_3674_, 1);
v___x_3677_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_3672_, v_handler_3673_, v_a_3676_);
return v___x_3677_;
}
else
{
lean_object* v___x_3678_; 
lean_dec(v_handler_3673_);
lean_dec_ref(v_inst_3672_);
v___x_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3678_, 0, v_x_3674_);
return v___x_3678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed(lean_object* v_inst_3679_, lean_object* v_handler_3680_, lean_object* v_x_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6(v_inst_3679_, v_handler_3680_, v_x_3681_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(lean_object* v_st_3684_, lean_object* v_____r_3685_){
_start:
{
uint8_t v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3687_ = 0;
v___x_3688_ = lean_box(v___x_3687_);
v___x_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3689_, 0, v_st_3684_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
v___x_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed(lean_object* v_st_3692_, lean_object* v_____r_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_3692_, v_____r_3693_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(lean_object* v_x_3696_){
_start:
{
if (lean_obj_tag(v_x_3696_) == 0)
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3706_; 
v_a_3698_ = lean_ctor_get(v_x_3696_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_x_3696_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3700_ = v_x_3696_;
v_isShared_3701_ = v_isSharedCheck_3706_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v_x_3696_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3706_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
lean_object* v___x_3704_; 
v___x_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
return v___x_3704_;
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3737_; 
v_a_3707_ = lean_ctor_get(v_x_3696_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v_x_3696_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3709_ = v_x_3696_;
v_isShared_3710_ = v_isSharedCheck_3737_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v_x_3696_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3737_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v_machine_3711_; lean_object* v_requestStream_3712_; lean_object* v_timer_3713_; lean_object* v_response_3714_; lean_object* v_respStream_3715_; lean_object* v_inputWanted_3716_; lean_object* v_pendingHead_3717_; lean_object* v_dateSecond_3718_; uint8_t v_requestEnded_3719_; uint8_t v_aborted_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3735_; 
v_machine_3711_ = lean_ctor_get(v_a_3707_, 0);
v_requestStream_3712_ = lean_ctor_get(v_a_3707_, 1);
v_timer_3713_ = lean_ctor_get(v_a_3707_, 2);
v_response_3714_ = lean_ctor_get(v_a_3707_, 3);
v_respStream_3715_ = lean_ctor_get(v_a_3707_, 4);
v_inputWanted_3716_ = lean_ctor_get(v_a_3707_, 5);
v_pendingHead_3717_ = lean_ctor_get(v_a_3707_, 7);
v_dateSecond_3718_ = lean_ctor_get(v_a_3707_, 8);
v_requestEnded_3719_ = lean_ctor_get_uint8(v_a_3707_, sizeof(void*)*9);
v_aborted_3720_ = lean_ctor_get_uint8(v_a_3707_, sizeof(void*)*9 + 1);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_a_3707_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; 
v_unused_3736_ = lean_ctor_get(v_a_3707_, 6);
lean_dec(v_unused_3736_);
v___x_3722_ = v_a_3707_;
v_isShared_3723_ = v_isSharedCheck_3735_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_dateSecond_3718_);
lean_inc(v_pendingHead_3717_);
lean_inc(v_inputWanted_3716_);
lean_inc(v_respStream_3715_);
lean_inc(v_response_3714_);
lean_inc(v_timer_3713_);
lean_inc(v_requestStream_3712_);
lean_inc(v_machine_3711_);
lean_dec(v_a_3707_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3735_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3724_; lean_object* v___x_3726_; 
v___x_3724_ = lean_box(0);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 6, v___x_3724_);
v___x_3726_ = v___x_3722_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_machine_3711_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_requestStream_3712_);
lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_timer_3713_);
lean_ctor_set(v_reuseFailAlloc_3734_, 3, v_response_3714_);
lean_ctor_set(v_reuseFailAlloc_3734_, 4, v_respStream_3715_);
lean_ctor_set(v_reuseFailAlloc_3734_, 5, v_inputWanted_3716_);
lean_ctor_set(v_reuseFailAlloc_3734_, 6, v___x_3724_);
lean_ctor_set(v_reuseFailAlloc_3734_, 7, v_pendingHead_3717_);
lean_ctor_set(v_reuseFailAlloc_3734_, 8, v_dateSecond_3718_);
lean_ctor_set_uint8(v_reuseFailAlloc_3734_, sizeof(void*)*9, v_requestEnded_3719_);
lean_ctor_set_uint8(v_reuseFailAlloc_3734_, sizeof(void*)*9 + 1, v_aborted_3720_);
v___x_3726_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
uint8_t v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3727_ = 0;
v___x_3728_ = lean_box(v___x_3727_);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3726_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v___x_3729_);
v___x_3731_ = v___x_3709_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
return v___x_3732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8___boxed(lean_object* v_x_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__8(v_x_3738_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(lean_object* v_inst_3741_, lean_object* v_state_3742_, lean_object* v___f_3743_, lean_object* v_x_3744_){
_start:
{
if (lean_obj_tag(v_x_3744_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3754_; 
lean_dec_ref(v___f_3743_);
lean_dec_ref(v_state_3742_);
lean_dec_ref(v_inst_3741_);
v_a_3746_ = lean_ctor_get(v_x_3744_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v_x_3744_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3748_ = v_x_3744_;
v_isShared_3749_ = v_isSharedCheck_3754_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v_x_3744_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3754_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
lean_object* v___x_3752_; 
v___x_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
return v___x_3752_;
}
}
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
lean_dec_ref_known(v_x_3744_, 1);
v___x_3755_ = lean_box(52);
v___x_3756_ = lean_unsigned_to_nat(0u);
v___x_3757_ = 0;
v___x_3758_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg(v_inst_3741_, v_state_3742_, v___x_3755_);
v___x_3759_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3756_, v___x_3757_, v___x_3758_, v___f_3743_);
return v___x_3759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed(lean_object* v_inst_3760_, lean_object* v_state_3761_, lean_object* v___f_3762_, lean_object* v_x_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7(v_inst_3760_, v_state_3761_, v___f_3762_, v_x_3763_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(uint8_t v___y_3766_, lean_object* v_x_3767_){
_start:
{
if (lean_obj_tag(v_x_3767_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3777_; 
v_a_3769_ = lean_ctor_get(v_x_3767_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_x_3767_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3771_ = v_x_3767_;
v_isShared_3772_ = v_isSharedCheck_3777_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v_x_3767_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3777_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3775_; 
v___x_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3774_);
return v___x_3775_;
}
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3797_; 
v_a_3778_ = lean_ctor_get(v_x_3767_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_x_3767_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3780_ = v_x_3767_;
v_isShared_3781_ = v_isSharedCheck_3797_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v_x_3767_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3797_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v_fst_3782_; lean_object* v_snd_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3796_; 
v_fst_3782_ = lean_ctor_get(v_a_3778_, 0);
v_snd_3783_ = lean_ctor_get(v_a_3778_, 1);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_a_3778_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3785_ = v_a_3778_;
v_isShared_3786_ = v_isSharedCheck_3796_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_snd_3783_);
lean_inc(v_fst_3782_);
lean_dec(v_a_3778_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3796_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3787_ = lean_box(v___y_3766_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 1, v___x_3787_);
lean_ctor_set(v___x_3785_, 0, v_snd_3783_);
v___x_3789_ = v___x_3785_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_snd_3783_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3790_; lean_object* v___x_3792_; 
v___x_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3790_, 0, v_fst_3782_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 0, v___x_3790_);
v___x_3792_ = v___x_3780_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3790_);
v___x_3792_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
return v___x_3793_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed(lean_object* v___y_3798_, lean_object* v_x_3799_, lean_object* v___y_3800_){
_start:
{
uint8_t v___y_8600__boxed_3801_; lean_object* v_res_3802_; 
v___y_8600__boxed_3801_ = lean_unbox(v___y_3798_);
v_res_3802_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9(v___y_8600__boxed_3801_, v_x_3799_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(lean_object* v_requestStream_3803_, lean_object* v_timer_3804_, lean_object* v_response_3805_, lean_object* v_inputWanted_3806_, lean_object* v_handler_3807_, lean_object* v_pendingHead_3808_, lean_object* v_dateSecond_3809_, uint8_t v_requestEnded_3810_, uint8_t v_aborted_3811_, lean_object* v_____x_3812_){
_start:
{
lean_object* v_snd_3814_; lean_object* v_fst_3815_; lean_object* v_fst_3816_; lean_object* v_snd_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3827_; 
v_snd_3814_ = lean_ctor_get(v_____x_3812_, 1);
lean_inc(v_snd_3814_);
v_fst_3815_ = lean_ctor_get(v_____x_3812_, 0);
lean_inc(v_fst_3815_);
lean_dec_ref(v_____x_3812_);
v_fst_3816_ = lean_ctor_get(v_snd_3814_, 0);
v_snd_3817_ = lean_ctor_get(v_snd_3814_, 1);
v_isSharedCheck_3827_ = !lean_is_exclusive(v_snd_3814_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3819_ = v_snd_3814_;
v_isShared_3820_ = v_isSharedCheck_3827_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_snd_3817_);
lean_inc(v_fst_3816_);
lean_dec(v_snd_3814_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3827_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; lean_object* v___x_3823_; 
v___x_3821_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_3821_, 0, v_fst_3815_);
lean_ctor_set(v___x_3821_, 1, v_requestStream_3803_);
lean_ctor_set(v___x_3821_, 2, v_timer_3804_);
lean_ctor_set(v___x_3821_, 3, v_response_3805_);
lean_ctor_set(v___x_3821_, 4, v_fst_3816_);
lean_ctor_set(v___x_3821_, 5, v_inputWanted_3806_);
lean_ctor_set(v___x_3821_, 6, v_handler_3807_);
lean_ctor_set(v___x_3821_, 7, v_pendingHead_3808_);
lean_ctor_set(v___x_3821_, 8, v_dateSecond_3809_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*9, v_requestEnded_3810_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*9 + 1, v_aborted_3811_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3821_);
v___x_3823_ = v___x_3819_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_snd_3817_);
v___x_3823_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
v___x_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
return v___x_3825_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed(lean_object* v_requestStream_3828_, lean_object* v_timer_3829_, lean_object* v_response_3830_, lean_object* v_inputWanted_3831_, lean_object* v_handler_3832_, lean_object* v_pendingHead_3833_, lean_object* v_dateSecond_3834_, lean_object* v_requestEnded_3835_, lean_object* v_aborted_3836_, lean_object* v_____x_3837_, lean_object* v___y_3838_){
_start:
{
uint8_t v_requestEnded_boxed_3839_; uint8_t v_aborted_boxed_3840_; lean_object* v_res_3841_; 
v_requestEnded_boxed_3839_ = lean_unbox(v_requestEnded_3835_);
v_aborted_boxed_3840_ = lean_unbox(v_aborted_3836_);
v_res_3841_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10(v_requestStream_3828_, v_timer_3829_, v_response_3830_, v_inputWanted_3831_, v_handler_3832_, v_pendingHead_3833_, v_dateSecond_3834_, v_requestEnded_boxed_3839_, v_aborted_boxed_3840_, v_____x_3837_);
return v_res_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(lean_object* v___f_3842_, lean_object* v_x_3843_){
_start:
{
if (lean_obj_tag(v_x_3843_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3853_; 
lean_dec_ref(v___f_3842_);
v_a_3845_ = lean_ctor_get(v_x_3843_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_x_3843_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3847_ = v_x_3843_;
v_isShared_3848_ = v_isSharedCheck_3853_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v_x_3843_);
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
lean_object* v_a_3854_; lean_object* v___x_3855_; 
v_a_3854_ = lean_ctor_get(v_x_3843_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v_x_3843_, 1);
v___x_3855_ = lean_apply_2(v___f_3842_, v_a_3854_, lean_box(0));
return v___x_3855_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed(lean_object* v___f_3856_, lean_object* v_x_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11(v___f_3856_, v_x_3857_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(lean_object* v_snd_3860_, uint8_t v___x_3861_, lean_object* v_fst_3862_, lean_object* v_x_3863_){
_start:
{
if (lean_obj_tag(v_x_3863_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3873_; 
lean_dec_ref(v_fst_3862_);
lean_dec(v_snd_3860_);
v_a_3865_ = lean_ctor_get(v_x_3863_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_x_3863_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3867_ = v_x_3863_;
v_isShared_3868_ = v_isSharedCheck_3873_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v_x_3863_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3873_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
return v___x_3871_;
}
}
}
else
{
lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3884_; 
v_isSharedCheck_3884_ = !lean_is_exclusive(v_x_3863_);
if (v_isSharedCheck_3884_ == 0)
{
lean_object* v_unused_3885_; 
v_unused_3885_ = lean_ctor_get(v_x_3863_, 0);
lean_dec(v_unused_3885_);
v___x_3875_ = v_x_3863_;
v_isShared_3876_ = v_isSharedCheck_3884_;
goto v_resetjp_3874_;
}
else
{
lean_dec(v_x_3863_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3884_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3881_; 
v___x_3877_ = lean_box(v___x_3861_);
v___x_3878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3878_, 0, v_snd_3860_);
lean_ctor_set(v___x_3878_, 1, v___x_3877_);
v___x_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3879_, 0, v_fst_3862_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
if (v_isShared_3876_ == 0)
{
lean_ctor_set(v___x_3875_, 0, v___x_3879_);
v___x_3881_ = v___x_3875_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed(lean_object* v_snd_3886_, lean_object* v___x_3887_, lean_object* v_fst_3888_, lean_object* v_x_3889_, lean_object* v___y_3890_){
_start:
{
uint8_t v___x_8733__boxed_3891_; lean_object* v_res_3892_; 
v___x_8733__boxed_3891_ = lean_unbox(v___x_3887_);
v_res_3892_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13(v_snd_3886_, v___x_8733__boxed_3891_, v_fst_3888_, v_x_3889_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(lean_object* v_inst_3893_, lean_object* v_handler_3894_, uint8_t v___y_3895_, lean_object* v___f_3896_, lean_object* v_x_3897_){
_start:
{
if (lean_obj_tag(v_x_3897_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_a_3899_ = lean_ctor_get(v_x_3897_, 0);
lean_inc(v_a_3899_);
lean_dec_ref_known(v_x_3897_, 1);
v___x_3900_ = lean_unsigned_to_nat(0u);
v___x_3901_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_3893_, v_handler_3894_, v_a_3899_);
v___x_3902_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3900_, v___y_3895_, v___x_3901_, v___f_3896_);
return v___x_3902_;
}
else
{
lean_object* v___x_3903_; 
lean_dec_ref(v___f_3896_);
lean_dec(v_handler_3894_);
lean_dec_ref(v_inst_3893_);
v___x_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3903_, 0, v_x_3897_);
return v___x_3903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed(lean_object* v_inst_3904_, lean_object* v_handler_3905_, lean_object* v___y_3906_, lean_object* v___f_3907_, lean_object* v_x_3908_, lean_object* v___y_3909_){
_start:
{
uint8_t v___y_8791__boxed_3910_; lean_object* v_res_3911_; 
v___y_8791__boxed_3910_ = lean_unbox(v___y_3906_);
v_res_3911_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12(v_inst_3904_, v_handler_3905_, v___y_8791__boxed_3910_, v___f_3907_, v_x_3908_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(uint8_t v___y_3912_, lean_object* v___f_3913_, uint8_t v___x_3914_, lean_object* v_inst_3915_, lean_object* v_handler_3916_, lean_object* v_inst_3917_, lean_object* v___f_3918_, lean_object* v___f_3919_, lean_object* v_x_3920_){
_start:
{
if (lean_obj_tag(v_x_3920_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3930_; 
lean_dec_ref(v___f_3919_);
lean_dec_ref(v___f_3918_);
lean_dec_ref(v_inst_3917_);
lean_dec(v_handler_3916_);
lean_dec_ref(v_inst_3915_);
lean_dec_ref(v___f_3913_);
v_a_3922_ = lean_ctor_get(v_x_3920_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_x_3920_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3924_ = v_x_3920_;
v_isShared_3925_ = v_isSharedCheck_3930_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v_x_3920_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3930_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3928_; 
v___x_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
return v___x_3928_;
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3964_; 
v_a_3931_ = lean_ctor_get(v_x_3920_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v_x_3920_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3933_ = v_x_3920_;
v_isShared_3934_ = v_isSharedCheck_3964_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v_x_3920_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3964_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v_snd_3935_; 
v_snd_3935_ = lean_ctor_get(v_a_3931_, 1);
lean_inc(v_snd_3935_);
if (lean_obj_tag(v_snd_3935_) == 0)
{
lean_object* v_fst_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3951_; 
lean_dec_ref(v___f_3919_);
lean_dec_ref(v___f_3918_);
lean_dec_ref(v_inst_3917_);
lean_dec(v_handler_3916_);
lean_dec_ref(v_inst_3915_);
v_fst_3936_ = lean_ctor_get(v_a_3931_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v_a_3931_);
if (v_isSharedCheck_3951_ == 0)
{
lean_object* v_unused_3952_; 
v_unused_3952_ = lean_ctor_get(v_a_3931_, 1);
lean_dec(v_unused_3952_);
v___x_3938_ = v_a_3931_;
v_isShared_3939_ = v_isSharedCheck_3951_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_fst_3936_);
lean_dec(v_a_3931_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3951_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3940_; lean_object* v___x_3942_; 
v___x_3940_ = lean_box(v___y_3912_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 1, v___x_3940_);
lean_ctor_set(v___x_3938_, 0, v_snd_3935_);
v___x_3942_ = v___x_3938_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_snd_3935_);
lean_ctor_set(v_reuseFailAlloc_3950_, 1, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3946_; 
v___x_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3943_, 0, v_fst_3936_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = lean_unsigned_to_nat(0u);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v___x_3943_);
v___x_3946_ = v___x_3933_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3943_);
v___x_3946_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
v___x_3948_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3944_, v___y_3912_, v___x_3947_, v___f_3913_);
return v___x_3948_;
}
}
}
}
else
{
lean_object* v_fst_3953_; lean_object* v_val_3954_; lean_object* v___x_3955_; lean_object* v___f_3956_; lean_object* v___x_3957_; lean_object* v___f_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
lean_del_object(v___x_3933_);
lean_dec_ref(v___f_3913_);
v_fst_3953_ = lean_ctor_get(v_a_3931_, 0);
lean_inc_n(v_fst_3953_, 2);
lean_dec(v_a_3931_);
v_val_3954_ = lean_ctor_get(v_snd_3935_, 0);
lean_inc(v_val_3954_);
v___x_3955_ = lean_box(v___x_3914_);
v___f_3956_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__13___boxed), 5, 3);
lean_closure_set(v___f_3956_, 0, v_snd_3935_);
lean_closure_set(v___f_3956_, 1, v___x_3955_);
lean_closure_set(v___f_3956_, 2, v_fst_3953_);
v___x_3957_ = lean_box(v___y_3912_);
v___f_3958_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__12___boxed), 6, 4);
lean_closure_set(v___f_3958_, 0, v_inst_3915_);
lean_closure_set(v___f_3958_, 1, v_handler_3916_);
lean_closure_set(v___f_3958_, 2, v___x_3957_);
lean_closure_set(v___f_3958_, 3, v___f_3956_);
v___x_3959_ = lean_unsigned_to_nat(0u);
v___x_3960_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg(v_inst_3917_, v_fst_3953_, v_val_3954_);
v___x_3961_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3959_, v___y_3912_, v___x_3960_, v___f_3918_);
v___x_3962_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3959_, v___y_3912_, v___x_3961_, v___f_3958_);
v___x_3963_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3959_, v___y_3912_, v___x_3962_, v___f_3919_);
return v___x_3963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed(lean_object* v___y_3965_, lean_object* v___f_3966_, lean_object* v___x_3967_, lean_object* v_inst_3968_, lean_object* v_handler_3969_, lean_object* v_inst_3970_, lean_object* v___f_3971_, lean_object* v___f_3972_, lean_object* v_x_3973_, lean_object* v___y_3974_){
_start:
{
uint8_t v___y_8816__boxed_3975_; uint8_t v___x_8818__boxed_3976_; lean_object* v_res_3977_; 
v___y_8816__boxed_3975_ = lean_unbox(v___y_3965_);
v___x_8818__boxed_3976_ = lean_unbox(v___x_3967_);
v_res_3977_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14(v___y_8816__boxed_3975_, v___f_3966_, v___x_8818__boxed_3976_, v_inst_3968_, v_handler_3969_, v_inst_3970_, v___f_3971_, v___f_3972_, v_x_3973_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(uint8_t v___y_3978_, uint8_t v___x_3979_, lean_object* v_inst_3980_, lean_object* v_handler_3981_, lean_object* v_inst_3982_, lean_object* v___f_3983_, lean_object* v_a_3984_, lean_object* v_x_3985_){
_start:
{
if (lean_obj_tag(v_x_3985_) == 0)
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3995_; 
lean_dec_ref(v_a_3984_);
lean_dec_ref(v___f_3983_);
lean_dec_ref(v_inst_3982_);
lean_dec(v_handler_3981_);
lean_dec_ref(v_inst_3980_);
v_a_3987_ = lean_ctor_get(v_x_3985_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_x_3985_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3989_ = v_x_3985_;
v_isShared_3990_ = v_isSharedCheck_3995_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v_x_3985_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3995_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3993_; 
v___x_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
return v___x_3993_;
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v_machine_3997_; lean_object* v_requestStream_3998_; lean_object* v_timer_3999_; lean_object* v_response_4000_; lean_object* v_inputWanted_4001_; lean_object* v_handler_4002_; lean_object* v_pendingHead_4003_; lean_object* v_dateSecond_4004_; uint8_t v_requestEnded_4005_; uint8_t v_aborted_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___f_4009_; lean_object* v___f_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___f_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v_a_3996_ = lean_ctor_get(v_x_3985_, 0);
lean_inc(v_a_3996_);
lean_dec_ref_known(v_x_3985_, 1);
v_machine_3997_ = lean_ctor_get(v_a_3996_, 0);
lean_inc_ref(v_machine_3997_);
v_requestStream_3998_ = lean_ctor_get(v_a_3996_, 1);
lean_inc_ref(v_requestStream_3998_);
v_timer_3999_ = lean_ctor_get(v_a_3996_, 2);
lean_inc(v_timer_3999_);
v_response_4000_ = lean_ctor_get(v_a_3996_, 3);
lean_inc_ref(v_response_4000_);
v_inputWanted_4001_ = lean_ctor_get(v_a_3996_, 5);
lean_inc(v_inputWanted_4001_);
v_handler_4002_ = lean_ctor_get(v_a_3996_, 6);
lean_inc(v_handler_4002_);
v_pendingHead_4003_ = lean_ctor_get(v_a_3996_, 7);
lean_inc(v_pendingHead_4003_);
v_dateSecond_4004_ = lean_ctor_get(v_a_3996_, 8);
lean_inc(v_dateSecond_4004_);
v_requestEnded_4005_ = lean_ctor_get_uint8(v_a_3996_, sizeof(void*)*9);
v_aborted_4006_ = lean_ctor_get_uint8(v_a_3996_, sizeof(void*)*9 + 1);
lean_dec(v_a_3996_);
v___x_4007_ = lean_box(v_requestEnded_4005_);
v___x_4008_ = lean_box(v_aborted_4006_);
v___f_4009_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__10___boxed), 11, 9);
lean_closure_set(v___f_4009_, 0, v_requestStream_3998_);
lean_closure_set(v___f_4009_, 1, v_timer_3999_);
lean_closure_set(v___f_4009_, 2, v_response_4000_);
lean_closure_set(v___f_4009_, 3, v_inputWanted_4001_);
lean_closure_set(v___f_4009_, 4, v_handler_4002_);
lean_closure_set(v___f_4009_, 5, v_pendingHead_4003_);
lean_closure_set(v___f_4009_, 6, v_dateSecond_4004_);
lean_closure_set(v___f_4009_, 7, v___x_4007_);
lean_closure_set(v___f_4009_, 8, v___x_4008_);
v___f_4010_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__11___boxed), 3, 1);
lean_closure_set(v___f_4010_, 0, v___f_4009_);
v___x_4011_ = lean_box(v___y_3978_);
v___x_4012_ = lean_box(v___x_3979_);
lean_inc_ref(v_inst_3982_);
lean_inc_ref(v___f_4010_);
v___f_4013_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__14___boxed), 10, 8);
lean_closure_set(v___f_4013_, 0, v___x_4011_);
lean_closure_set(v___f_4013_, 1, v___f_4010_);
lean_closure_set(v___f_4013_, 2, v___x_4012_);
lean_closure_set(v___f_4013_, 3, v_inst_3980_);
lean_closure_set(v___f_4013_, 4, v_handler_3981_);
lean_closure_set(v___f_4013_, 5, v_inst_3982_);
lean_closure_set(v___f_4013_, 6, v___f_3983_);
lean_closure_set(v___f_4013_, 7, v___f_4010_);
v___x_4014_ = lean_unsigned_to_nat(0u);
v___x_4015_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg(v_inst_3982_, v_machine_3997_, v_a_3984_);
v___x_4016_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4014_, v___y_3978_, v___x_4015_, v___f_4013_);
return v___x_4016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed(lean_object* v___y_4017_, lean_object* v___x_4018_, lean_object* v_inst_4019_, lean_object* v_handler_4020_, lean_object* v_inst_4021_, lean_object* v___f_4022_, lean_object* v_a_4023_, lean_object* v_x_4024_, lean_object* v___y_4025_){
_start:
{
uint8_t v___y_8929__boxed_4026_; uint8_t v___x_8930__boxed_4027_; lean_object* v_res_4028_; 
v___y_8929__boxed_4026_ = lean_unbox(v___y_4017_);
v___x_8930__boxed_4027_ = lean_unbox(v___x_4018_);
v_res_4028_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15(v___y_8929__boxed_4026_, v___x_8930__boxed_4027_, v_inst_4019_, v_handler_4020_, v_inst_4021_, v___f_4022_, v_a_4023_, v_x_4024_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(lean_object* v_machine_4029_, lean_object* v_requestStream_4030_, lean_object* v_timer_4031_, lean_object* v_response_4032_, lean_object* v_respStream_4033_, lean_object* v_inputWanted_4034_, lean_object* v___x_4035_, lean_object* v_pendingHead_4036_, lean_object* v_dateSecond_4037_, uint8_t v_requestEnded_4038_, uint8_t v_aborted_4039_, uint8_t v___x_4040_, lean_object* v_x_4041_){
_start:
{
if (lean_obj_tag(v_x_4041_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4051_; 
lean_dec(v_dateSecond_4037_);
lean_dec(v_pendingHead_4036_);
lean_dec(v___x_4035_);
lean_dec(v_inputWanted_4034_);
lean_dec(v_respStream_4033_);
lean_dec_ref(v_response_4032_);
lean_dec(v_timer_4031_);
lean_dec_ref(v_requestStream_4030_);
lean_dec_ref(v_machine_4029_);
v_a_4043_ = lean_ctor_get(v_x_4041_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v_x_4041_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4045_ = v_x_4041_;
v_isShared_4046_ = v_isSharedCheck_4051_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v_x_4041_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4051_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4049_; 
v___x_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
return v___x_4049_;
}
}
}
else
{
lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4064_; 
v_isSharedCheck_4064_ = !lean_is_exclusive(v_x_4041_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; 
v_unused_4065_ = lean_ctor_get(v_x_4041_, 0);
lean_dec(v_unused_4065_);
v___x_4053_ = v_x_4041_;
v_isShared_4054_ = v_isSharedCheck_4064_;
goto v_resetjp_4052_;
}
else
{
lean_dec(v_x_4041_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4064_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4061_; 
v___x_4055_ = lean_box(52);
v___x_4056_ = l_Std_Http_Protocol_H1_Machine_closeWithError(v_machine_4029_, v___x_4055_);
v___x_4057_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_4057_, 0, v___x_4056_);
lean_ctor_set(v___x_4057_, 1, v_requestStream_4030_);
lean_ctor_set(v___x_4057_, 2, v_timer_4031_);
lean_ctor_set(v___x_4057_, 3, v_response_4032_);
lean_ctor_set(v___x_4057_, 4, v_respStream_4033_);
lean_ctor_set(v___x_4057_, 5, v_inputWanted_4034_);
lean_ctor_set(v___x_4057_, 6, v___x_4035_);
lean_ctor_set(v___x_4057_, 7, v_pendingHead_4036_);
lean_ctor_set(v___x_4057_, 8, v_dateSecond_4037_);
lean_ctor_set_uint8(v___x_4057_, sizeof(void*)*9, v_requestEnded_4038_);
lean_ctor_set_uint8(v___x_4057_, sizeof(void*)*9 + 1, v_aborted_4039_);
v___x_4058_ = lean_box(v___x_4040_);
v___x_4059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4057_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v___x_4059_);
v___x_4061_ = v___x_4053_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
lean_object* v___x_4062_; 
v___x_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
return v___x_4062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed(lean_object* v_machine_4066_, lean_object* v_requestStream_4067_, lean_object* v_timer_4068_, lean_object* v_response_4069_, lean_object* v_respStream_4070_, lean_object* v_inputWanted_4071_, lean_object* v___x_4072_, lean_object* v_pendingHead_4073_, lean_object* v_dateSecond_4074_, lean_object* v_requestEnded_4075_, lean_object* v_aborted_4076_, lean_object* v___x_4077_, lean_object* v_x_4078_, lean_object* v___y_4079_){
_start:
{
uint8_t v_requestEnded_boxed_4080_; uint8_t v_aborted_boxed_4081_; uint8_t v___x_8994__boxed_4082_; lean_object* v_res_4083_; 
v_requestEnded_boxed_4080_ = lean_unbox(v_requestEnded_4075_);
v_aborted_boxed_4081_ = lean_unbox(v_aborted_4076_);
v___x_8994__boxed_4082_ = lean_unbox(v___x_4077_);
v_res_4083_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16(v_machine_4066_, v_requestStream_4067_, v_timer_4068_, v_response_4069_, v_respStream_4070_, v_inputWanted_4071_, v___x_4072_, v_pendingHead_4073_, v_dateSecond_4074_, v_requestEnded_boxed_4080_, v_aborted_boxed_4081_, v___x_8994__boxed_4082_, v_x_4078_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(uint16_t v___x_4086_, lean_object* v_inst_4087_, lean_object* v_handler_4088_, uint8_t v___x_4089_, lean_object* v___f_4090_, lean_object* v_____r_4091_){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4093_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___closed__0));
v___x_4094_ = lean_uint16_to_nat(v___x_4086_);
v___x_4095_ = l_Nat_reprFast(v___x_4094_);
v___x_4096_ = lean_string_append(v___x_4093_, v___x_4095_);
lean_dec_ref(v___x_4095_);
v___x_4097_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___closed__1));
v___x_4098_ = lean_string_append(v___x_4096_, v___x_4097_);
v___x_4099_ = lean_mk_io_user_error(v___x_4098_);
v___x_4100_ = lean_unsigned_to_nat(0u);
v___x_4101_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_4087_, v_handler_4088_, v___x_4099_);
v___x_4102_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4100_, v___x_4089_, v___x_4101_, v___f_4090_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed(lean_object* v___x_4103_, lean_object* v_inst_4104_, lean_object* v_handler_4105_, lean_object* v___x_4106_, lean_object* v___f_4107_, lean_object* v_____r_4108_, lean_object* v___y_4109_){
_start:
{
uint16_t v___x_9056__boxed_4110_; uint8_t v___x_9058__boxed_4111_; lean_object* v_res_4112_; 
v___x_9056__boxed_4110_ = lean_unbox(v___x_4103_);
v___x_9058__boxed_4111_ = lean_unbox(v___x_4106_);
v_res_4112_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17(v___x_9056__boxed_4110_, v_inst_4104_, v_handler_4105_, v___x_9058__boxed_4111_, v___f_4107_, v_____r_4108_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19(lean_object* v_close_4113_, lean_object* v_body_4114_, uint8_t v___x_4115_, lean_object* v___f_4116_, lean_object* v___f_4117_, lean_object* v_x_4118_){
_start:
{
if (lean_obj_tag(v_x_4118_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4128_; 
lean_dec_ref(v___f_4117_);
lean_dec_ref(v___f_4116_);
lean_dec(v_body_4114_);
lean_dec_ref(v_close_4113_);
v_a_4120_ = lean_ctor_get(v_x_4118_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v_x_4118_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4122_ = v_x_4118_;
v_isShared_4123_ = v_isSharedCheck_4128_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v_x_4118_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4128_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
lean_object* v___x_4126_; 
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
return v___x_4126_;
}
}
}
else
{
lean_object* v_a_4129_; uint8_t v___x_4130_; 
v_a_4129_ = lean_ctor_get(v_x_4118_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v_x_4118_, 1);
v___x_4130_ = lean_unbox(v_a_4129_);
lean_dec(v_a_4129_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
lean_dec_ref(v___f_4117_);
v___x_4131_ = lean_unsigned_to_nat(0u);
v___x_4132_ = lean_apply_2(v_close_4113_, v_body_4114_, lean_box(0));
v___x_4133_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4131_, v___x_4115_, v___x_4132_, v___f_4116_);
return v___x_4133_;
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec_ref(v___f_4116_);
lean_dec(v_body_4114_);
lean_dec_ref(v_close_4113_);
v___x_4134_ = lean_box(0);
v___x_4135_ = lean_apply_2(v___f_4117_, v___x_4134_, lean_box(0));
return v___x_4135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19___boxed(lean_object* v_close_4136_, lean_object* v_body_4137_, lean_object* v___x_4138_, lean_object* v___f_4139_, lean_object* v___f_4140_, lean_object* v_x_4141_, lean_object* v___y_4142_){
_start:
{
uint8_t v___x_9096__boxed_4143_; lean_object* v_res_4144_; 
v___x_9096__boxed_4143_ = lean_unbox(v___x_4138_);
v_res_4144_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19(v_close_4136_, v_body_4137_, v___x_9096__boxed_4143_, v___f_4139_, v___f_4140_, v_x_4141_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(lean_object* v_state_4145_, lean_object* v_____r_4146_){
_start:
{
uint8_t v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4148_ = 0;
v___x_4149_ = lean_box(v___x_4148_);
v___x_4150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4150_, 0, v_state_4145_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
v___x_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
v___x_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed(lean_object* v_state_4153_, lean_object* v_____r_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18(v_state_4153_, v_____r_4154_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__21(lean_object* v_close_4157_, lean_object* v_body_4158_, lean_object* v___f_4159_, lean_object* v___f_4160_, lean_object* v_x_4161_){
_start:
{
if (lean_obj_tag(v_x_4161_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4171_; 
lean_dec_ref(v___f_4160_);
lean_dec_ref(v___f_4159_);
lean_dec(v_body_4158_);
lean_dec_ref(v_close_4157_);
v_a_4163_ = lean_ctor_get(v_x_4161_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v_x_4161_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4165_ = v_x_4161_;
v_isShared_4166_ = v_isSharedCheck_4171_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v_x_4161_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4171_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4163_);
v___x_4168_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
lean_object* v___x_4169_; 
v___x_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
return v___x_4169_;
}
}
}
else
{
lean_object* v_a_4172_; uint8_t v___x_4173_; 
v_a_4172_ = lean_ctor_get(v_x_4161_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v_x_4161_, 1);
v___x_4173_ = lean_unbox(v_a_4172_);
if (v___x_4173_ == 0)
{
lean_object* v___x_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; lean_object* v___x_4177_; 
lean_dec_ref(v___f_4160_);
v___x_4174_ = lean_unsigned_to_nat(0u);
v___x_4175_ = lean_apply_2(v_close_4157_, v_body_4158_, lean_box(0));
v___x_4176_ = lean_unbox(v_a_4172_);
lean_dec(v_a_4172_);
v___x_4177_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4174_, v___x_4176_, v___x_4175_, v___f_4159_);
return v___x_4177_;
}
else
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
lean_dec(v_a_4172_);
lean_dec_ref(v___f_4159_);
lean_dec(v_body_4158_);
lean_dec_ref(v_close_4157_);
v___x_4178_ = lean_box(0);
v___x_4179_ = lean_apply_2(v___f_4160_, v___x_4178_, lean_box(0));
return v___x_4179_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__21___boxed(lean_object* v_close_4180_, lean_object* v_body_4181_, lean_object* v___f_4182_, lean_object* v___f_4183_, lean_object* v_x_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__21(v_close_4180_, v_body_4181_, v___f_4182_, v___f_4183_, v_x_4184_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20(lean_object* v_state_4187_, lean_object* v_x_4188_){
_start:
{
if (lean_obj_tag(v_x_4188_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4198_; 
lean_dec_ref(v_state_4187_);
v_a_4190_ = lean_ctor_get(v_x_4188_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v_x_4188_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4192_ = v_x_4188_;
v_isShared_4193_ = v_isSharedCheck_4198_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v_x_4188_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4198_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4196_; 
v___x_4196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
return v___x_4196_;
}
}
}
else
{
lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4209_; 
v_isSharedCheck_4209_ = !lean_is_exclusive(v_x_4188_);
if (v_isSharedCheck_4209_ == 0)
{
lean_object* v_unused_4210_; 
v_unused_4210_ = lean_ctor_get(v_x_4188_, 0);
lean_dec(v_unused_4210_);
v___x_4200_ = v_x_4188_;
v_isShared_4201_ = v_isSharedCheck_4209_;
goto v_resetjp_4199_;
}
else
{
lean_dec(v_x_4188_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4209_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
uint8_t v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4206_; 
v___x_4202_ = 0;
v___x_4203_ = lean_box(v___x_4202_);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v_state_4187_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 0, v___x_4204_);
v___x_4206_ = v___x_4200_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4204_);
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
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20___boxed(lean_object* v_state_4211_, lean_object* v_x_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20(v_state_4211_, v_x_4212_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__22(lean_object* v_x_4215_){
_start:
{
if (lean_obj_tag(v_x_4215_) == 0)
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4225_; 
v_a_4217_ = lean_ctor_get(v_x_4215_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v_x_4215_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4219_ = v_x_4215_;
v_isShared_4220_ = v_isSharedCheck_4225_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v_x_4215_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4225_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
lean_object* v___x_4223_; 
v___x_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4222_);
return v___x_4223_;
}
}
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4237_; 
v_a_4226_ = lean_ctor_get(v_x_4215_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_x_4215_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4228_ = v_x_4215_;
v_isShared_4229_ = v_isSharedCheck_4237_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v_x_4215_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4237_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
uint8_t v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4234_; 
v___x_4230_ = 0;
v___x_4231_ = lean_box(v___x_4230_);
v___x_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4232_, 0, v_a_4226_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___x_4232_);
v___x_4234_ = v___x_4228_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4232_);
v___x_4234_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
lean_object* v___x_4235_; 
v___x_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4234_);
return v___x_4235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__22___boxed(lean_object* v_x_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__22(v_x_4238_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__23(lean_object* v_inst_4241_, lean_object* v_state_4242_, lean_object* v___f_4243_, lean_object* v_x_4244_){
_start:
{
if (lean_obj_tag(v_x_4244_) == 0)
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4254_; 
lean_dec_ref(v___f_4243_);
lean_dec_ref(v_state_4242_);
lean_dec_ref(v_inst_4241_);
v_a_4246_ = lean_ctor_get(v_x_4244_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_x_4244_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4248_ = v_x_4244_;
v_isShared_4249_ = v_isSharedCheck_4254_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v_x_4244_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4254_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
lean_object* v___x_4252_; 
v___x_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4251_);
return v___x_4252_;
}
}
}
else
{
lean_object* v___x_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
lean_dec_ref_known(v_x_4244_, 1);
v___x_4255_ = lean_box(31);
v___x_4256_ = lean_unsigned_to_nat(0u);
v___x_4257_ = 0;
v___x_4258_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg(v_inst_4241_, v_state_4242_, v___x_4255_);
v___x_4259_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4256_, v___x_4257_, v___x_4258_, v___f_4243_);
return v___x_4259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__23___boxed(lean_object* v_inst_4260_, lean_object* v_state_4261_, lean_object* v___f_4262_, lean_object* v_x_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__23(v_inst_4260_, v_state_4261_, v___f_4262_, v_x_4263_);
return v_res_4265_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__3(void){
_start:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4269_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__2));
v___x_4270_ = lean_mk_io_user_error(v___x_4269_);
return v___x_4270_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__5(void){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4272_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__4));
v___x_4273_ = lean_mk_io_user_error(v___x_4272_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(lean_object* v_inst_4274_, lean_object* v_inst_4275_, lean_object* v_handler_4276_, lean_object* v_config_4277_, lean_object* v_outbox_4278_, lean_object* v_event_4279_, lean_object* v_state_4280_){
_start:
{
lean_object* v___y_4283_; lean_object* v___y_4284_; uint8_t v___y_4285_; lean_object* v_val_4286_; 
switch(lean_obj_tag(v_event_4279_))
{
case 0:
{
lean_object* v_x_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4381_; 
lean_dec_ref(v_outbox_4278_);
lean_dec(v_handler_4276_);
lean_dec_ref(v_inst_4275_);
lean_dec_ref(v_inst_4274_);
v_x_4289_ = lean_ctor_get(v_event_4279_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v_event_4279_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4291_ = v_event_4279_;
v_isShared_4292_ = v_isSharedCheck_4381_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_x_4289_);
lean_dec(v_event_4279_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4381_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
if (lean_obj_tag(v_x_4289_) == 0)
{
lean_object* v_machine_4293_; lean_object* v_reader_4294_; lean_object* v_requestStream_4295_; lean_object* v_timer_4296_; lean_object* v_response_4297_; lean_object* v_respStream_4298_; lean_object* v_inputWanted_4299_; lean_object* v_handler_4300_; lean_object* v_pendingHead_4301_; lean_object* v_dateSecond_4302_; uint8_t v_requestEnded_4303_; uint8_t v_aborted_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4347_; 
lean_dec_ref(v_config_4277_);
v_machine_4293_ = lean_ctor_get(v_state_4280_, 0);
lean_inc_ref(v_machine_4293_);
v_reader_4294_ = lean_ctor_get(v_machine_4293_, 0);
lean_inc_ref(v_reader_4294_);
v_requestStream_4295_ = lean_ctor_get(v_state_4280_, 1);
v_timer_4296_ = lean_ctor_get(v_state_4280_, 2);
v_response_4297_ = lean_ctor_get(v_state_4280_, 3);
v_respStream_4298_ = lean_ctor_get(v_state_4280_, 4);
v_inputWanted_4299_ = lean_ctor_get(v_state_4280_, 5);
v_handler_4300_ = lean_ctor_get(v_state_4280_, 6);
v_pendingHead_4301_ = lean_ctor_get(v_state_4280_, 7);
v_dateSecond_4302_ = lean_ctor_get(v_state_4280_, 8);
v_requestEnded_4303_ = lean_ctor_get_uint8(v_state_4280_, sizeof(void*)*9);
v_aborted_4304_ = lean_ctor_get_uint8(v_state_4280_, sizeof(void*)*9 + 1);
v_isSharedCheck_4347_ = !lean_is_exclusive(v_state_4280_);
if (v_isSharedCheck_4347_ == 0)
{
lean_object* v_unused_4348_; 
v_unused_4348_ = lean_ctor_get(v_state_4280_, 0);
lean_dec(v_unused_4348_);
v___x_4306_ = v_state_4280_;
v_isShared_4307_ = v_isSharedCheck_4347_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_dateSecond_4302_);
lean_inc(v_pendingHead_4301_);
lean_inc(v_handler_4300_);
lean_inc(v_inputWanted_4299_);
lean_inc(v_respStream_4298_);
lean_inc(v_response_4297_);
lean_inc(v_timer_4296_);
lean_inc(v_requestStream_4295_);
lean_dec(v_state_4280_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4347_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v_writer_4308_; lean_object* v_config_4309_; lean_object* v_events_4310_; lean_object* v_error_4311_; lean_object* v_date_4312_; uint8_t v_keepAlive_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4345_; 
v_writer_4308_ = lean_ctor_get(v_machine_4293_, 1);
v_config_4309_ = lean_ctor_get(v_machine_4293_, 2);
v_events_4310_ = lean_ctor_get(v_machine_4293_, 3);
v_error_4311_ = lean_ctor_get(v_machine_4293_, 4);
v_date_4312_ = lean_ctor_get(v_machine_4293_, 5);
v_keepAlive_4313_ = lean_ctor_get_uint8(v_machine_4293_, sizeof(void*)*6);
v_isSharedCheck_4345_ = !lean_is_exclusive(v_machine_4293_);
if (v_isSharedCheck_4345_ == 0)
{
lean_object* v_unused_4346_; 
v_unused_4346_ = lean_ctor_get(v_machine_4293_, 0);
lean_dec(v_unused_4346_);
v___x_4315_ = v_machine_4293_;
v_isShared_4316_ = v_isSharedCheck_4345_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_date_4312_);
lean_inc(v_error_4311_);
lean_inc(v_events_4310_);
lean_inc(v_config_4309_);
lean_inc(v_writer_4308_);
lean_dec(v_machine_4293_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4345_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v_state_4317_; lean_object* v_input_4318_; lean_object* v_messageHead_4319_; lean_object* v_messageCount_4320_; lean_object* v_bodyBytesRead_4321_; lean_object* v_headerBytesRead_4322_; uint8_t v_inputStopped_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4344_; 
v_state_4317_ = lean_ctor_get(v_reader_4294_, 0);
v_input_4318_ = lean_ctor_get(v_reader_4294_, 1);
v_messageHead_4319_ = lean_ctor_get(v_reader_4294_, 2);
v_messageCount_4320_ = lean_ctor_get(v_reader_4294_, 3);
v_bodyBytesRead_4321_ = lean_ctor_get(v_reader_4294_, 4);
v_headerBytesRead_4322_ = lean_ctor_get(v_reader_4294_, 5);
v_inputStopped_4323_ = lean_ctor_get_uint8(v_reader_4294_, sizeof(void*)*6 + 1);
v_isSharedCheck_4344_ = !lean_is_exclusive(v_reader_4294_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4325_ = v_reader_4294_;
v_isShared_4326_ = v_isSharedCheck_4344_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_headerBytesRead_4322_);
lean_inc(v_bodyBytesRead_4321_);
lean_inc(v_messageCount_4320_);
lean_inc(v_messageHead_4319_);
lean_inc(v_input_4318_);
lean_inc(v_state_4317_);
lean_dec(v_reader_4294_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4344_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
uint8_t v___x_4327_; lean_object* v___x_4329_; 
v___x_4327_ = 1;
if (v_isShared_4326_ == 0)
{
v___x_4329_ = v___x_4325_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_state_4317_);
lean_ctor_set(v_reuseFailAlloc_4343_, 1, v_input_4318_);
lean_ctor_set(v_reuseFailAlloc_4343_, 2, v_messageHead_4319_);
lean_ctor_set(v_reuseFailAlloc_4343_, 3, v_messageCount_4320_);
lean_ctor_set(v_reuseFailAlloc_4343_, 4, v_bodyBytesRead_4321_);
lean_ctor_set(v_reuseFailAlloc_4343_, 5, v_headerBytesRead_4322_);
lean_ctor_set_uint8(v_reuseFailAlloc_4343_, sizeof(void*)*6 + 1, v_inputStopped_4323_);
v___x_4329_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
uint8_t v___x_4330_; lean_object* v___x_4332_; 
lean_ctor_set_uint8(v___x_4329_, sizeof(void*)*6, v___x_4327_);
v___x_4330_ = 0;
if (v_isShared_4316_ == 0)
{
lean_ctor_set(v___x_4315_, 0, v___x_4329_);
v___x_4332_ = v___x_4315_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4329_);
lean_ctor_set(v_reuseFailAlloc_4342_, 1, v_writer_4308_);
lean_ctor_set(v_reuseFailAlloc_4342_, 2, v_config_4309_);
lean_ctor_set(v_reuseFailAlloc_4342_, 3, v_events_4310_);
lean_ctor_set(v_reuseFailAlloc_4342_, 4, v_error_4311_);
lean_ctor_set(v_reuseFailAlloc_4342_, 5, v_date_4312_);
lean_ctor_set_uint8(v_reuseFailAlloc_4342_, sizeof(void*)*6, v_keepAlive_4313_);
v___x_4332_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
lean_object* v___x_4334_; 
lean_ctor_set_uint8(v___x_4332_, sizeof(void*)*6 + 1, v___x_4330_);
if (v_isShared_4307_ == 0)
{
lean_ctor_set(v___x_4306_, 0, v___x_4332_);
v___x_4334_ = v___x_4306_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v___x_4332_);
lean_ctor_set(v_reuseFailAlloc_4341_, 1, v_requestStream_4295_);
lean_ctor_set(v_reuseFailAlloc_4341_, 2, v_timer_4296_);
lean_ctor_set(v_reuseFailAlloc_4341_, 3, v_response_4297_);
lean_ctor_set(v_reuseFailAlloc_4341_, 4, v_respStream_4298_);
lean_ctor_set(v_reuseFailAlloc_4341_, 5, v_inputWanted_4299_);
lean_ctor_set(v_reuseFailAlloc_4341_, 6, v_handler_4300_);
lean_ctor_set(v_reuseFailAlloc_4341_, 7, v_pendingHead_4301_);
lean_ctor_set(v_reuseFailAlloc_4341_, 8, v_dateSecond_4302_);
lean_ctor_set_uint8(v_reuseFailAlloc_4341_, sizeof(void*)*9, v_requestEnded_4303_);
lean_ctor_set_uint8(v_reuseFailAlloc_4341_, sizeof(void*)*9 + 1, v_aborted_4304_);
v___x_4334_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4338_; 
v___x_4335_ = lean_box(v___x_4330_);
v___x_4336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4334_);
lean_ctor_set(v___x_4336_, 1, v___x_4335_);
if (v_isShared_4292_ == 0)
{
lean_ctor_set_tag(v___x_4291_, 1);
lean_ctor_set(v___x_4291_, 0, v___x_4336_);
v___x_4338_ = v___x_4291_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4336_);
v___x_4338_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
lean_object* v___x_4339_; 
v___x_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4338_);
return v___x_4339_;
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
lean_object* v_val_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4380_; 
v_val_4349_ = lean_ctor_get(v_x_4289_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v_x_4289_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4351_ = v_x_4289_;
v_isShared_4352_ = v_isSharedCheck_4380_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_val_4349_);
lean_dec(v_x_4289_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4380_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v_machine_4353_; lean_object* v_requestStream_4354_; lean_object* v_timer_4355_; lean_object* v_response_4356_; lean_object* v_respStream_4357_; lean_object* v_inputWanted_4358_; lean_object* v_handler_4359_; lean_object* v_pendingHead_4360_; lean_object* v_dateSecond_4361_; uint8_t v_requestEnded_4362_; uint8_t v_aborted_4363_; lean_object* v___f_4364_; 
v_machine_4353_ = lean_ctor_get(v_state_4280_, 0);
v_requestStream_4354_ = lean_ctor_get(v_state_4280_, 1);
v_timer_4355_ = lean_ctor_get(v_state_4280_, 2);
v_response_4356_ = lean_ctor_get(v_state_4280_, 3);
v_respStream_4357_ = lean_ctor_get(v_state_4280_, 4);
v_inputWanted_4358_ = lean_ctor_get(v_state_4280_, 5);
v_handler_4359_ = lean_ctor_get(v_state_4280_, 6);
v_pendingHead_4360_ = lean_ctor_get(v_state_4280_, 7);
v_dateSecond_4361_ = lean_ctor_get(v_state_4280_, 8);
v_requestEnded_4362_ = lean_ctor_get_uint8(v_state_4280_, sizeof(void*)*9);
v_aborted_4363_ = lean_ctor_get_uint8(v_state_4280_, sizeof(void*)*9 + 1);
lean_inc(v_val_4349_);
v___f_4364_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_4364_, 0, v_val_4349_);
if (lean_obj_tag(v_timer_4355_) == 0)
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___f_4367_; lean_object* v___x_4368_; uint8_t v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4372_; 
lean_inc(v_dateSecond_4361_);
lean_inc(v_pendingHead_4360_);
lean_inc(v_handler_4359_);
lean_inc(v_inputWanted_4358_);
lean_inc(v_respStream_4357_);
lean_inc_ref(v_response_4356_);
lean_inc_ref(v_requestStream_4354_);
lean_inc_ref(v_machine_4353_);
lean_dec(v_val_4349_);
lean_dec_ref(v_state_4280_);
v___x_4365_ = lean_box(v_requestEnded_4362_);
v___x_4366_ = lean_box(v_aborted_4363_);
v___f_4367_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__1___boxed), 14, 12);
lean_closure_set(v___f_4367_, 0, v_config_4277_);
lean_closure_set(v___f_4367_, 1, v_machine_4353_);
lean_closure_set(v___f_4367_, 2, v_requestStream_4354_);
lean_closure_set(v___f_4367_, 3, v_response_4356_);
lean_closure_set(v___f_4367_, 4, v_respStream_4357_);
lean_closure_set(v___f_4367_, 5, v_inputWanted_4358_);
lean_closure_set(v___f_4367_, 6, v_handler_4359_);
lean_closure_set(v___f_4367_, 7, v_pendingHead_4360_);
lean_closure_set(v___f_4367_, 8, v_dateSecond_4361_);
lean_closure_set(v___f_4367_, 9, v___x_4365_);
lean_closure_set(v___f_4367_, 10, v___x_4366_);
lean_closure_set(v___f_4367_, 11, v___f_4364_);
v___x_4368_ = lean_unsigned_to_nat(0u);
v___x_4369_ = 0;
v___x_4370_ = lean_io_mono_ms_now();
if (v_isShared_4352_ == 0)
{
lean_ctor_set(v___x_4351_, 0, v___x_4370_);
v___x_4372_ = v___x_4351_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v___x_4370_);
v___x_4372_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
lean_object* v___x_4374_; 
if (v_isShared_4292_ == 0)
{
lean_ctor_set(v___x_4291_, 0, v___x_4372_);
v___x_4374_ = v___x_4291_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___x_4372_);
v___x_4374_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4375_; 
v___x_4375_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4368_, v___x_4369_, v___x_4374_, v___f_4367_);
return v___x_4375_;
}
}
}
else
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
lean_dec_ref(v___f_4364_);
lean_del_object(v___x_4351_);
lean_del_object(v___x_4291_);
lean_dec_ref(v_config_4277_);
v___x_4378_ = lean_box(0);
v___x_4379_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__0(v_val_4349_, v___x_4378_, v_state_4280_);
return v___x_4379_;
}
}
}
}
}
case 1:
{
lean_object* v_x_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4491_; 
lean_dec_ref(v_outbox_4278_);
lean_dec_ref(v_config_4277_);
lean_dec(v_handler_4276_);
lean_dec_ref(v_inst_4274_);
v_x_4382_ = lean_ctor_get(v_event_4279_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v_event_4279_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4384_ = v_event_4279_;
v_isShared_4385_ = v_isSharedCheck_4491_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_x_4382_);
lean_dec(v_event_4279_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4491_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
if (lean_obj_tag(v_x_4382_) == 0)
{
lean_object* v_machine_4386_; lean_object* v_requestStream_4387_; lean_object* v_timer_4388_; lean_object* v_response_4389_; lean_object* v_respStream_4390_; lean_object* v_inputWanted_4391_; lean_object* v_handler_4392_; lean_object* v_pendingHead_4393_; lean_object* v_dateSecond_4394_; uint8_t v_requestEnded_4395_; uint8_t v_aborted_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___f_4399_; 
lean_del_object(v___x_4384_);
v_machine_4386_ = lean_ctor_get(v_state_4280_, 0);
lean_inc_ref_n(v_machine_4386_, 2);
v_requestStream_4387_ = lean_ctor_get(v_state_4280_, 1);
lean_inc_ref_n(v_requestStream_4387_, 2);
v_timer_4388_ = lean_ctor_get(v_state_4280_, 2);
lean_inc_n(v_timer_4388_, 2);
v_response_4389_ = lean_ctor_get(v_state_4280_, 3);
lean_inc_ref_n(v_response_4389_, 2);
v_respStream_4390_ = lean_ctor_get(v_state_4280_, 4);
lean_inc(v_respStream_4390_);
v_inputWanted_4391_ = lean_ctor_get(v_state_4280_, 5);
lean_inc_n(v_inputWanted_4391_, 2);
v_handler_4392_ = lean_ctor_get(v_state_4280_, 6);
lean_inc_n(v_handler_4392_, 2);
v_pendingHead_4393_ = lean_ctor_get(v_state_4280_, 7);
lean_inc_n(v_pendingHead_4393_, 2);
v_dateSecond_4394_ = lean_ctor_get(v_state_4280_, 8);
lean_inc_n(v_dateSecond_4394_, 2);
v_requestEnded_4395_ = lean_ctor_get_uint8(v_state_4280_, sizeof(void*)*9);
v_aborted_4396_ = lean_ctor_get_uint8(v_state_4280_, sizeof(void*)*9 + 1);
lean_dec_ref(v_state_4280_);
v___x_4397_ = lean_box(v_requestEnded_4395_);
v___x_4398_ = lean_box(v_aborted_4396_);
v___f_4399_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2___boxed), 12, 10);
lean_closure_set(v___f_4399_, 0, v_machine_4386_);
lean_closure_set(v___f_4399_, 1, v_requestStream_4387_);
lean_closure_set(v___f_4399_, 2, v_timer_4388_);
lean_closure_set(v___f_4399_, 3, v_response_4389_);
lean_closure_set(v___f_4399_, 4, v_inputWanted_4391_);
lean_closure_set(v___f_4399_, 5, v_handler_4392_);
lean_closure_set(v___f_4399_, 6, v_pendingHead_4393_);
lean_closure_set(v___f_4399_, 7, v_dateSecond_4394_);
lean_closure_set(v___f_4399_, 8, v___x_4397_);
lean_closure_set(v___f_4399_, 9, v___x_4398_);
if (lean_obj_tag(v_respStream_4390_) == 1)
{
lean_object* v_val_4400_; lean_object* v_close_4401_; lean_object* v_isClosed_4402_; lean_object* v___f_4403_; lean_object* v___f_4404_; lean_object* v___x_4405_; uint8_t v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
lean_dec(v_dateSecond_4394_);
lean_dec(v_pendingHead_4393_);
lean_dec(v_handler_4392_);
lean_dec(v_inputWanted_4391_);
lean_dec_ref(v_response_4389_);
lean_dec(v_timer_4388_);
lean_dec_ref(v_requestStream_4387_);
lean_dec_ref(v_machine_4386_);
v_val_4400_ = lean_ctor_get(v_respStream_4390_, 0);
lean_inc_n(v_val_4400_, 2);
lean_dec_ref_known(v_respStream_4390_, 1);
v_close_4401_ = lean_ctor_get(v_inst_4275_, 1);
lean_inc_ref(v_close_4401_);
v_isClosed_4402_ = lean_ctor_get(v_inst_4275_, 2);
lean_inc_ref(v_isClosed_4402_);
lean_dec_ref(v_inst_4275_);
lean_inc_ref(v___f_4399_);
v___f_4403_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4403_, 0, v___f_4399_);
v___f_4404_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__4___boxed), 6, 4);
lean_closure_set(v___f_4404_, 0, v_close_4401_);
lean_closure_set(v___f_4404_, 1, v_val_4400_);
lean_closure_set(v___f_4404_, 2, v___f_4403_);
lean_closure_set(v___f_4404_, 3, v___f_4399_);
v___x_4405_ = lean_unsigned_to_nat(0u);
v___x_4406_ = 0;
v___x_4407_ = lean_apply_2(v_isClosed_4402_, v_val_4400_, lean_box(0));
v___x_4408_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4405_, v___x_4406_, v___x_4407_, v___f_4404_);
return v___x_4408_;
}
else
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
lean_dec_ref(v___f_4399_);
lean_dec(v_respStream_4390_);
lean_dec_ref(v_inst_4275_);
v___x_4409_ = lean_box(0);
v___x_4410_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__2(v_machine_4386_, v_requestStream_4387_, v_timer_4388_, v_response_4389_, v_inputWanted_4391_, v_handler_4392_, v_pendingHead_4393_, v_dateSecond_4394_, v_requestEnded_4395_, v_aborted_4396_, v___x_4409_);
return v___x_4410_;
}
}
else
{
lean_object* v_val_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4490_; 
lean_dec_ref(v_inst_4275_);
v_val_4411_ = lean_ctor_get(v_x_4382_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v_x_4382_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4413_ = v_x_4382_;
v_isShared_4414_ = v_isSharedCheck_4490_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_val_4411_);
lean_dec(v_x_4382_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4490_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v_machine_4415_; lean_object* v_requestStream_4416_; lean_object* v_timer_4417_; lean_object* v_response_4418_; lean_object* v_respStream_4419_; lean_object* v_inputWanted_4420_; lean_object* v_handler_4421_; lean_object* v_pendingHead_4422_; lean_object* v_dateSecond_4423_; uint8_t v_requestEnded_4424_; uint8_t v_aborted_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4489_; 
v_machine_4415_ = lean_ctor_get(v_state_4280_, 0);
v_requestStream_4416_ = lean_ctor_get(v_state_4280_, 1);
v_timer_4417_ = lean_ctor_get(v_state_4280_, 2);
v_response_4418_ = lean_ctor_get(v_state_4280_, 3);
v_respStream_4419_ = lean_ctor_get(v_state_4280_, 4);
v_inputWanted_4420_ = lean_ctor_get(v_state_4280_, 5);
v_handler_4421_ = lean_ctor_get(v_state_4280_, 6);
v_pendingHead_4422_ = lean_ctor_get(v_state_4280_, 7);
v_dateSecond_4423_ = lean_ctor_get(v_state_4280_, 8);
v_requestEnded_4424_ = lean_ctor_get_uint8(v_state_4280_, sizeof(void*)*9);
v_aborted_4425_ = lean_ctor_get_uint8(v_state_4280_, sizeof(void*)*9 + 1);
v_isSharedCheck_4489_ = !lean_is_exclusive(v_state_4280_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4427_ = v_state_4280_;
v_isShared_4428_ = v_isSharedCheck_4489_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_dateSecond_4423_);
lean_inc(v_pendingHead_4422_);
lean_inc(v_handler_4421_);
lean_inc(v_inputWanted_4420_);
lean_inc(v_respStream_4419_);
lean_inc(v_response_4418_);
lean_inc(v_timer_4417_);
lean_inc(v_requestStream_4416_);
lean_inc(v_machine_4415_);
lean_dec(v_state_4280_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4489_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___y_4430_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; uint8_t v___x_4448_; 
v___x_4443_ = lean_unsigned_to_nat(1u);
v___x_4444_ = lean_mk_empty_array_with_capacity(v___x_4443_);
v___x_4445_ = lean_array_push(v___x_4444_, v_val_4411_);
v___x_4446_ = lean_array_get_size(v___x_4445_);
v___x_4447_ = lean_unsigned_to_nat(0u);
v___x_4448_ = lean_nat_dec_eq(v___x_4446_, v___x_4447_);
if (v___x_4448_ == 0)
{
lean_object* v_reader_4449_; lean_object* v_writer_4450_; lean_object* v_config_4451_; lean_object* v_events_4452_; lean_object* v_error_4453_; lean_object* v_date_4454_; uint8_t v_keepAlive_4455_; uint8_t v_pullBodyStalled_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4488_; 
v_reader_4449_ = lean_ctor_get(v_machine_4415_, 0);
v_writer_4450_ = lean_ctor_get(v_machine_4415_, 1);
v_config_4451_ = lean_ctor_get(v_machine_4415_, 2);
v_events_4452_ = lean_ctor_get(v_machine_4415_, 3);
v_error_4453_ = lean_ctor_get(v_machine_4415_, 4);
v_date_4454_ = lean_ctor_get(v_machine_4415_, 5);
v_keepAlive_4455_ = lean_ctor_get_uint8(v_machine_4415_, sizeof(void*)*6);
v_pullBodyStalled_4456_ = lean_ctor_get_uint8(v_machine_4415_, sizeof(void*)*6 + 1);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_machine_4415_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4458_ = v_machine_4415_;
v_isShared_4459_ = v_isSharedCheck_4488_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_date_4454_);
lean_inc(v_error_4453_);
lean_inc(v_events_4452_);
lean_inc(v_config_4451_);
lean_inc(v_writer_4450_);
lean_inc(v_reader_4449_);
lean_dec(v_machine_4415_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4488_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___y_4461_; lean_object* v___x_4482_; uint8_t v___x_4483_; 
v___x_4482_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__20));
v___x_4483_ = lean_nat_dec_lt(v___x_4447_, v___x_4446_);
if (v___x_4483_ == 0)
{
v___y_4461_ = v___x_4447_;
goto v___jp_4460_;
}
else
{
lean_object* v___f_4484_; size_t v___x_4485_; size_t v___x_4486_; lean_object* v___x_4487_; 
v___f_4484_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_tryDrainBody___redArg___closed__0));
v___x_4485_ = ((size_t)0ULL);
v___x_4486_ = lean_usize_of_nat(v___x_4446_);
lean_inc_ref(v___x_4445_);
v___x_4487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_4482_, v___f_4484_, v___x_4445_, v___x_4485_, v___x_4486_, v___x_4447_);
v___y_4461_ = v___x_4487_;
goto v___jp_4460_;
}
v___jp_4460_:
{
lean_object* v_userData_4462_; lean_object* v_outputData_4463_; lean_object* v_state_4464_; lean_object* v_knownSize_4465_; lean_object* v_messageHead_4466_; uint8_t v_userClosedBody_4467_; uint8_t v_omitBody_4468_; lean_object* v_userDataBytes_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4481_; 
v_userData_4462_ = lean_ctor_get(v_writer_4450_, 0);
v_outputData_4463_ = lean_ctor_get(v_writer_4450_, 1);
v_state_4464_ = lean_ctor_get(v_writer_4450_, 2);
v_knownSize_4465_ = lean_ctor_get(v_writer_4450_, 3);
v_messageHead_4466_ = lean_ctor_get(v_writer_4450_, 4);
v_userClosedBody_4467_ = lean_ctor_get_uint8(v_writer_4450_, sizeof(void*)*6);
v_omitBody_4468_ = lean_ctor_get_uint8(v_writer_4450_, sizeof(void*)*6 + 1);
v_userDataBytes_4469_ = lean_ctor_get(v_writer_4450_, 5);
v_isSharedCheck_4481_ = !lean_is_exclusive(v_writer_4450_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4471_ = v_writer_4450_;
v_isShared_4472_ = v_isSharedCheck_4481_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_userDataBytes_4469_);
lean_inc(v_messageHead_4466_);
lean_inc(v_knownSize_4465_);
lean_inc(v_state_4464_);
lean_inc(v_outputData_4463_);
lean_inc(v_userData_4462_);
lean_dec(v_writer_4450_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4481_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4476_; 
v___x_4473_ = l_Array_append___redArg(v_userData_4462_, v___x_4445_);
lean_dec_ref(v___x_4445_);
v___x_4474_ = lean_nat_add(v_userDataBytes_4469_, v___y_4461_);
lean_dec(v___y_4461_);
lean_dec(v_userDataBytes_4469_);
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 5, v___x_4474_);
lean_ctor_set(v___x_4471_, 0, v___x_4473_);
v___x_4476_ = v___x_4471_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4473_);
lean_ctor_set(v_reuseFailAlloc_4480_, 1, v_outputData_4463_);
lean_ctor_set(v_reuseFailAlloc_4480_, 2, v_state_4464_);
lean_ctor_set(v_reuseFailAlloc_4480_, 3, v_knownSize_4465_);
lean_ctor_set(v_reuseFailAlloc_4480_, 4, v_messageHead_4466_);
lean_ctor_set(v_reuseFailAlloc_4480_, 5, v___x_4474_);
lean_ctor_set_uint8(v_reuseFailAlloc_4480_, sizeof(void*)*6, v_userClosedBody_4467_);
lean_ctor_set_uint8(v_reuseFailAlloc_4480_, sizeof(void*)*6 + 1, v_omitBody_4468_);
v___x_4476_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4478_; 
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 1, v___x_4476_);
v___x_4478_ = v___x_4458_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_reader_4449_);
lean_ctor_set(v_reuseFailAlloc_4479_, 1, v___x_4476_);
lean_ctor_set(v_reuseFailAlloc_4479_, 2, v_config_4451_);
lean_ctor_set(v_reuseFailAlloc_4479_, 3, v_events_4452_);
lean_ctor_set(v_reuseFailAlloc_4479_, 4, v_error_4453_);
lean_ctor_set(v_reuseFailAlloc_4479_, 5, v_date_4454_);
lean_ctor_set_uint8(v_reuseFailAlloc_4479_, sizeof(void*)*6, v_keepAlive_4455_);
lean_ctor_set_uint8(v_reuseFailAlloc_4479_, sizeof(void*)*6 + 1, v_pullBodyStalled_4456_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
v___y_4430_ = v___x_4478_;
goto v___jp_4429_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_4445_);
v___y_4430_ = v_machine_4415_;
goto v___jp_4429_;
}
v___jp_4429_:
{
lean_object* v___x_4432_; 
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v___y_4430_);
v___x_4432_ = v___x_4427_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___y_4430_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v_requestStream_4416_);
lean_ctor_set(v_reuseFailAlloc_4442_, 2, v_timer_4417_);
lean_ctor_set(v_reuseFailAlloc_4442_, 3, v_response_4418_);
lean_ctor_set(v_reuseFailAlloc_4442_, 4, v_respStream_4419_);
lean_ctor_set(v_reuseFailAlloc_4442_, 5, v_inputWanted_4420_);
lean_ctor_set(v_reuseFailAlloc_4442_, 6, v_handler_4421_);
lean_ctor_set(v_reuseFailAlloc_4442_, 7, v_pendingHead_4422_);
lean_ctor_set(v_reuseFailAlloc_4442_, 8, v_dateSecond_4423_);
lean_ctor_set_uint8(v_reuseFailAlloc_4442_, sizeof(void*)*9, v_requestEnded_4424_);
lean_ctor_set_uint8(v_reuseFailAlloc_4442_, sizeof(void*)*9 + 1, v_aborted_4425_);
v___x_4432_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
uint8_t v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4433_ = 0;
v___x_4434_ = lean_box(v___x_4433_);
v___x_4435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4432_);
lean_ctor_set(v___x_4435_, 1, v___x_4434_);
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 0, v___x_4435_);
v___x_4437_ = v___x_4413_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v___x_4435_);
v___x_4437_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
lean_object* v___x_4439_; 
if (v_isShared_4385_ == 0)
{
lean_ctor_set_tag(v___x_4384_, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4437_);
v___x_4439_ = v___x_4384_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v___x_4437_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
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
uint8_t v_x_4492_; 
lean_dec_ref(v_outbox_4278_);
lean_dec_ref(v_config_4277_);
lean_dec_ref(v_inst_4275_);
v_x_4492_ = lean_ctor_get_uint8(v_event_4279_, 0);
lean_dec_ref_known(v_event_4279_, 0);
if (v_x_4492_ == 0)
{
lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
lean_dec(v_handler_4276_);
lean_dec_ref(v_inst_4274_);
v___x_4493_ = lean_box(v_x_4492_);
v___x_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4494_, 0, v_state_4280_);
lean_ctor_set(v___x_4494_, 1, v___x_4493_);
v___x_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
v___x_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
return v___x_4496_;
}
else
{
lean_object* v_machine_4497_; lean_object* v_requestStream_4498_; lean_object* v_timer_4499_; lean_object* v_response_4500_; lean_object* v_respStream_4501_; lean_object* v_inputWanted_4502_; lean_object* v_handler_4503_; lean_object* v_pendingHead_4504_; lean_object* v_dateSecond_4505_; uint8_t v_requestEnded_4506_; uint8_t v_aborted_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4564_; 
v_machine_4497_ = lean_ctor_get(v_state_4280_, 0);
v_requestStream_4498_ = lean_ctor_get(v_state_4280_, 1);
v_timer_4499_ = lean_ctor_get(v_state_4280_, 2);
v_response_4500_ = lean_ctor_get(v_state_4280_, 3);
v_respStream_4501_ = lean_ctor_get(v_state_4280_, 4);
v_inputWanted_4502_ = lean_ctor_get(v_state_4280_, 5);
v_handler_4503_ = lean_ctor_get(v_state_4280_, 6);
v_pendingHead_4504_ = lean_ctor_get(v_state_4280_, 7);
v_dateSecond_4505_ = lean_ctor_get(v_state_4280_, 8);
v_requestEnded_4506_ = lean_ctor_get_uint8(v_state_4280_, sizeof(void*)*9);
v_aborted_4507_ = lean_ctor_get_uint8(v_state_4280_, sizeof(void*)*9 + 1);
v_isSharedCheck_4564_ = !lean_is_exclusive(v_state_4280_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4509_ = v_state_4280_;
v_isShared_4510_ = v_isSharedCheck_4564_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_dateSecond_4505_);
lean_inc(v_pendingHead_4504_);
lean_inc(v_handler_4503_);
lean_inc(v_inputWanted_4502_);
lean_inc(v_respStream_4501_);
lean_inc(v_response_4500_);
lean_inc(v_timer_4499_);
lean_inc(v_requestStream_4498_);
lean_inc(v_machine_4497_);
lean_dec(v_state_4280_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4564_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
uint8_t v___x_4511_; lean_object* v___x_4512_; lean_object* v_fst_4513_; lean_object* v_reader_4514_; lean_object* v_writer_4515_; lean_object* v_snd_4516_; lean_object* v_config_4517_; lean_object* v_events_4518_; lean_object* v_error_4519_; lean_object* v_date_4520_; uint8_t v_keepAlive_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4561_; 
v___x_4511_ = 0;
v___x_4512_ = l___private_Std_Http_Protocol_H1_0__Std_Http_Protocol_H1_Machine_pullNextChunk(v___x_4511_, v_machine_4497_);
v_fst_4513_ = lean_ctor_get(v___x_4512_, 0);
lean_inc(v_fst_4513_);
v_reader_4514_ = lean_ctor_get(v_fst_4513_, 0);
lean_inc_ref(v_reader_4514_);
v_writer_4515_ = lean_ctor_get(v_fst_4513_, 1);
lean_inc_ref(v_writer_4515_);
v_snd_4516_ = lean_ctor_get(v___x_4512_, 1);
lean_inc(v_snd_4516_);
lean_dec_ref(v___x_4512_);
v_config_4517_ = lean_ctor_get(v_fst_4513_, 2);
v_events_4518_ = lean_ctor_get(v_fst_4513_, 3);
v_error_4519_ = lean_ctor_get(v_fst_4513_, 4);
v_date_4520_ = lean_ctor_get(v_fst_4513_, 5);
v_keepAlive_4521_ = lean_ctor_get_uint8(v_fst_4513_, sizeof(void*)*6);
v_isSharedCheck_4561_ = !lean_is_exclusive(v_fst_4513_);
if (v_isSharedCheck_4561_ == 0)
{
lean_object* v_unused_4562_; lean_object* v_unused_4563_; 
v_unused_4562_ = lean_ctor_get(v_fst_4513_, 1);
lean_dec(v_unused_4562_);
v_unused_4563_ = lean_ctor_get(v_fst_4513_, 0);
lean_dec(v_unused_4563_);
v___x_4523_ = v_fst_4513_;
v_isShared_4524_ = v_isSharedCheck_4561_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_date_4520_);
lean_inc(v_error_4519_);
lean_inc(v_events_4518_);
lean_inc(v_config_4517_);
lean_dec(v_fst_4513_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4561_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v_state_4525_; lean_object* v_state_4526_; lean_object* v___f_4527_; uint8_t v___y_4529_; uint8_t v___y_4550_; 
v_state_4525_ = lean_ctor_get(v_reader_4514_, 0);
v_state_4526_ = lean_ctor_get(v_writer_4515_, 2);
v___f_4527_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_4527_, 0, v_inst_4274_);
lean_closure_set(v___f_4527_, 1, v_handler_4276_);
switch(lean_obj_tag(v_state_4526_))
{
case 6:
{
v___y_4550_ = v_x_4492_;
goto v___jp_4549_;
}
case 7:
{
v___y_4550_ = v_x_4492_;
goto v___jp_4549_;
}
default: 
{
switch(lean_obj_tag(v_state_4526_))
{
case 0:
{
uint8_t v___x_4553_; 
v___x_4553_ = 0;
v___y_4550_ = v___x_4553_;
goto v___jp_4549_;
}
case 1:
{
uint8_t v___x_4554_; 
v___x_4554_ = 0;
v___y_4550_ = v___x_4554_;
goto v___jp_4549_;
}
default: 
{
if (lean_obj_tag(v_state_4525_) == 2)
{
lean_object* v_a_4555_; 
v_a_4555_ = lean_ctor_get(v_state_4525_, 0);
if (lean_obj_tag(v_a_4555_) == 0)
{
lean_object* v_remaining_4556_; lean_object* v___x_4557_; uint8_t v___x_4558_; 
v_remaining_4556_ = lean_ctor_get(v_a_4555_, 0);
v___x_4557_ = lean_unsigned_to_nat(0u);
v___x_4558_ = lean_nat_dec_eq(v_remaining_4556_, v___x_4557_);
v___y_4550_ = v___x_4558_;
goto v___jp_4549_;
}
else
{
uint8_t v___x_4559_; 
v___x_4559_ = 0;
v___y_4550_ = v___x_4559_;
goto v___jp_4549_;
}
}
else
{
uint8_t v___x_4560_; 
v___x_4560_ = 0;
v___y_4550_ = v___x_4560_;
goto v___jp_4549_;
}
}
}
}
}
v___jp_4528_:
{
lean_object* v___x_4531_; 
if (v_isShared_4524_ == 0)
{
v___x_4531_ = v___x_4523_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_reader_4514_);
lean_ctor_set(v_reuseFailAlloc_4548_, 1, v_writer_4515_);
lean_ctor_set(v_reuseFailAlloc_4548_, 2, v_config_4517_);
lean_ctor_set(v_reuseFailAlloc_4548_, 3, v_events_4518_);
lean_ctor_set(v_reuseFailAlloc_4548_, 4, v_error_4519_);
lean_ctor_set(v_reuseFailAlloc_4548_, 5, v_date_4520_);
lean_ctor_set_uint8(v_reuseFailAlloc_4548_, sizeof(void*)*6, v_keepAlive_4521_);
v___x_4531_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
lean_object* v_st_4533_; 
lean_ctor_set_uint8(v___x_4531_, sizeof(void*)*6 + 1, v___y_4529_);
lean_inc_ref(v_requestStream_4498_);
if (v_isShared_4510_ == 0)
{
lean_ctor_set(v___x_4509_, 0, v___x_4531_);
v_st_4533_ = v___x_4509_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v___x_4531_);
lean_ctor_set(v_reuseFailAlloc_4547_, 1, v_requestStream_4498_);
lean_ctor_set(v_reuseFailAlloc_4547_, 2, v_timer_4499_);
lean_ctor_set(v_reuseFailAlloc_4547_, 3, v_response_4500_);
lean_ctor_set(v_reuseFailAlloc_4547_, 4, v_respStream_4501_);
lean_ctor_set(v_reuseFailAlloc_4547_, 5, v_inputWanted_4502_);
lean_ctor_set(v_reuseFailAlloc_4547_, 6, v_handler_4503_);
lean_ctor_set(v_reuseFailAlloc_4547_, 7, v_pendingHead_4504_);
lean_ctor_set(v_reuseFailAlloc_4547_, 8, v_dateSecond_4505_);
lean_ctor_set_uint8(v_reuseFailAlloc_4547_, sizeof(void*)*9, v_requestEnded_4506_);
lean_ctor_set_uint8(v_reuseFailAlloc_4547_, sizeof(void*)*9 + 1, v_aborted_4507_);
v_st_4533_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___f_4534_; 
lean_inc_ref(v_st_4533_);
v___f_4534_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5___boxed), 3, 1);
lean_closure_set(v___f_4534_, 0, v_st_4533_);
if (lean_obj_tag(v_snd_4516_) == 1)
{
lean_object* v_val_4535_; uint8_t v_final_4536_; uint8_t v_incomplete_4537_; lean_object* v_chunk_4538_; lean_object* v___f_4539_; lean_object* v___x_4540_; uint8_t v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
lean_dec_ref(v_st_4533_);
v_val_4535_ = lean_ctor_get(v_snd_4516_, 0);
lean_inc(v_val_4535_);
lean_dec_ref_known(v_snd_4516_, 1);
v_final_4536_ = lean_ctor_get_uint8(v_val_4535_, sizeof(void*)*1);
v_incomplete_4537_ = lean_ctor_get_uint8(v_val_4535_, sizeof(void*)*1 + 1);
v_chunk_4538_ = lean_ctor_get(v_val_4535_, 0);
lean_inc_ref(v_chunk_4538_);
lean_dec(v_val_4535_);
v___f_4539_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4539_, 0, v___f_4534_);
v___x_4540_ = lean_unsigned_to_nat(0u);
v___x_4541_ = 0;
v___x_4542_ = l_Std_Http_Body_Stream_offer(v_requestStream_4498_, v_chunk_4538_, v_incomplete_4537_, v_final_4536_);
v___x_4543_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4540_, v___x_4541_, v___x_4542_, v___f_4527_);
v___x_4544_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4540_, v___x_4541_, v___x_4543_, v___f_4539_);
return v___x_4544_;
}
else
{
lean_object* v___x_4545_; lean_object* v___x_4546_; 
lean_dec_ref(v___f_4534_);
lean_dec_ref(v___f_4527_);
lean_dec(v_snd_4516_);
lean_dec_ref(v_requestStream_4498_);
v___x_4545_ = lean_box(0);
v___x_4546_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__5(v_st_4533_, v___x_4545_);
return v___x_4546_;
}
}
}
}
v___jp_4549_:
{
if (lean_obj_tag(v_snd_4516_) == 0)
{
if (v___y_4550_ == 0)
{
if (lean_obj_tag(v_state_4525_) == 2)
{
v___y_4529_ = v_x_4492_;
goto v___jp_4528_;
}
else
{
v___y_4529_ = v___y_4550_;
goto v___jp_4528_;
}
}
else
{
uint8_t v___x_4551_; 
v___x_4551_ = 0;
v___y_4529_ = v___x_4551_;
goto v___jp_4528_;
}
}
else
{
uint8_t v___x_4552_; 
v___x_4552_ = 0;
v___y_4529_ = v___x_4552_;
goto v___jp_4528_;
}
}
}
}
}
}
case 3:
{
lean_object* v_x_4565_; 
lean_dec_ref(v_outbox_4278_);
v_x_4565_ = lean_ctor_get(v_event_4279_, 0);
lean_inc_ref(v_x_4565_);
lean_dec_ref_known(v_event_4279_, 1);
if (lean_obj_tag(v_x_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v___f_4567_; lean_object* v___f_4568_; lean_object* v___x_4569_; uint8_t v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
lean_dec_ref(v_config_4277_);
v_a_4566_ = lean_ctor_get(v_x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v_x_4565_, 1);
v___f_4567_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__0));
v___f_4568_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__7___boxed), 5, 3);
lean_closure_set(v___f_4568_, 0, v_inst_4275_);
lean_closure_set(v___f_4568_, 1, v_state_4280_);
lean_closure_set(v___f_4568_, 2, v___f_4567_);
v___x_4569_ = lean_unsigned_to_nat(0u);
v___x_4570_ = 0;
v___x_4571_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_4274_, v_handler_4276_, v_a_4566_);
v___x_4572_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4569_, v___x_4570_, v___x_4571_, v___f_4568_);
return v___x_4572_;
}
else
{
lean_object* v_machine_4573_; lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4650_; 
v_machine_4573_ = lean_ctor_get(v_state_4280_, 0);
lean_inc_ref(v_machine_4573_);
v_a_4574_ = lean_ctor_get(v_x_4565_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v_x_4565_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4576_ = v_x_4565_;
v_isShared_4577_ = v_isSharedCheck_4650_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v_x_4565_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4650_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v_requestStream_4578_; lean_object* v_timer_4579_; lean_object* v_response_4580_; lean_object* v_respStream_4581_; lean_object* v_inputWanted_4582_; lean_object* v_pendingHead_4583_; lean_object* v_dateSecond_4584_; uint8_t v_requestEnded_4585_; uint8_t v_aborted_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4647_; 
v_requestStream_4578_ = lean_ctor_get(v_state_4280_, 1);
v_timer_4579_ = lean_ctor_get(v_state_4280_, 2);
v_response_4580_ = lean_ctor_get(v_state_4280_, 3);
v_respStream_4581_ = lean_ctor_get(v_state_4280_, 4);
v_inputWanted_4582_ = lean_ctor_get(v_state_4280_, 5);
v_pendingHead_4583_ = lean_ctor_get(v_state_4280_, 7);
v_dateSecond_4584_ = lean_ctor_get(v_state_4280_, 8);
v_requestEnded_4585_ = lean_ctor_get_uint8(v_state_4280_, sizeof(void*)*9);
v_aborted_4586_ = lean_ctor_get_uint8(v_state_4280_, sizeof(void*)*9 + 1);
v_isSharedCheck_4647_ = !lean_is_exclusive(v_state_4280_);
if (v_isSharedCheck_4647_ == 0)
{
lean_object* v_unused_4648_; lean_object* v_unused_4649_; 
v_unused_4648_ = lean_ctor_get(v_state_4280_, 6);
lean_dec(v_unused_4648_);
v_unused_4649_ = lean_ctor_get(v_state_4280_, 0);
lean_dec(v_unused_4649_);
v___x_4588_ = v_state_4280_;
v_isShared_4589_ = v_isSharedCheck_4647_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_dateSecond_4584_);
lean_inc(v_pendingHead_4583_);
lean_inc(v_inputWanted_4582_);
lean_inc(v_respStream_4581_);
lean_inc(v_response_4580_);
lean_inc(v_timer_4579_);
lean_inc(v_requestStream_4578_);
lean_dec(v_state_4280_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4647_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v_error_4590_; lean_object* v___x_4591_; lean_object* v_state_4593_; 
v_error_4590_ = lean_ctor_get(v_machine_4573_, 4);
v___x_4591_ = lean_box(0);
lean_inc(v_dateSecond_4584_);
lean_inc(v_pendingHead_4583_);
lean_inc(v_inputWanted_4582_);
lean_inc(v_respStream_4581_);
lean_inc_ref(v_response_4580_);
lean_inc(v_timer_4579_);
lean_inc_ref(v_requestStream_4578_);
lean_inc_ref(v_machine_4573_);
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 6, v___x_4591_);
v_state_4593_ = v___x_4588_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_machine_4573_);
lean_ctor_set(v_reuseFailAlloc_4646_, 1, v_requestStream_4578_);
lean_ctor_set(v_reuseFailAlloc_4646_, 2, v_timer_4579_);
lean_ctor_set(v_reuseFailAlloc_4646_, 3, v_response_4580_);
lean_ctor_set(v_reuseFailAlloc_4646_, 4, v_respStream_4581_);
lean_ctor_set(v_reuseFailAlloc_4646_, 5, v_inputWanted_4582_);
lean_ctor_set(v_reuseFailAlloc_4646_, 6, v___x_4591_);
lean_ctor_set(v_reuseFailAlloc_4646_, 7, v_pendingHead_4583_);
lean_ctor_set(v_reuseFailAlloc_4646_, 8, v_dateSecond_4584_);
lean_ctor_set_uint8(v_reuseFailAlloc_4646_, sizeof(void*)*9, v_requestEnded_4585_);
lean_ctor_set_uint8(v_reuseFailAlloc_4646_, sizeof(void*)*9 + 1, v_aborted_4586_);
v_state_4593_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
if (lean_obj_tag(v_error_4590_) == 0)
{
lean_object* v_line_4594_; lean_object* v_body_4595_; lean_object* v_status_4596_; uint8_t v___x_4597_; uint8_t v___y_4599_; uint16_t v___x_4615_; uint16_t v___x_4616_; uint8_t v___x_4617_; 
v_line_4594_ = lean_ctor_get(v_a_4574_, 0);
v_body_4595_ = lean_ctor_get(v_a_4574_, 1);
v_status_4596_ = lean_ctor_get(v_line_4594_, 0);
v___x_4597_ = 1;
v___x_4615_ = 100;
v___x_4616_ = l_Std_Http_Status_toCode(v_status_4596_);
v___x_4617_ = lean_uint16_dec_le(v___x_4615_, v___x_4616_);
if (v___x_4617_ == 0)
{
lean_dec(v_dateSecond_4584_);
lean_dec(v_pendingHead_4583_);
lean_dec(v_inputWanted_4582_);
lean_dec(v_respStream_4581_);
lean_dec_ref(v_response_4580_);
lean_dec(v_timer_4579_);
lean_dec_ref(v_requestStream_4578_);
lean_dec_ref(v_machine_4573_);
v___y_4599_ = v___x_4617_;
goto v___jp_4598_;
}
else
{
uint16_t v___x_4618_; uint8_t v___x_4619_; 
v___x_4618_ = 200;
v___x_4619_ = lean_uint16_dec_lt(v___x_4616_, v___x_4618_);
if (v___x_4619_ == 0)
{
lean_dec(v_dateSecond_4584_);
lean_dec(v_pendingHead_4583_);
lean_dec(v_inputWanted_4582_);
lean_dec(v_respStream_4581_);
lean_dec_ref(v_response_4580_);
lean_dec(v_timer_4579_);
lean_dec_ref(v_requestStream_4578_);
lean_dec_ref(v_machine_4573_);
v___y_4599_ = v___x_4619_;
goto v___jp_4598_;
}
else
{
lean_object* v_close_4620_; lean_object* v_isClosed_4621_; uint8_t v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___f_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___f_4629_; lean_object* v___f_4630_; lean_object* v___x_4631_; lean_object* v___f_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
lean_inc_n(v_body_4595_, 2);
lean_dec_ref(v_state_4593_);
lean_del_object(v___x_4576_);
lean_dec(v_a_4574_);
lean_dec_ref(v_config_4277_);
v_close_4620_ = lean_ctor_get(v_inst_4275_, 1);
lean_inc_ref(v_close_4620_);
v_isClosed_4621_ = lean_ctor_get(v_inst_4275_, 2);
lean_inc_ref(v_isClosed_4621_);
lean_dec_ref(v_inst_4275_);
v___x_4622_ = 0;
v___x_4623_ = lean_box(v_requestEnded_4585_);
v___x_4624_ = lean_box(v_aborted_4586_);
v___x_4625_ = lean_box(v___x_4622_);
v___f_4626_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__16___boxed), 14, 12);
lean_closure_set(v___f_4626_, 0, v_machine_4573_);
lean_closure_set(v___f_4626_, 1, v_requestStream_4578_);
lean_closure_set(v___f_4626_, 2, v_timer_4579_);
lean_closure_set(v___f_4626_, 3, v_response_4580_);
lean_closure_set(v___f_4626_, 4, v_respStream_4581_);
lean_closure_set(v___f_4626_, 5, v_inputWanted_4582_);
lean_closure_set(v___f_4626_, 6, v___x_4591_);
lean_closure_set(v___f_4626_, 7, v_pendingHead_4583_);
lean_closure_set(v___f_4626_, 8, v_dateSecond_4584_);
lean_closure_set(v___f_4626_, 9, v___x_4623_);
lean_closure_set(v___f_4626_, 10, v___x_4624_);
lean_closure_set(v___f_4626_, 11, v___x_4625_);
v___x_4627_ = lean_box(v___x_4616_);
v___x_4628_ = lean_box(v___x_4622_);
v___f_4629_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__17___boxed), 7, 5);
lean_closure_set(v___f_4629_, 0, v___x_4627_);
lean_closure_set(v___f_4629_, 1, v_inst_4274_);
lean_closure_set(v___f_4629_, 2, v_handler_4276_);
lean_closure_set(v___f_4629_, 3, v___x_4628_);
lean_closure_set(v___f_4629_, 4, v___f_4626_);
lean_inc_ref(v___f_4629_);
v___f_4630_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4630_, 0, v___f_4629_);
v___x_4631_ = lean_box(v___x_4622_);
v___f_4632_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__19___boxed), 7, 5);
lean_closure_set(v___f_4632_, 0, v_close_4620_);
lean_closure_set(v___f_4632_, 1, v_body_4595_);
lean_closure_set(v___f_4632_, 2, v___x_4631_);
lean_closure_set(v___f_4632_, 3, v___f_4630_);
lean_closure_set(v___f_4632_, 4, v___f_4629_);
v___x_4633_ = lean_unsigned_to_nat(0u);
v___x_4634_ = lean_apply_2(v_isClosed_4621_, v_body_4595_, lean_box(0));
v___x_4635_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4633_, v___x_4622_, v___x_4634_, v___f_4632_);
return v___x_4635_;
}
}
v___jp_4598_:
{
lean_object* v___x_4600_; lean_object* v___f_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___f_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4600_ = lean_box(v___y_4599_);
v___f_4601_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__9___boxed), 3, 1);
lean_closure_set(v___f_4601_, 0, v___x_4600_);
v___x_4602_ = lean_box(v___y_4599_);
v___x_4603_ = lean_box(v___x_4597_);
v___f_4604_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__15___boxed), 9, 7);
lean_closure_set(v___f_4604_, 0, v___x_4602_);
lean_closure_set(v___f_4604_, 1, v___x_4603_);
lean_closure_set(v___f_4604_, 2, v_inst_4274_);
lean_closure_set(v___f_4604_, 3, v_handler_4276_);
lean_closure_set(v___f_4604_, 4, v_inst_4275_);
lean_closure_set(v___f_4604_, 5, v___f_4601_);
lean_closure_set(v___f_4604_, 6, v_a_4574_);
v___x_4605_ = lean_unsigned_to_nat(0u);
v___x_4606_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(v_config_4277_, v_state_4593_);
lean_dec_ref(v_config_4277_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; lean_object* v___x_4609_; 
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
lean_inc(v_a_4607_);
lean_dec_ref_known(v___x_4606_, 1);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 0, v_a_4607_);
v___x_4609_ = v___x_4576_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4607_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
v___y_4283_ = v___x_4605_;
v___y_4284_ = v___f_4604_;
v___y_4285_ = v___y_4599_;
v_val_4286_ = v___x_4609_;
goto v___jp_4282_;
}
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4613_; 
v_a_4611_ = lean_ctor_get(v___x_4606_, 0);
lean_inc(v_a_4611_);
lean_dec_ref_known(v___x_4606_, 1);
if (v_isShared_4577_ == 0)
{
lean_ctor_set_tag(v___x_4576_, 0);
lean_ctor_set(v___x_4576_, 0, v_a_4611_);
v___x_4613_ = v___x_4576_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4611_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
v___y_4283_ = v___x_4605_;
v___y_4284_ = v___f_4604_;
v___y_4285_ = v___y_4599_;
v_val_4286_ = v___x_4613_;
goto v___jp_4282_;
}
}
}
}
else
{
lean_object* v_close_4636_; lean_object* v_isClosed_4637_; lean_object* v_body_4638_; lean_object* v___f_4639_; lean_object* v___f_4640_; lean_object* v___f_4641_; lean_object* v___x_4642_; uint8_t v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
lean_dec(v_dateSecond_4584_);
lean_dec(v_pendingHead_4583_);
lean_dec(v_inputWanted_4582_);
lean_dec(v_respStream_4581_);
lean_dec_ref(v_response_4580_);
lean_dec(v_timer_4579_);
lean_dec_ref(v_requestStream_4578_);
lean_del_object(v___x_4576_);
lean_dec_ref(v_machine_4573_);
lean_dec_ref(v_config_4277_);
lean_dec(v_handler_4276_);
lean_dec_ref(v_inst_4274_);
v_close_4636_ = lean_ctor_get(v_inst_4275_, 1);
lean_inc_ref(v_close_4636_);
v_isClosed_4637_ = lean_ctor_get(v_inst_4275_, 2);
lean_inc_ref(v_isClosed_4637_);
lean_dec_ref(v_inst_4275_);
v_body_4638_ = lean_ctor_get(v_a_4574_, 1);
lean_inc_n(v_body_4638_, 2);
lean_dec(v_a_4574_);
v___f_4639_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__18___boxed), 3, 1);
lean_closure_set(v___f_4639_, 0, v_state_4593_);
lean_inc_ref(v___f_4639_);
v___f_4640_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_4640_, 0, v___f_4639_);
v___f_4641_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__21___boxed), 6, 4);
lean_closure_set(v___f_4641_, 0, v_close_4636_);
lean_closure_set(v___f_4641_, 1, v_body_4638_);
lean_closure_set(v___f_4641_, 2, v___f_4640_);
lean_closure_set(v___f_4641_, 3, v___f_4639_);
v___x_4642_ = lean_unsigned_to_nat(0u);
v___x_4643_ = 0;
v___x_4644_ = lean_apply_2(v_isClosed_4637_, v_body_4638_, lean_box(0));
v___x_4645_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4642_, v___x_4643_, v___x_4644_, v___f_4641_);
return v___x_4645_;
}
}
}
}
}
}
case 4:
{
lean_object* v___f_4651_; lean_object* v___x_4652_; uint8_t v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; 
lean_dec_ref(v_config_4277_);
lean_dec(v_handler_4276_);
lean_dec_ref(v_inst_4275_);
lean_dec_ref(v_inst_4274_);
v___f_4651_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__20___boxed), 3, 1);
lean_closure_set(v___f_4651_, 0, v_state_4280_);
v___x_4652_ = lean_unsigned_to_nat(0u);
v___x_4653_ = 0;
v___x_4654_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_outbox_4278_);
v___x_4655_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4652_, v___x_4653_, v___x_4654_, v___f_4651_);
return v___x_4655_;
}
case 5:
{
lean_object* v_timer_4656_; lean_object* v___f_4657_; lean_object* v___f_4658_; lean_object* v___y_4660_; 
lean_dec_ref(v_outbox_4278_);
lean_dec_ref(v_config_4277_);
v_timer_4656_ = lean_ctor_get(v_state_4280_, 2);
lean_inc(v_timer_4656_);
v___f_4657_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
v___f_4658_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___lam__23___boxed), 5, 3);
lean_closure_set(v___f_4658_, 0, v_inst_4275_);
lean_closure_set(v___f_4658_, 1, v_state_4280_);
lean_closure_set(v___f_4658_, 2, v___f_4657_);
if (lean_obj_tag(v_timer_4656_) == 1)
{
lean_object* v___x_4665_; 
lean_dec_ref_known(v_timer_4656_, 1);
v___x_4665_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__3, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__3_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__3);
v___y_4660_ = v___x_4665_;
goto v___jp_4659_;
}
else
{
lean_object* v___x_4666_; 
lean_dec(v_timer_4656_);
v___x_4666_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__5);
v___y_4660_ = v___x_4666_;
goto v___jp_4659_;
}
v___jp_4659_:
{
lean_object* v___x_4661_; uint8_t v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4661_ = lean_unsigned_to_nat(0u);
v___x_4662_ = 0;
lean_inc(v___y_4660_);
v___x_4663_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_4274_, v_handler_4276_, v___y_4660_);
v___x_4664_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4661_, v___x_4662_, v___x_4663_, v___f_4658_);
return v___x_4664_;
}
}
case 6:
{
lean_object* v___f_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; uint8_t v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
lean_dec_ref(v_outbox_4278_);
lean_dec_ref(v_config_4277_);
lean_dec(v_handler_4276_);
lean_dec_ref(v_inst_4274_);
v___f_4667_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___closed__1));
v___x_4668_ = lean_box(55);
v___x_4669_ = lean_unsigned_to_nat(0u);
v___x_4670_ = 0;
v___x_4671_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_abortWith___redArg(v_inst_4275_, v_state_4280_, v___x_4668_);
v___x_4672_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4669_, v___x_4670_, v___x_4671_, v___f_4667_);
return v___x_4672_;
}
default: 
{
uint8_t v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
lean_dec_ref(v_outbox_4278_);
lean_dec_ref(v_config_4277_);
lean_dec(v_handler_4276_);
lean_dec_ref(v_inst_4275_);
lean_dec_ref(v_inst_4274_);
v___x_4673_ = 1;
v___x_4674_ = lean_box(v___x_4673_);
v___x_4675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4675_, 0, v_state_4280_);
lean_ctor_set(v___x_4675_, 1, v___x_4674_);
v___x_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4675_);
v___x_4677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4676_);
return v___x_4677_;
}
}
v___jp_4282_:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4287_, 0, v_val_4286_);
v___x_4288_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_4283_, v___y_4285_, v___x_4287_, v___y_4284_);
return v___x_4288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg___boxed(lean_object* v_inst_4678_, lean_object* v_inst_4679_, lean_object* v_handler_4680_, lean_object* v_config_4681_, lean_object* v_outbox_4682_, lean_object* v_event_4683_, lean_object* v_state_4684_, lean_object* v_a_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_4678_, v_inst_4679_, v_handler_4680_, v_config_4681_, v_outbox_4682_, v_event_4683_, v_state_4684_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(lean_object* v_00_u03b1_4687_, lean_object* v_00_u03c3_4688_, lean_object* v_00_u03b2_4689_, lean_object* v_inst_4690_, lean_object* v_inst_4691_, lean_object* v_handler_4692_, lean_object* v_config_4693_, lean_object* v_outbox_4694_, lean_object* v_event_4695_, lean_object* v_state_4696_){
_start:
{
lean_object* v___x_4698_; 
v___x_4698_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_inst_4690_, v_inst_4691_, v_handler_4692_, v_config_4693_, v_outbox_4694_, v_event_4695_, v_state_4696_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___boxed(lean_object* v_00_u03b1_4699_, lean_object* v_00_u03c3_4700_, lean_object* v_00_u03b2_4701_, lean_object* v_inst_4702_, lean_object* v_inst_4703_, lean_object* v_handler_4704_, lean_object* v_config_4705_, lean_object* v_outbox_4706_, lean_object* v_event_4707_, lean_object* v_state_4708_, lean_object* v_a_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent(v_00_u03b1_4699_, v_00_u03c3_4700_, v_00_u03b2_4701_, v_inst_4702_, v_inst_4703_, v_handler_4704_, v_config_4705_, v_outbox_4706_, v_event_4707_, v_state_4708_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(lean_object* v_respStream_4711_, lean_object* v_connectionContext_4712_, lean_object* v_timer_4713_, lean_object* v_response_4714_, lean_object* v_inputWanted_4715_, lean_object* v_socket_4716_, lean_object* v_reader_4717_, lean_object* v_inputLimit_4718_, uint8_t v_pullBodyStalled_4719_, uint8_t v_requestBodyOpen_4720_, lean_object* v_state_4721_, uint8_t v_requestBodyInterested_4722_, lean_object* v_handler_4723_, lean_object* v_requestBody_4724_){
_start:
{
lean_object* v___y_4727_; lean_object* v___y_4728_; lean_object* v___y_4729_; lean_object* v___y_4730_; lean_object* v___y_4731_; uint8_t v___y_4732_; lean_object* v___y_4737_; uint8_t v___y_4738_; lean_object* v___y_4739_; lean_object* v___y_4740_; lean_object* v___y_4741_; lean_object* v___y_4742_; uint8_t v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4747_; lean_object* v___y_4748_; uint8_t v___y_4749_; lean_object* v___y_4750_; uint8_t v___y_4754_; lean_object* v___y_4755_; uint8_t v___y_4756_; lean_object* v___y_4757_; uint8_t v___y_4761_; uint8_t v___y_4762_; lean_object* v___y_4763_; uint8_t v___y_4764_; lean_object* v___y_4765_; uint8_t v___y_4768_; uint8_t v___y_4769_; lean_object* v___y_4770_; uint8_t v___y_4771_; uint8_t v___y_4774_; uint8_t v___y_4775_; lean_object* v___y_4776_; uint8_t v___y_4777_; uint8_t v___y_4780_; uint8_t v___y_4781_; lean_object* v___y_4782_; uint8_t v___y_4783_; uint8_t v___y_4793_; uint8_t v___y_4794_; lean_object* v___y_4795_; uint8_t v___y_4796_; uint8_t v___y_4798_; uint8_t v___y_4799_; lean_object* v___y_4800_; uint8_t v___y_4803_; uint8_t v___y_4804_; lean_object* v___y_4805_; uint8_t v___y_4808_; uint8_t v___y_4809_; lean_object* v___y_4810_; uint8_t v___y_4811_; uint8_t v___y_4813_; uint8_t v___y_4814_; uint8_t v___y_4815_; lean_object* v___y_4816_; uint8_t v___y_4818_; uint8_t v___y_4819_; uint8_t v___y_4820_; lean_object* v___y_4821_; uint8_t v___y_4822_; uint8_t v___y_4825_; uint8_t v___y_4826_; uint8_t v___y_4827_; lean_object* v___y_4828_; uint8_t v___y_4835_; uint8_t v___y_4836_; uint8_t v___y_4837_; lean_object* v___y_4838_; uint8_t v___y_4840_; uint8_t v___y_4841_; uint8_t v___y_4842_; lean_object* v___y_4843_; uint8_t v___y_4844_; uint8_t v___y_4846_; uint8_t v___y_4847_; uint8_t v___y_4848_; lean_object* v___y_4849_; uint8_t v___y_4850_; uint8_t v___y_4853_; uint8_t v___y_4854_; uint8_t v___y_4855_; lean_object* v___y_4856_; uint8_t v___y_4863_; uint8_t v___y_4864_; lean_object* v___y_4865_; uint8_t v___y_4866_; uint8_t v___y_4868_; lean_object* v___y_4869_; uint8_t v___y_4873_; uint8_t v___y_4876_; uint8_t v___y_4879_; uint8_t v___y_4880_; uint8_t v___y_4882_; uint8_t v___y_4883_; uint8_t v___y_4886_; uint8_t v___y_4887_; uint8_t v___y_4894_; uint8_t v___y_4895_; uint8_t v___y_4897_; uint8_t v___y_4898_; uint8_t v___y_4899_; 
if (lean_obj_tag(v_timer_4713_) == 2)
{
uint8_t v___x_4901_; 
v___x_4901_ = 1;
if (lean_obj_tag(v_inputWanted_4715_) == 0)
{
uint8_t v___x_4902_; 
v___x_4902_ = 0;
if (v_requestBodyOpen_4720_ == 0)
{
v___y_4886_ = v___x_4901_;
v___y_4887_ = v___x_4902_;
goto v___jp_4885_;
}
else
{
switch(lean_obj_tag(v_state_4721_))
{
case 6:
{
v___y_4873_ = v___x_4901_;
goto v___jp_4872_;
}
case 7:
{
v___y_4873_ = v___x_4901_;
goto v___jp_4872_;
}
default: 
{
switch(lean_obj_tag(v_state_4721_))
{
case 0:
{
v___y_4897_ = v___x_4901_;
v___y_4898_ = v___x_4902_;
v___y_4899_ = v___x_4902_;
goto v___jp_4896_;
}
case 1:
{
v___y_4897_ = v___x_4901_;
v___y_4898_ = v___x_4902_;
v___y_4899_ = v___x_4902_;
goto v___jp_4896_;
}
default: 
{
lean_object* v_state_4903_; 
v_state_4903_ = lean_ctor_get(v_reader_4717_, 0);
if (lean_obj_tag(v_state_4903_) == 2)
{
lean_object* v_a_4904_; 
v_a_4904_ = lean_ctor_get(v_state_4903_, 0);
if (lean_obj_tag(v_a_4904_) == 0)
{
lean_object* v_remaining_4905_; lean_object* v___x_4906_; uint8_t v___x_4907_; 
v_remaining_4905_ = lean_ctor_get(v_a_4904_, 0);
v___x_4906_ = lean_unsigned_to_nat(0u);
v___x_4907_ = lean_nat_dec_eq(v_remaining_4905_, v___x_4906_);
if (v___x_4907_ == 0)
{
v___y_4897_ = v___x_4901_;
v___y_4898_ = v___x_4902_;
v___y_4899_ = v___x_4907_;
goto v___jp_4896_;
}
else
{
v___y_4873_ = v___x_4901_;
goto v___jp_4872_;
}
}
else
{
v___y_4897_ = v___x_4901_;
v___y_4898_ = v___x_4902_;
v___y_4899_ = v___x_4902_;
goto v___jp_4896_;
}
}
else
{
v___y_4897_ = v___x_4901_;
v___y_4898_ = v___x_4902_;
v___y_4899_ = v___x_4902_;
goto v___jp_4896_;
}
}
}
}
}
}
}
else
{
v___y_4873_ = v___x_4901_;
goto v___jp_4872_;
}
}
else
{
uint8_t v___x_4908_; 
v___x_4908_ = 1;
v___y_4873_ = v___x_4908_;
goto v___jp_4872_;
}
v___jp_4726_:
{
lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4733_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_4733_, 0, v___y_4730_);
lean_ctor_set(v___x_4733_, 1, v___y_4728_);
lean_ctor_set(v___x_4733_, 2, v___y_4729_);
lean_ctor_set(v___x_4733_, 3, v___y_4727_);
lean_ctor_set(v___x_4733_, 4, v___y_4731_);
lean_ctor_set(v___x_4733_, 5, v_respStream_4711_);
lean_ctor_set(v___x_4733_, 6, v_requestBody_4724_);
lean_ctor_set(v___x_4733_, 7, v_connectionContext_4712_);
lean_ctor_set_uint8(v___x_4733_, sizeof(void*)*8, v___y_4732_);
v___x_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4733_);
v___x_4735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4735_, 0, v___x_4734_);
return v___x_4735_;
}
v___jp_4736_:
{
if (lean_obj_tag(v_timer_4713_) == 0)
{
v___y_4727_ = v___y_4737_;
v___y_4728_ = v___y_4739_;
v___y_4729_ = v___y_4740_;
v___y_4730_ = v___y_4741_;
v___y_4731_ = v___y_4742_;
v___y_4732_ = v___y_4738_;
goto v___jp_4726_;
}
else
{
uint8_t v___x_4743_; 
lean_dec(v_timer_4713_);
v___x_4743_ = 0;
v___y_4727_ = v___y_4737_;
v___y_4728_ = v___y_4739_;
v___y_4729_ = v___y_4740_;
v___y_4730_ = v___y_4741_;
v___y_4731_ = v___y_4742_;
v___y_4732_ = v___x_4743_;
goto v___jp_4726_;
}
}
v___jp_4744_:
{
if (v___y_4749_ == 0)
{
lean_object* v___x_4751_; 
lean_dec_ref(v_response_4714_);
v___x_4751_ = lean_box(0);
v___y_4737_ = v___y_4750_;
v___y_4738_ = v___y_4745_;
v___y_4739_ = v___y_4746_;
v___y_4740_ = v___y_4747_;
v___y_4741_ = v___y_4748_;
v___y_4742_ = v___x_4751_;
goto v___jp_4736_;
}
else
{
lean_object* v___x_4752_; 
v___x_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4752_, 0, v_response_4714_);
v___y_4737_ = v___y_4750_;
v___y_4738_ = v___y_4745_;
v___y_4739_ = v___y_4746_;
v___y_4740_ = v___y_4747_;
v___y_4741_ = v___y_4748_;
v___y_4742_ = v___x_4752_;
goto v___jp_4736_;
}
}
v___jp_4753_:
{
lean_object* v___x_4758_; 
v___x_4758_ = lean_box(0);
if (lean_obj_tag(v_inputWanted_4715_) == 0)
{
v___y_4745_ = v___y_4754_;
v___y_4746_ = v___y_4757_;
v___y_4747_ = v___x_4758_;
v___y_4748_ = v___y_4755_;
v___y_4749_ = v___y_4756_;
v___y_4750_ = v___x_4758_;
goto v___jp_4744_;
}
else
{
lean_object* v_val_4759_; 
v_val_4759_ = lean_ctor_get(v_inputWanted_4715_, 0);
lean_inc(v_val_4759_);
lean_dec_ref_known(v_inputWanted_4715_, 1);
v___y_4745_ = v___y_4754_;
v___y_4746_ = v___y_4757_;
v___y_4747_ = v___x_4758_;
v___y_4748_ = v___y_4755_;
v___y_4749_ = v___y_4756_;
v___y_4750_ = v_val_4759_;
goto v___jp_4744_;
}
}
v___jp_4760_:
{
if (v___y_4764_ == 0)
{
lean_object* v___x_4766_; 
lean_dec(v___y_4763_);
v___x_4766_ = lean_box(0);
v___y_4754_ = v___y_4761_;
v___y_4755_ = v___y_4765_;
v___y_4756_ = v___y_4762_;
v___y_4757_ = v___x_4766_;
goto v___jp_4753_;
}
else
{
v___y_4754_ = v___y_4761_;
v___y_4755_ = v___y_4765_;
v___y_4756_ = v___y_4762_;
v___y_4757_ = v___y_4763_;
goto v___jp_4753_;
}
}
v___jp_4767_:
{
lean_object* v___x_4772_; 
v___x_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4772_, 0, v_socket_4716_);
v___y_4761_ = v___y_4768_;
v___y_4762_ = v___y_4769_;
v___y_4763_ = v___y_4770_;
v___y_4764_ = v___y_4771_;
v___y_4765_ = v___x_4772_;
goto v___jp_4760_;
}
v___jp_4773_:
{
lean_object* v___x_4778_; 
v___x_4778_ = lean_box(0);
v___y_4761_ = v___y_4774_;
v___y_4762_ = v___y_4775_;
v___y_4763_ = v___y_4776_;
v___y_4764_ = v___y_4777_;
v___y_4765_ = v___x_4778_;
goto v___jp_4760_;
}
v___jp_4779_:
{
uint8_t v_peerClosed_4784_; 
v_peerClosed_4784_ = lean_ctor_get_uint8(v_reader_4717_, sizeof(void*)*6);
if (v_peerClosed_4784_ == 0)
{
uint8_t v_inputStopped_4785_; 
v_inputStopped_4785_ = lean_ctor_get_uint8(v_reader_4717_, sizeof(void*)*6 + 1);
if (v_inputStopped_4785_ == 0)
{
lean_object* v_input_4786_; lean_object* v_array_4787_; lean_object* v_idx_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; uint8_t v___x_4791_; 
v_input_4786_ = lean_ctor_get(v_reader_4717_, 1);
v_array_4787_ = lean_ctor_get(v_input_4786_, 0);
v_idx_4788_ = lean_ctor_get(v_input_4786_, 1);
v___x_4789_ = lean_byte_array_size(v_array_4787_);
v___x_4790_ = lean_nat_sub(v___x_4789_, v_idx_4788_);
v___x_4791_ = lean_nat_dec_le(v_inputLimit_4718_, v___x_4790_);
lean_dec(v___x_4790_);
if (v___x_4791_ == 0)
{
v___y_4768_ = v___y_4780_;
v___y_4769_ = v___y_4781_;
v___y_4770_ = v___y_4782_;
v___y_4771_ = v___y_4783_;
goto v___jp_4767_;
}
else
{
if (lean_obj_tag(v_inputWanted_4715_) == 0)
{
lean_dec(v_socket_4716_);
v___y_4774_ = v___y_4780_;
v___y_4775_ = v___y_4781_;
v___y_4776_ = v___y_4782_;
v___y_4777_ = v___y_4783_;
goto v___jp_4773_;
}
else
{
v___y_4768_ = v___y_4780_;
v___y_4769_ = v___y_4781_;
v___y_4770_ = v___y_4782_;
v___y_4771_ = v___y_4783_;
goto v___jp_4767_;
}
}
}
else
{
lean_dec(v_socket_4716_);
v___y_4774_ = v___y_4780_;
v___y_4775_ = v___y_4781_;
v___y_4776_ = v___y_4782_;
v___y_4777_ = v___y_4783_;
goto v___jp_4773_;
}
}
else
{
lean_dec(v_socket_4716_);
v___y_4774_ = v___y_4780_;
v___y_4775_ = v___y_4781_;
v___y_4776_ = v___y_4782_;
v___y_4777_ = v___y_4783_;
goto v___jp_4773_;
}
}
v___jp_4792_:
{
v___y_4780_ = v___y_4793_;
v___y_4781_ = v___y_4794_;
v___y_4782_ = v___y_4795_;
v___y_4783_ = v___y_4796_;
goto v___jp_4779_;
}
v___jp_4797_:
{
uint8_t v___x_4801_; 
v___x_4801_ = 1;
v___y_4780_ = v___y_4798_;
v___y_4781_ = v___y_4799_;
v___y_4782_ = v___y_4800_;
v___y_4783_ = v___x_4801_;
goto v___jp_4779_;
}
v___jp_4802_:
{
uint8_t v___x_4806_; 
v___x_4806_ = 0;
v___y_4774_ = v___y_4803_;
v___y_4775_ = v___y_4804_;
v___y_4776_ = v___y_4805_;
v___y_4777_ = v___x_4806_;
goto v___jp_4773_;
}
v___jp_4807_:
{
if (v___y_4811_ == 0)
{
v___y_4798_ = v___y_4808_;
v___y_4799_ = v___y_4809_;
v___y_4800_ = v___y_4810_;
goto v___jp_4797_;
}
else
{
lean_dec(v_socket_4716_);
v___y_4803_ = v___y_4808_;
v___y_4804_ = v___y_4809_;
v___y_4805_ = v___y_4810_;
goto v___jp_4802_;
}
}
v___jp_4812_:
{
if (v_pullBodyStalled_4719_ == 0)
{
lean_dec(v_socket_4716_);
v___y_4803_ = v___y_4813_;
v___y_4804_ = v___y_4815_;
v___y_4805_ = v___y_4816_;
goto v___jp_4802_;
}
else
{
v___y_4808_ = v___y_4813_;
v___y_4809_ = v___y_4815_;
v___y_4810_ = v___y_4816_;
v___y_4811_ = v___y_4814_;
goto v___jp_4807_;
}
}
v___jp_4817_:
{
lean_object* v_state_4823_; 
v_state_4823_ = lean_ctor_get(v_reader_4717_, 0);
if (lean_obj_tag(v_state_4823_) == 2)
{
v___y_4813_ = v___y_4818_;
v___y_4814_ = v___y_4820_;
v___y_4815_ = v___y_4819_;
v___y_4816_ = v___y_4821_;
goto v___jp_4812_;
}
else
{
if (v___y_4822_ == 0)
{
v___y_4798_ = v___y_4818_;
v___y_4799_ = v___y_4819_;
v___y_4800_ = v___y_4821_;
goto v___jp_4797_;
}
else
{
v___y_4813_ = v___y_4818_;
v___y_4814_ = v___y_4820_;
v___y_4815_ = v___y_4819_;
v___y_4816_ = v___y_4821_;
goto v___jp_4812_;
}
}
}
v___jp_4824_:
{
if (v_requestBodyOpen_4720_ == 0)
{
lean_dec(v_socket_4716_);
v___y_4774_ = v___y_4825_;
v___y_4775_ = v___y_4827_;
v___y_4776_ = v___y_4828_;
v___y_4777_ = v_requestBodyOpen_4720_;
goto v___jp_4773_;
}
else
{
switch(lean_obj_tag(v_state_4721_))
{
case 6:
{
v___y_4808_ = v___y_4825_;
v___y_4809_ = v___y_4827_;
v___y_4810_ = v___y_4828_;
v___y_4811_ = v___y_4826_;
goto v___jp_4807_;
}
case 7:
{
v___y_4808_ = v___y_4825_;
v___y_4809_ = v___y_4827_;
v___y_4810_ = v___y_4828_;
v___y_4811_ = v___y_4826_;
goto v___jp_4807_;
}
default: 
{
switch(lean_obj_tag(v_state_4721_))
{
case 0:
{
v___y_4818_ = v___y_4825_;
v___y_4819_ = v___y_4827_;
v___y_4820_ = v___y_4826_;
v___y_4821_ = v___y_4828_;
v___y_4822_ = v___y_4826_;
goto v___jp_4817_;
}
case 1:
{
v___y_4818_ = v___y_4825_;
v___y_4819_ = v___y_4827_;
v___y_4820_ = v___y_4826_;
v___y_4821_ = v___y_4828_;
v___y_4822_ = v___y_4826_;
goto v___jp_4817_;
}
default: 
{
lean_object* v_state_4829_; 
v_state_4829_ = lean_ctor_get(v_reader_4717_, 0);
if (lean_obj_tag(v_state_4829_) == 2)
{
lean_object* v_a_4830_; 
v_a_4830_ = lean_ctor_get(v_state_4829_, 0);
if (lean_obj_tag(v_a_4830_) == 0)
{
lean_object* v_remaining_4831_; lean_object* v___x_4832_; uint8_t v___x_4833_; 
v_remaining_4831_ = lean_ctor_get(v_a_4830_, 0);
v___x_4832_ = lean_unsigned_to_nat(0u);
v___x_4833_ = lean_nat_dec_eq(v_remaining_4831_, v___x_4832_);
if (v___x_4833_ == 0)
{
v___y_4818_ = v___y_4825_;
v___y_4819_ = v___y_4827_;
v___y_4820_ = v___y_4826_;
v___y_4821_ = v___y_4828_;
v___y_4822_ = v___x_4833_;
goto v___jp_4817_;
}
else
{
v___y_4808_ = v___y_4825_;
v___y_4809_ = v___y_4827_;
v___y_4810_ = v___y_4828_;
v___y_4811_ = v___y_4826_;
goto v___jp_4807_;
}
}
else
{
v___y_4818_ = v___y_4825_;
v___y_4819_ = v___y_4827_;
v___y_4820_ = v___y_4826_;
v___y_4821_ = v___y_4828_;
v___y_4822_ = v___y_4826_;
goto v___jp_4817_;
}
}
else
{
v___y_4818_ = v___y_4825_;
v___y_4819_ = v___y_4827_;
v___y_4820_ = v___y_4826_;
v___y_4821_ = v___y_4828_;
v___y_4822_ = v___y_4826_;
goto v___jp_4817_;
}
}
}
}
}
}
}
v___jp_4834_:
{
if (v_requestBodyInterested_4722_ == 0)
{
v___y_4825_ = v___y_4835_;
v___y_4826_ = v___y_4837_;
v___y_4827_ = v___y_4836_;
v___y_4828_ = v___y_4838_;
goto v___jp_4824_;
}
else
{
v___y_4793_ = v___y_4835_;
v___y_4794_ = v___y_4836_;
v___y_4795_ = v___y_4838_;
v___y_4796_ = v___y_4835_;
goto v___jp_4792_;
}
}
v___jp_4839_:
{
if (v___y_4844_ == 0)
{
v___y_4825_ = v___y_4840_;
v___y_4826_ = v___y_4842_;
v___y_4827_ = v___y_4841_;
v___y_4828_ = v___y_4843_;
goto v___jp_4824_;
}
else
{
v___y_4835_ = v___y_4840_;
v___y_4836_ = v___y_4841_;
v___y_4837_ = v___y_4842_;
v___y_4838_ = v___y_4843_;
goto v___jp_4834_;
}
}
v___jp_4845_:
{
lean_object* v_state_4851_; 
v_state_4851_ = lean_ctor_get(v_reader_4717_, 0);
if (lean_obj_tag(v_state_4851_) == 2)
{
v___y_4835_ = v___y_4846_;
v___y_4836_ = v___y_4848_;
v___y_4837_ = v___y_4847_;
v___y_4838_ = v___y_4849_;
goto v___jp_4834_;
}
else
{
v___y_4840_ = v___y_4846_;
v___y_4841_ = v___y_4848_;
v___y_4842_ = v___y_4847_;
v___y_4843_ = v___y_4849_;
v___y_4844_ = v___y_4850_;
goto v___jp_4839_;
}
}
v___jp_4852_:
{
switch(lean_obj_tag(v_state_4721_))
{
case 6:
{
v___y_4840_ = v___y_4853_;
v___y_4841_ = v___y_4854_;
v___y_4842_ = v___y_4855_;
v___y_4843_ = v___y_4856_;
v___y_4844_ = v___y_4855_;
goto v___jp_4839_;
}
case 7:
{
v___y_4840_ = v___y_4853_;
v___y_4841_ = v___y_4854_;
v___y_4842_ = v___y_4855_;
v___y_4843_ = v___y_4856_;
v___y_4844_ = v___y_4855_;
goto v___jp_4839_;
}
default: 
{
switch(lean_obj_tag(v_state_4721_))
{
case 0:
{
v___y_4846_ = v___y_4853_;
v___y_4847_ = v___y_4855_;
v___y_4848_ = v___y_4854_;
v___y_4849_ = v___y_4856_;
v___y_4850_ = v___y_4855_;
goto v___jp_4845_;
}
case 1:
{
v___y_4846_ = v___y_4853_;
v___y_4847_ = v___y_4855_;
v___y_4848_ = v___y_4854_;
v___y_4849_ = v___y_4856_;
v___y_4850_ = v___y_4855_;
goto v___jp_4845_;
}
default: 
{
lean_object* v_state_4857_; 
v_state_4857_ = lean_ctor_get(v_reader_4717_, 0);
if (lean_obj_tag(v_state_4857_) == 2)
{
lean_object* v_a_4858_; 
v_a_4858_ = lean_ctor_get(v_state_4857_, 0);
if (lean_obj_tag(v_a_4858_) == 0)
{
lean_object* v_remaining_4859_; lean_object* v___x_4860_; uint8_t v___x_4861_; 
v_remaining_4859_ = lean_ctor_get(v_a_4858_, 0);
v___x_4860_ = lean_unsigned_to_nat(0u);
v___x_4861_ = lean_nat_dec_eq(v_remaining_4859_, v___x_4860_);
if (v___x_4861_ == 0)
{
v___y_4846_ = v___y_4853_;
v___y_4847_ = v___y_4855_;
v___y_4848_ = v___y_4854_;
v___y_4849_ = v___y_4856_;
v___y_4850_ = v___x_4861_;
goto v___jp_4845_;
}
else
{
v___y_4840_ = v___y_4853_;
v___y_4841_ = v___y_4854_;
v___y_4842_ = v___y_4855_;
v___y_4843_ = v___y_4856_;
v___y_4844_ = v___y_4855_;
goto v___jp_4839_;
}
}
else
{
v___y_4846_ = v___y_4853_;
v___y_4847_ = v___y_4855_;
v___y_4848_ = v___y_4854_;
v___y_4849_ = v___y_4856_;
v___y_4850_ = v___y_4855_;
goto v___jp_4845_;
}
}
else
{
v___y_4846_ = v___y_4853_;
v___y_4847_ = v___y_4855_;
v___y_4848_ = v___y_4854_;
v___y_4849_ = v___y_4856_;
v___y_4850_ = v___y_4855_;
goto v___jp_4845_;
}
}
}
}
}
}
v___jp_4862_:
{
if (lean_obj_tag(v_respStream_4711_) == 0)
{
switch(lean_obj_tag(v_state_4721_))
{
case 0:
{
v___y_4853_ = v___y_4863_;
v___y_4854_ = v___y_4864_;
v___y_4855_ = v___y_4866_;
v___y_4856_ = v___y_4865_;
goto v___jp_4852_;
}
case 1:
{
v___y_4853_ = v___y_4863_;
v___y_4854_ = v___y_4864_;
v___y_4855_ = v___y_4866_;
v___y_4856_ = v___y_4865_;
goto v___jp_4852_;
}
default: 
{
v___y_4793_ = v___y_4863_;
v___y_4794_ = v___y_4864_;
v___y_4795_ = v___y_4865_;
v___y_4796_ = v___y_4863_;
goto v___jp_4792_;
}
}
}
else
{
v___y_4793_ = v___y_4863_;
v___y_4794_ = v___y_4864_;
v___y_4795_ = v___y_4865_;
v___y_4796_ = v___y_4863_;
goto v___jp_4792_;
}
}
v___jp_4867_:
{
uint8_t v___x_4870_; 
v___x_4870_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg(v_handler_4723_);
if (v___x_4870_ == 0)
{
v___y_4780_ = v___y_4868_;
v___y_4781_ = v___x_4870_;
v___y_4782_ = v___y_4869_;
v___y_4783_ = v___y_4868_;
goto v___jp_4779_;
}
else
{
uint8_t v___x_4871_; 
v___x_4871_ = 0;
v___y_4863_ = v___y_4868_;
v___y_4864_ = v___x_4870_;
v___y_4865_ = v___y_4869_;
v___y_4866_ = v___x_4871_;
goto v___jp_4862_;
}
}
v___jp_4872_:
{
lean_object* v___x_4874_; 
lean_inc(v_timer_4713_);
v___x_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4874_, 0, v_timer_4713_);
v___y_4868_ = v___y_4873_;
v___y_4869_ = v___x_4874_;
goto v___jp_4867_;
}
v___jp_4875_:
{
lean_object* v___x_4877_; 
v___x_4877_ = lean_box(0);
v___y_4868_ = v___y_4876_;
v___y_4869_ = v___x_4877_;
goto v___jp_4867_;
}
v___jp_4878_:
{
if (v___y_4880_ == 0)
{
v___y_4876_ = v___y_4879_;
goto v___jp_4875_;
}
else
{
v___y_4873_ = v___y_4879_;
goto v___jp_4872_;
}
}
v___jp_4881_:
{
lean_object* v_state_4884_; 
v_state_4884_ = lean_ctor_get(v_reader_4717_, 0);
if (lean_obj_tag(v_state_4884_) == 2)
{
v___y_4879_ = v___y_4882_;
v___y_4880_ = v_requestBodyInterested_4722_;
goto v___jp_4878_;
}
else
{
if (v___y_4883_ == 0)
{
v___y_4876_ = v___y_4882_;
goto v___jp_4875_;
}
else
{
v___y_4879_ = v___y_4882_;
v___y_4880_ = v_requestBodyInterested_4722_;
goto v___jp_4878_;
}
}
}
v___jp_4885_:
{
switch(lean_obj_tag(v_state_4721_))
{
case 6:
{
v___y_4879_ = v___y_4886_;
v___y_4880_ = v___y_4887_;
goto v___jp_4878_;
}
case 7:
{
v___y_4879_ = v___y_4886_;
v___y_4880_ = v___y_4887_;
goto v___jp_4878_;
}
default: 
{
switch(lean_obj_tag(v_state_4721_))
{
case 0:
{
v___y_4882_ = v___y_4886_;
v___y_4883_ = v___y_4887_;
goto v___jp_4881_;
}
case 1:
{
v___y_4882_ = v___y_4886_;
v___y_4883_ = v___y_4887_;
goto v___jp_4881_;
}
default: 
{
lean_object* v_state_4888_; 
v_state_4888_ = lean_ctor_get(v_reader_4717_, 0);
if (lean_obj_tag(v_state_4888_) == 2)
{
lean_object* v_a_4889_; 
v_a_4889_ = lean_ctor_get(v_state_4888_, 0);
if (lean_obj_tag(v_a_4889_) == 0)
{
lean_object* v_remaining_4890_; lean_object* v___x_4891_; uint8_t v___x_4892_; 
v_remaining_4890_ = lean_ctor_get(v_a_4889_, 0);
v___x_4891_ = lean_unsigned_to_nat(0u);
v___x_4892_ = lean_nat_dec_eq(v_remaining_4890_, v___x_4891_);
if (v___x_4892_ == 0)
{
v___y_4882_ = v___y_4886_;
v___y_4883_ = v___x_4892_;
goto v___jp_4881_;
}
else
{
v___y_4879_ = v___y_4886_;
v___y_4880_ = v___y_4887_;
goto v___jp_4878_;
}
}
else
{
v___y_4882_ = v___y_4886_;
v___y_4883_ = v___y_4887_;
goto v___jp_4881_;
}
}
else
{
v___y_4882_ = v___y_4886_;
v___y_4883_ = v___y_4887_;
goto v___jp_4881_;
}
}
}
}
}
}
v___jp_4893_:
{
if (v_pullBodyStalled_4719_ == 0)
{
v___y_4886_ = v___y_4894_;
v___y_4887_ = v___y_4895_;
goto v___jp_4885_;
}
else
{
v___y_4873_ = v___y_4894_;
goto v___jp_4872_;
}
}
v___jp_4896_:
{
lean_object* v_state_4900_; 
v_state_4900_ = lean_ctor_get(v_reader_4717_, 0);
if (lean_obj_tag(v_state_4900_) == 2)
{
v___y_4894_ = v___y_4897_;
v___y_4895_ = v___y_4898_;
goto v___jp_4893_;
}
else
{
if (v___y_4899_ == 0)
{
v___y_4873_ = v___y_4897_;
goto v___jp_4872_;
}
else
{
v___y_4894_ = v___y_4897_;
v___y_4895_ = v___y_4898_;
goto v___jp_4893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed(lean_object* v_respStream_4909_, lean_object* v_connectionContext_4910_, lean_object* v_timer_4911_, lean_object* v_response_4912_, lean_object* v_inputWanted_4913_, lean_object* v_socket_4914_, lean_object* v_reader_4915_, lean_object* v_inputLimit_4916_, lean_object* v_pullBodyStalled_4917_, lean_object* v_requestBodyOpen_4918_, lean_object* v_state_4919_, lean_object* v_requestBodyInterested_4920_, lean_object* v_handler_4921_, lean_object* v_requestBody_4922_, lean_object* v___y_4923_){
_start:
{
uint8_t v_pullBodyStalled_boxed_4924_; uint8_t v_requestBodyOpen_boxed_4925_; uint8_t v_requestBodyInterested_boxed_4926_; lean_object* v_res_4927_; 
v_pullBodyStalled_boxed_4924_ = lean_unbox(v_pullBodyStalled_4917_);
v_requestBodyOpen_boxed_4925_ = lean_unbox(v_requestBodyOpen_4918_);
v_requestBodyInterested_boxed_4926_ = lean_unbox(v_requestBodyInterested_4920_);
v_res_4927_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0(v_respStream_4909_, v_connectionContext_4910_, v_timer_4911_, v_response_4912_, v_inputWanted_4913_, v_socket_4914_, v_reader_4915_, v_inputLimit_4916_, v_pullBodyStalled_boxed_4924_, v_requestBodyOpen_boxed_4925_, v_state_4919_, v_requestBodyInterested_boxed_4926_, v_handler_4921_, v_requestBody_4922_);
lean_dec(v_handler_4921_);
lean_dec(v_state_4919_);
lean_dec(v_inputLimit_4916_);
lean_dec_ref(v_reader_4915_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(lean_object* v___f_4928_, lean_object* v_x_4929_){
_start:
{
if (lean_obj_tag(v_x_4929_) == 0)
{
lean_object* v_a_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4939_; 
lean_dec_ref(v___f_4928_);
v_a_4931_ = lean_ctor_get(v_x_4929_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v_x_4929_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4933_ = v_x_4929_;
v_isShared_4934_ = v_isSharedCheck_4939_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_a_4931_);
lean_dec(v_x_4929_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4939_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v___x_4936_; 
if (v_isShared_4934_ == 0)
{
v___x_4936_ = v___x_4933_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4931_);
v___x_4936_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
lean_object* v___x_4937_; 
v___x_4937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4936_);
return v___x_4937_;
}
}
}
else
{
lean_object* v_a_4940_; lean_object* v___x_4941_; 
v_a_4940_ = lean_ctor_get(v_x_4929_, 0);
lean_inc(v_a_4940_);
lean_dec_ref_known(v_x_4929_, 1);
v___x_4941_ = lean_apply_2(v___f_4928_, v_a_4940_, lean_box(0));
return v___x_4941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed(lean_object* v___f_4942_, lean_object* v_x_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1(v___f_4942_, v_x_4943_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(lean_object* v_respStream_4950_, lean_object* v_connectionContext_4951_, lean_object* v_timer_4952_, lean_object* v_response_4953_, lean_object* v_inputWanted_4954_, lean_object* v_socket_4955_, lean_object* v_reader_4956_, lean_object* v_inputLimit_4957_, uint8_t v_pullBodyStalled_4958_, uint8_t v_requestBodyOpen_4959_, lean_object* v_state_4960_, lean_object* v_handler_4961_, lean_object* v_requestStream_4962_, uint8_t v_requestBodyInterested_4963_){
_start:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___f_4968_; lean_object* v___f_4969_; uint8_t v___y_4971_; 
v___x_4965_ = lean_box(v_pullBodyStalled_4958_);
v___x_4966_ = lean_box(v_requestBodyOpen_4959_);
v___x_4967_ = lean_box(v_requestBodyInterested_4963_);
lean_inc(v_state_4960_);
lean_inc_ref(v_reader_4956_);
v___f_4968_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__0___boxed), 15, 13);
lean_closure_set(v___f_4968_, 0, v_respStream_4950_);
lean_closure_set(v___f_4968_, 1, v_connectionContext_4951_);
lean_closure_set(v___f_4968_, 2, v_timer_4952_);
lean_closure_set(v___f_4968_, 3, v_response_4953_);
lean_closure_set(v___f_4968_, 4, v_inputWanted_4954_);
lean_closure_set(v___f_4968_, 5, v_socket_4955_);
lean_closure_set(v___f_4968_, 6, v_reader_4956_);
lean_closure_set(v___f_4968_, 7, v_inputLimit_4957_);
lean_closure_set(v___f_4968_, 8, v___x_4965_);
lean_closure_set(v___f_4968_, 9, v___x_4966_);
lean_closure_set(v___f_4968_, 10, v_state_4960_);
lean_closure_set(v___f_4968_, 11, v___x_4967_);
lean_closure_set(v___f_4968_, 12, v_handler_4961_);
v___f_4969_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4969_, 0, v___f_4968_);
switch(lean_obj_tag(v_state_4960_))
{
case 6:
{
uint8_t v___x_4975_; 
lean_dec_ref(v_requestStream_4962_);
lean_dec_ref(v_reader_4956_);
v___x_4975_ = 0;
v___y_4971_ = v___x_4975_;
goto v___jp_4970_;
}
case 7:
{
uint8_t v___x_4976_; 
lean_dec_ref(v_requestStream_4962_);
lean_dec_ref(v_reader_4956_);
v___x_4976_ = 0;
v___y_4971_ = v___x_4976_;
goto v___jp_4970_;
}
default: 
{
uint8_t v___y_4985_; 
switch(lean_obj_tag(v_state_4960_))
{
case 0:
{
uint8_t v___x_4987_; 
v___x_4987_ = 0;
v___y_4985_ = v___x_4987_;
goto v___jp_4984_;
}
case 1:
{
uint8_t v___x_4988_; 
v___x_4988_ = 0;
v___y_4985_ = v___x_4988_;
goto v___jp_4984_;
}
default: 
{
lean_object* v_state_4989_; 
lean_dec(v_state_4960_);
v_state_4989_ = lean_ctor_get(v_reader_4956_, 0);
if (lean_obj_tag(v_state_4989_) == 2)
{
lean_object* v_a_4990_; 
v_a_4990_ = lean_ctor_get(v_state_4989_, 0);
if (lean_obj_tag(v_a_4990_) == 0)
{
lean_object* v_remaining_4991_; lean_object* v___x_4992_; uint8_t v___x_4993_; 
v_remaining_4991_ = lean_ctor_get(v_a_4990_, 0);
v___x_4992_ = lean_unsigned_to_nat(0u);
v___x_4993_ = lean_nat_dec_eq(v_remaining_4991_, v___x_4992_);
if (v___x_4993_ == 0)
{
v___y_4985_ = v___x_4993_;
goto v___jp_4984_;
}
else
{
uint8_t v___x_4994_; 
lean_dec_ref(v_requestStream_4962_);
lean_dec_ref(v_reader_4956_);
v___x_4994_ = 0;
v___y_4971_ = v___x_4994_;
goto v___jp_4970_;
}
}
else
{
uint8_t v___x_4995_; 
v___x_4995_ = 0;
v___y_4985_ = v___x_4995_;
goto v___jp_4984_;
}
}
else
{
uint8_t v___x_4996_; 
v___x_4996_ = 0;
v___y_4985_ = v___x_4996_;
goto v___jp_4984_;
}
}
}
v___jp_4977_:
{
if (v_pullBodyStalled_4958_ == 0)
{
if (v_requestBodyOpen_4959_ == 0)
{
lean_dec_ref(v_requestStream_4962_);
v___y_4971_ = v_requestBodyOpen_4959_;
goto v___jp_4970_;
}
else
{
lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4978_, 0, v_requestStream_4962_);
v___x_4979_ = lean_unsigned_to_nat(0u);
v___x_4980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4978_);
v___x_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4980_);
v___x_4982_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4979_, v_pullBodyStalled_4958_, v___x_4981_, v___f_4969_);
return v___x_4982_;
}
}
else
{
uint8_t v___x_4983_; 
lean_dec_ref(v_requestStream_4962_);
v___x_4983_ = 0;
v___y_4971_ = v___x_4983_;
goto v___jp_4970_;
}
}
v___jp_4984_:
{
lean_object* v_state_4986_; 
v_state_4986_ = lean_ctor_get(v_reader_4956_, 0);
lean_inc(v_state_4986_);
lean_dec_ref(v_reader_4956_);
if (lean_obj_tag(v_state_4986_) == 2)
{
lean_dec_ref_known(v_state_4986_, 1);
goto v___jp_4977_;
}
else
{
lean_dec(v_state_4986_);
if (v___y_4985_ == 0)
{
lean_dec_ref(v_requestStream_4962_);
v___y_4971_ = v___y_4985_;
goto v___jp_4970_;
}
else
{
goto v___jp_4977_;
}
}
}
}
}
v___jp_4970_:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___x_4972_ = lean_unsigned_to_nat(0u);
v___x_4973_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___closed__1));
v___x_4974_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4972_, v___y_4971_, v___x_4973_, v___f_4969_);
return v___x_4974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed(lean_object* v_respStream_4997_, lean_object* v_connectionContext_4998_, lean_object* v_timer_4999_, lean_object* v_response_5000_, lean_object* v_inputWanted_5001_, lean_object* v_socket_5002_, lean_object* v_reader_5003_, lean_object* v_inputLimit_5004_, lean_object* v_pullBodyStalled_5005_, lean_object* v_requestBodyOpen_5006_, lean_object* v_state_5007_, lean_object* v_handler_5008_, lean_object* v_requestStream_5009_, lean_object* v_requestBodyInterested_5010_, lean_object* v___y_5011_){
_start:
{
uint8_t v_pullBodyStalled_boxed_5012_; uint8_t v_requestBodyOpen_boxed_5013_; uint8_t v_requestBodyInterested_boxed_5014_; lean_object* v_res_5015_; 
v_pullBodyStalled_boxed_5012_ = lean_unbox(v_pullBodyStalled_5005_);
v_requestBodyOpen_boxed_5013_ = lean_unbox(v_requestBodyOpen_5006_);
v_requestBodyInterested_boxed_5014_ = lean_unbox(v_requestBodyInterested_5010_);
v_res_5015_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3(v_respStream_4997_, v_connectionContext_4998_, v_timer_4999_, v_response_5000_, v_inputWanted_5001_, v_socket_5002_, v_reader_5003_, v_inputLimit_5004_, v_pullBodyStalled_boxed_5012_, v_requestBodyOpen_boxed_5013_, v_state_5007_, v_handler_5008_, v_requestStream_5009_, v_requestBodyInterested_boxed_5014_);
return v_res_5015_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(lean_object* v___f_5016_, lean_object* v_x_5017_){
_start:
{
if (lean_obj_tag(v_x_5017_) == 0)
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5027_; 
lean_dec_ref(v___f_5016_);
v_a_5019_ = lean_ctor_get(v_x_5017_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v_x_5017_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5021_ = v_x_5017_;
v_isShared_5022_ = v_isSharedCheck_5027_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v_x_5017_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5027_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_5022_ == 0)
{
v___x_5024_ = v___x_5021_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_a_5019_);
v___x_5024_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
lean_object* v___x_5025_; 
v___x_5025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5025_, 0, v___x_5024_);
return v___x_5025_;
}
}
}
else
{
lean_object* v_a_5028_; lean_object* v___x_5029_; 
v_a_5028_ = lean_ctor_get(v_x_5017_, 0);
lean_inc(v_a_5028_);
lean_dec_ref_known(v_x_5017_, 1);
v___x_5029_ = lean_apply_2(v___f_5016_, v_a_5028_, lean_box(0));
return v___x_5029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed(lean_object* v___f_5030_, lean_object* v_x_5031_, lean_object* v___y_5032_){
_start:
{
lean_object* v_res_5033_; 
v_res_5033_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2(v___f_5030_, v_x_5031_);
return v_res_5033_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(lean_object* v_respStream_5034_, lean_object* v_connectionContext_5035_, lean_object* v_timer_5036_, lean_object* v_response_5037_, lean_object* v_inputWanted_5038_, lean_object* v_socket_5039_, lean_object* v_reader_5040_, lean_object* v_inputLimit_5041_, uint8_t v_pullBodyStalled_5042_, lean_object* v_state_5043_, lean_object* v_handler_5044_, lean_object* v_requestStream_5045_, uint8_t v_requestBodyOpen_5046_){
_start:
{
lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___f_5050_; lean_object* v___f_5051_; uint8_t v___y_5053_; 
v___x_5048_ = lean_box(v_pullBodyStalled_5042_);
v___x_5049_ = lean_box(v_requestBodyOpen_5046_);
lean_inc_ref(v_requestStream_5045_);
lean_inc(v_state_5043_);
lean_inc_ref(v_reader_5040_);
v___f_5050_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__3___boxed), 15, 13);
lean_closure_set(v___f_5050_, 0, v_respStream_5034_);
lean_closure_set(v___f_5050_, 1, v_connectionContext_5035_);
lean_closure_set(v___f_5050_, 2, v_timer_5036_);
lean_closure_set(v___f_5050_, 3, v_response_5037_);
lean_closure_set(v___f_5050_, 4, v_inputWanted_5038_);
lean_closure_set(v___f_5050_, 5, v_socket_5039_);
lean_closure_set(v___f_5050_, 6, v_reader_5040_);
lean_closure_set(v___f_5050_, 7, v_inputLimit_5041_);
lean_closure_set(v___f_5050_, 8, v___x_5048_);
lean_closure_set(v___f_5050_, 9, v___x_5049_);
lean_closure_set(v___f_5050_, 10, v_state_5043_);
lean_closure_set(v___f_5050_, 11, v_handler_5044_);
lean_closure_set(v___f_5050_, 12, v_requestStream_5045_);
v___f_5051_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5051_, 0, v___f_5050_);
switch(lean_obj_tag(v_state_5043_))
{
case 6:
{
uint8_t v___x_5059_; 
lean_dec_ref(v_requestStream_5045_);
lean_dec_ref(v_reader_5040_);
v___x_5059_ = 0;
v___y_5053_ = v___x_5059_;
goto v___jp_5052_;
}
case 7:
{
uint8_t v___x_5060_; 
lean_dec_ref(v_requestStream_5045_);
lean_dec_ref(v_reader_5040_);
v___x_5060_ = 0;
v___y_5053_ = v___x_5060_;
goto v___jp_5052_;
}
default: 
{
uint8_t v___y_5067_; 
switch(lean_obj_tag(v_state_5043_))
{
case 0:
{
uint8_t v___x_5069_; 
v___x_5069_ = 0;
v___y_5067_ = v___x_5069_;
goto v___jp_5066_;
}
case 1:
{
uint8_t v___x_5070_; 
v___x_5070_ = 0;
v___y_5067_ = v___x_5070_;
goto v___jp_5066_;
}
default: 
{
lean_object* v_state_5071_; 
lean_dec(v_state_5043_);
v_state_5071_ = lean_ctor_get(v_reader_5040_, 0);
if (lean_obj_tag(v_state_5071_) == 2)
{
lean_object* v_a_5072_; 
v_a_5072_ = lean_ctor_get(v_state_5071_, 0);
if (lean_obj_tag(v_a_5072_) == 0)
{
lean_object* v_remaining_5073_; lean_object* v___x_5074_; uint8_t v___x_5075_; 
v_remaining_5073_ = lean_ctor_get(v_a_5072_, 0);
v___x_5074_ = lean_unsigned_to_nat(0u);
v___x_5075_ = lean_nat_dec_eq(v_remaining_5073_, v___x_5074_);
if (v___x_5075_ == 0)
{
v___y_5067_ = v___x_5075_;
goto v___jp_5066_;
}
else
{
uint8_t v___x_5076_; 
lean_dec_ref(v_requestStream_5045_);
lean_dec_ref(v_reader_5040_);
v___x_5076_ = 0;
v___y_5053_ = v___x_5076_;
goto v___jp_5052_;
}
}
else
{
uint8_t v___x_5077_; 
v___x_5077_ = 0;
v___y_5067_ = v___x_5077_;
goto v___jp_5066_;
}
}
else
{
uint8_t v___x_5078_; 
v___x_5078_ = 0;
v___y_5067_ = v___x_5078_;
goto v___jp_5066_;
}
}
}
v___jp_5061_:
{
if (v_requestBodyOpen_5046_ == 0)
{
lean_dec_ref(v_requestStream_5045_);
v___y_5053_ = v_requestBodyOpen_5046_;
goto v___jp_5052_;
}
else
{
lean_object* v___x_5062_; uint8_t v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5062_ = lean_unsigned_to_nat(0u);
v___x_5063_ = 0;
v___x_5064_ = l_Std_Http_Body_Stream_hasInterest(v_requestStream_5045_);
v___x_5065_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5062_, v___x_5063_, v___x_5064_, v___f_5051_);
return v___x_5065_;
}
}
v___jp_5066_:
{
lean_object* v_state_5068_; 
v_state_5068_ = lean_ctor_get(v_reader_5040_, 0);
lean_inc(v_state_5068_);
lean_dec_ref(v_reader_5040_);
if (lean_obj_tag(v_state_5068_) == 2)
{
lean_dec_ref_known(v_state_5068_, 1);
goto v___jp_5061_;
}
else
{
lean_dec(v_state_5068_);
if (v___y_5067_ == 0)
{
lean_dec_ref(v_requestStream_5045_);
v___y_5053_ = v___y_5067_;
goto v___jp_5052_;
}
else
{
goto v___jp_5061_;
}
}
}
}
}
v___jp_5052_:
{
lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
v___x_5054_ = lean_unsigned_to_nat(0u);
v___x_5055_ = lean_box(v___y_5053_);
v___x_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5056_, 0, v___x_5055_);
v___x_5057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5056_);
v___x_5058_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5054_, v___y_5053_, v___x_5057_, v___f_5051_);
return v___x_5058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed(lean_object* v_respStream_5079_, lean_object* v_connectionContext_5080_, lean_object* v_timer_5081_, lean_object* v_response_5082_, lean_object* v_inputWanted_5083_, lean_object* v_socket_5084_, lean_object* v_reader_5085_, lean_object* v_inputLimit_5086_, lean_object* v_pullBodyStalled_5087_, lean_object* v_state_5088_, lean_object* v_handler_5089_, lean_object* v_requestStream_5090_, lean_object* v_requestBodyOpen_5091_, lean_object* v___y_5092_){
_start:
{
uint8_t v_pullBodyStalled_boxed_5093_; uint8_t v_requestBodyOpen_boxed_5094_; lean_object* v_res_5095_; 
v_pullBodyStalled_boxed_5093_ = lean_unbox(v_pullBodyStalled_5087_);
v_requestBodyOpen_boxed_5094_ = lean_unbox(v_requestBodyOpen_5091_);
v_res_5095_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5(v_respStream_5079_, v_connectionContext_5080_, v_timer_5081_, v_response_5082_, v_inputWanted_5083_, v_socket_5084_, v_reader_5085_, v_inputLimit_5086_, v_pullBodyStalled_boxed_5093_, v_state_5088_, v_handler_5089_, v_requestStream_5090_, v_requestBodyOpen_boxed_5094_);
return v_res_5095_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7(lean_object* v___f_5096_, uint8_t v___y_5097_, lean_object* v_x_5098_){
_start:
{
uint8_t v___y_5101_; 
if (lean_obj_tag(v_x_5098_) == 0)
{
lean_object* v_a_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5116_; 
lean_dec_ref(v___f_5096_);
v_a_5108_ = lean_ctor_get(v_x_5098_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v_x_5098_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5110_ = v_x_5098_;
v_isShared_5111_ = v_isSharedCheck_5116_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_a_5108_);
lean_dec(v_x_5098_);
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
lean_object* v_a_5117_; uint8_t v___x_5118_; 
v_a_5117_ = lean_ctor_get(v_x_5098_, 0);
lean_inc(v_a_5117_);
lean_dec_ref_known(v_x_5098_, 1);
v___x_5118_ = lean_unbox(v_a_5117_);
lean_dec(v_a_5117_);
if (v___x_5118_ == 0)
{
v___y_5101_ = v___y_5097_;
goto v___jp_5100_;
}
else
{
uint8_t v___x_5119_; 
v___x_5119_ = 0;
v___y_5101_ = v___x_5119_;
goto v___jp_5100_;
}
}
v___jp_5100_:
{
lean_object* v___x_5102_; uint8_t v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5102_ = lean_unsigned_to_nat(0u);
v___x_5103_ = 0;
v___x_5104_ = lean_box(v___y_5101_);
v___x_5105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5104_);
v___x_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5105_);
v___x_5107_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5102_, v___x_5103_, v___x_5106_, v___f_5096_);
return v___x_5107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7___boxed(lean_object* v___f_5120_, lean_object* v___y_5121_, lean_object* v_x_5122_, lean_object* v___y_5123_){
_start:
{
uint8_t v___y_4876__boxed_5124_; lean_object* v_res_5125_; 
v___y_4876__boxed_5124_ = lean_unbox(v___y_5121_);
v_res_5125_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7(v___f_5120_, v___y_4876__boxed_5124_, v_x_5122_);
return v_res_5125_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4(uint8_t v___y_5126_, lean_object* v_____do__lift_5127_, lean_object* v___y_5128_){
_start:
{
uint8_t v___y_5131_; lean_object* v_ended_5135_; 
v_ended_5135_ = lean_ctor_get(v_____do__lift_5127_, 3);
if (lean_obj_tag(v_ended_5135_) == 0)
{
uint8_t v___x_5136_; 
v___x_5136_ = 0;
v___y_5131_ = v___x_5136_;
goto v___jp_5130_;
}
else
{
v___y_5131_ = v___y_5126_;
goto v___jp_5130_;
}
v___jp_5130_:
{
lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; 
v___x_5132_ = lean_box(v___y_5131_);
v___x_5133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5133_, 0, v___x_5132_);
v___x_5134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5134_, 0, v___x_5133_);
return v___x_5134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4___boxed(lean_object* v___y_5137_, lean_object* v_____do__lift_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_){
_start:
{
uint8_t v___y_4927__boxed_5141_; lean_object* v_res_5142_; 
v___y_4927__boxed_5141_ = lean_unbox(v___y_5137_);
v_res_5142_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4(v___y_4927__boxed_5141_, v_____do__lift_5138_, v___y_5139_);
lean_dec(v___y_5139_);
lean_dec_ref(v_____do__lift_5138_);
return v_res_5142_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3(void){
_start:
{
lean_object* v___x_5150_; lean_object* v___f_5151_; lean_object* v___f_5152_; 
v___x_5150_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__1, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__1_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__1);
v___f_5151_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__2));
v___f_5152_ = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(v___f_5152_, 0, v___f_5151_);
lean_closure_set(v___f_5152_, 1, v___x_5150_);
return v___f_5152_;
}
}
static lean_object* _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4(void){
_start:
{
lean_object* v___f_5153_; lean_object* v___x_5154_; 
v___f_5153_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__3);
v___x_5154_ = lean_alloc_closure((void*)(l_StateRefT_x27_get___boxed), 5, 4);
lean_closure_set(v___x_5154_, 0, lean_box(0));
lean_closure_set(v___x_5154_, 1, lean_box(0));
lean_closure_set(v___x_5154_, 2, lean_box(0));
lean_closure_set(v___x_5154_, 3, v___f_5153_);
return v___x_5154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(lean_object* v_socket_5155_, lean_object* v_connectionContext_5156_, lean_object* v_state_5157_, lean_object* v_inputWanted_5158_, lean_object* v_inputLimit_5159_){
_start:
{
lean_object* v_machine_5161_; lean_object* v_writer_5162_; lean_object* v_requestStream_5163_; lean_object* v_timer_5164_; lean_object* v_response_5165_; lean_object* v_respStream_5166_; lean_object* v_handler_5167_; lean_object* v_reader_5168_; uint8_t v_pullBodyStalled_5169_; lean_object* v_state_5170_; lean_object* v___x_5171_; lean_object* v___f_5172_; lean_object* v___f_5173_; uint8_t v___y_5175_; 
v_machine_5161_ = lean_ctor_get(v_state_5157_, 0);
lean_inc_ref(v_machine_5161_);
v_writer_5162_ = lean_ctor_get(v_machine_5161_, 1);
lean_inc_ref(v_writer_5162_);
v_requestStream_5163_ = lean_ctor_get(v_state_5157_, 1);
lean_inc_ref_n(v_requestStream_5163_, 2);
v_timer_5164_ = lean_ctor_get(v_state_5157_, 2);
lean_inc(v_timer_5164_);
v_response_5165_ = lean_ctor_get(v_state_5157_, 3);
lean_inc_ref(v_response_5165_);
v_respStream_5166_ = lean_ctor_get(v_state_5157_, 4);
lean_inc(v_respStream_5166_);
v_handler_5167_ = lean_ctor_get(v_state_5157_, 6);
lean_inc(v_handler_5167_);
lean_dec_ref(v_state_5157_);
v_reader_5168_ = lean_ctor_get(v_machine_5161_, 0);
lean_inc_ref_n(v_reader_5168_, 2);
v_pullBodyStalled_5169_ = lean_ctor_get_uint8(v_machine_5161_, sizeof(void*)*6 + 1);
lean_dec_ref(v_machine_5161_);
v_state_5170_ = lean_ctor_get(v_writer_5162_, 2);
lean_inc_n(v_state_5170_, 2);
lean_dec_ref(v_writer_5162_);
v___x_5171_ = lean_box(v_pullBodyStalled_5169_);
v___f_5172_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__5___boxed), 14, 12);
lean_closure_set(v___f_5172_, 0, v_respStream_5166_);
lean_closure_set(v___f_5172_, 1, v_connectionContext_5156_);
lean_closure_set(v___f_5172_, 2, v_timer_5164_);
lean_closure_set(v___f_5172_, 3, v_response_5165_);
lean_closure_set(v___f_5172_, 4, v_inputWanted_5158_);
lean_closure_set(v___f_5172_, 5, v_socket_5155_);
lean_closure_set(v___f_5172_, 6, v_reader_5168_);
lean_closure_set(v___f_5172_, 7, v_inputLimit_5159_);
lean_closure_set(v___f_5172_, 8, v___x_5171_);
lean_closure_set(v___f_5172_, 9, v_state_5170_);
lean_closure_set(v___f_5172_, 10, v_handler_5167_);
lean_closure_set(v___f_5172_, 11, v_requestStream_5163_);
v___f_5173_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5173_, 0, v___f_5172_);
switch(lean_obj_tag(v_state_5170_))
{
case 6:
{
uint8_t v___x_5181_; 
lean_dec_ref(v_reader_5168_);
lean_dec_ref(v_requestStream_5163_);
v___x_5181_ = 0;
v___y_5175_ = v___x_5181_;
goto v___jp_5174_;
}
case 7:
{
uint8_t v___x_5182_; 
lean_dec_ref(v_reader_5168_);
lean_dec_ref(v_requestStream_5163_);
v___x_5182_ = 0;
v___y_5175_ = v___x_5182_;
goto v___jp_5174_;
}
default: 
{
uint8_t v___y_5184_; uint8_t v___y_5200_; 
switch(lean_obj_tag(v_state_5170_))
{
case 0:
{
uint8_t v___x_5203_; 
v___x_5203_ = 0;
v___y_5200_ = v___x_5203_;
goto v___jp_5199_;
}
case 1:
{
uint8_t v___x_5204_; 
v___x_5204_ = 0;
v___y_5200_ = v___x_5204_;
goto v___jp_5199_;
}
default: 
{
lean_object* v_state_5205_; 
lean_dec(v_state_5170_);
v_state_5205_ = lean_ctor_get(v_reader_5168_, 0);
if (lean_obj_tag(v_state_5205_) == 2)
{
lean_object* v_a_5206_; 
v_a_5206_ = lean_ctor_get(v_state_5205_, 0);
if (lean_obj_tag(v_a_5206_) == 0)
{
lean_object* v_remaining_5207_; lean_object* v___x_5208_; uint8_t v___x_5209_; 
v_remaining_5207_ = lean_ctor_get(v_a_5206_, 0);
v___x_5208_ = lean_unsigned_to_nat(0u);
v___x_5209_ = lean_nat_dec_eq(v_remaining_5207_, v___x_5208_);
if (v___x_5209_ == 0)
{
v___y_5200_ = v___x_5209_;
goto v___jp_5199_;
}
else
{
uint8_t v___x_5210_; 
lean_dec_ref(v_reader_5168_);
lean_dec_ref(v_requestStream_5163_);
v___x_5210_ = 0;
v___y_5175_ = v___x_5210_;
goto v___jp_5174_;
}
}
else
{
uint8_t v___x_5211_; 
v___x_5211_ = 0;
v___y_5200_ = v___x_5211_;
goto v___jp_5199_;
}
}
else
{
uint8_t v___x_5212_; 
v___x_5212_ = 0;
v___y_5200_ = v___x_5212_;
goto v___jp_5199_;
}
}
}
v___jp_5183_:
{
lean_object* v___x_5185_; lean_object* v___f_5186_; lean_object* v___x_5187_; lean_object* v___f_5188_; lean_object* v___x_5189_; uint8_t v___x_5190_; lean_object* v___x_5191_; lean_object* v___f_5192_; lean_object* v___f_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_3805__overap_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; 
v___x_5185_ = lean_box(v___y_5184_);
v___f_5186_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__7___boxed), 4, 2);
lean_closure_set(v___f_5186_, 0, v___f_5173_);
lean_closure_set(v___f_5186_, 1, v___x_5185_);
v___x_5187_ = lean_box(v___y_5184_);
v___f_5188_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___lam__4___boxed), 4, 1);
lean_closure_set(v___f_5188_, 0, v___x_5187_);
v___x_5189_ = lean_unsigned_to_nat(0u);
v___x_5190_ = 0;
v___x_5191_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__0, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__0_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__0);
v___f_5192_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__5, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__5_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__5);
v___f_5193_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg___lam__15___closed__6));
v___x_5194_ = lean_obj_once(&l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4, &l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4_once, _init_l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___closed__4);
v___x_5195_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_5195_, 0, lean_box(0));
lean_closure_set(v___x_5195_, 1, lean_box(0));
lean_closure_set(v___x_5195_, 2, v___x_5191_);
lean_closure_set(v___x_5195_, 3, lean_box(0));
lean_closure_set(v___x_5195_, 4, lean_box(0));
lean_closure_set(v___x_5195_, 5, v___x_5194_);
lean_closure_set(v___x_5195_, 6, v___f_5188_);
v___x_3805__overap_5196_ = l_Std_Mutex_atomically___redArg(v___x_5191_, v___f_5192_, v___f_5193_, v_requestStream_5163_, v___x_5195_);
v___x_5197_ = lean_apply_1(v___x_3805__overap_5196_, lean_box(0));
v___x_5198_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5189_, v___x_5190_, v___x_5197_, v___f_5186_);
return v___x_5198_;
}
v___jp_5199_:
{
lean_object* v_state_5201_; 
v_state_5201_ = lean_ctor_get(v_reader_5168_, 0);
lean_inc(v_state_5201_);
lean_dec_ref(v_reader_5168_);
if (lean_obj_tag(v_state_5201_) == 2)
{
uint8_t v___x_5202_; 
lean_dec_ref_known(v_state_5201_, 1);
v___x_5202_ = 1;
v___y_5184_ = v___x_5202_;
goto v___jp_5183_;
}
else
{
lean_dec(v_state_5201_);
if (v___y_5200_ == 0)
{
lean_dec_ref(v_requestStream_5163_);
v___y_5175_ = v___y_5200_;
goto v___jp_5174_;
}
else
{
v___y_5184_ = v___y_5200_;
goto v___jp_5183_;
}
}
}
}
}
v___jp_5174_:
{
lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; 
v___x_5176_ = lean_unsigned_to_nat(0u);
v___x_5177_ = lean_box(v___y_5175_);
v___x_5178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5178_, 0, v___x_5177_);
v___x_5179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5179_, 0, v___x_5178_);
v___x_5180_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5176_, v___y_5175_, v___x_5179_, v___f_5173_);
return v___x_5180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg___boxed(lean_object* v_socket_5213_, lean_object* v_connectionContext_5214_, lean_object* v_state_5215_, lean_object* v_inputWanted_5216_, lean_object* v_inputLimit_5217_, lean_object* v_a_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_5213_, v_connectionContext_5214_, v_state_5215_, v_inputWanted_5216_, v_inputLimit_5217_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(lean_object* v_00_u03b1_5220_, lean_object* v_00_u03b2_5221_, lean_object* v_inst_5222_, lean_object* v_socket_5223_, lean_object* v_connectionContext_5224_, lean_object* v_state_5225_, lean_object* v_inputWanted_5226_, lean_object* v_inputLimit_5227_){
_start:
{
lean_object* v___x_5229_; 
v___x_5229_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_5223_, v_connectionContext_5224_, v_state_5225_, v_inputWanted_5226_, v_inputLimit_5227_);
return v___x_5229_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___boxed(lean_object* v_00_u03b1_5230_, lean_object* v_00_u03b2_5231_, lean_object* v_inst_5232_, lean_object* v_socket_5233_, lean_object* v_connectionContext_5234_, lean_object* v_state_5235_, lean_object* v_inputWanted_5236_, lean_object* v_inputLimit_5237_, lean_object* v_a_5238_){
_start:
{
lean_object* v_res_5239_; 
v_res_5239_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources(v_00_u03b1_5230_, v_00_u03b2_5231_, v_inst_5232_, v_socket_5233_, v_connectionContext_5234_, v_state_5235_, v_inputWanted_5236_, v_inputLimit_5237_);
lean_dec_ref(v_inst_5232_);
return v_res_5239_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput(lean_object* v_x_5240_){
_start:
{
switch(lean_obj_tag(v_x_5240_))
{
case 0:
{
lean_object* v_head_5241_; uint8_t v_method_5242_; uint8_t v___x_5243_; 
v_head_5241_ = lean_ctor_get(v_x_5240_, 0);
v_method_5242_ = lean_ctor_get_uint8(v_head_5241_, sizeof(void*)*2);
v___x_5243_ = l_Std_Http_Method_isSafe(v_method_5242_);
if (v___x_5243_ == 0)
{
uint8_t v___x_5244_; 
v___x_5244_ = 1;
return v___x_5244_;
}
else
{
uint8_t v___x_5245_; 
v___x_5245_ = 0;
return v___x_5245_;
}
}
case 7:
{
uint8_t v___x_5246_; 
v___x_5246_ = 1;
return v___x_5246_;
}
default: 
{
uint8_t v___x_5247_; 
v___x_5247_ = 0;
return v___x_5247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput___boxed(lean_object* v_x_5248_){
_start:
{
uint8_t v_res_5249_; lean_object* v_r_5250_; 
v_res_5249_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_needsWrittenOutput(v_x_5248_);
lean_dec(v_x_5248_);
v_r_5250_ = lean_box(v_res_5249_);
return v_r_5250_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0(lean_object* v_inst_5251_, lean_object* v_handler_5252_, lean_object* v_x_5253_){
_start:
{
if (lean_obj_tag(v_x_5253_) == 0)
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5263_; 
lean_dec(v_handler_5252_);
lean_dec_ref(v_inst_5251_);
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
lean_object* v_a_5264_; 
v_a_5264_ = lean_ctor_get(v_x_5253_, 0);
lean_inc(v_a_5264_);
lean_dec_ref_known(v_x_5253_, 1);
if (lean_obj_tag(v_a_5264_) == 1)
{
lean_object* v_val_5265_; lean_object* v___x_5266_; 
v_val_5265_ = lean_ctor_get(v_a_5264_, 0);
lean_inc(v_val_5265_);
lean_dec_ref_known(v_a_5264_, 1);
v___x_5266_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg(v_inst_5251_, v_handler_5252_, v_val_5265_);
return v___x_5266_;
}
else
{
lean_object* v___x_5267_; 
lean_dec(v_a_5264_);
lean_dec(v_handler_5252_);
lean_dec_ref(v_inst_5251_);
v___x_5267_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_5267_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0___boxed(lean_object* v_inst_5268_, lean_object* v_handler_5269_, lean_object* v_x_5270_, lean_object* v___y_5271_){
_start:
{
lean_object* v_res_5272_; 
v_res_5272_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0(v_inst_5268_, v_handler_5269_, v_x_5270_);
return v_res_5272_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(lean_object* v_inst_5273_, lean_object* v_handler_5274_, lean_object* v_outbox_5275_){
_start:
{
lean_object* v___f_5277_; lean_object* v___x_5278_; uint8_t v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; 
v___f_5277_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_5277_, 0, v_inst_5273_);
lean_closure_set(v___f_5277_, 1, v_handler_5274_);
v___x_5278_ = lean_unsigned_to_nat(0u);
v___x_5279_ = 0;
v___x_5280_ = l_Std_Http_Internal_Outbox_takeError_x3f___redArg(v_outbox_5275_);
v___x_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5281_, 0, v___x_5280_);
v___x_5282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5282_, 0, v___x_5281_);
v___x_5283_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5278_, v___x_5279_, v___x_5282_, v___f_5277_);
return v___x_5283_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg___boxed(lean_object* v_inst_5284_, lean_object* v_handler_5285_, lean_object* v_outbox_5286_, lean_object* v_a_5287_){
_start:
{
lean_object* v_res_5288_; 
v_res_5288_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_inst_5284_, v_handler_5285_, v_outbox_5286_);
lean_dec_ref(v_outbox_5286_);
return v_res_5288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure(lean_object* v_00_u03c3_5289_, lean_object* v_00_u03b1_5290_, lean_object* v_inst_5291_, lean_object* v_handler_5292_, lean_object* v_outbox_5293_){
_start:
{
lean_object* v___x_5295_; 
v___x_5295_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_inst_5291_, v_handler_5292_, v_outbox_5293_);
return v___x_5295_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___boxed(lean_object* v_00_u03c3_5296_, lean_object* v_00_u03b1_5297_, lean_object* v_inst_5298_, lean_object* v_handler_5299_, lean_object* v_outbox_5300_, lean_object* v_a_5301_){
_start:
{
lean_object* v_res_5302_; 
v_res_5302_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure(v_00_u03c3_5296_, v_00_u03b1_5297_, v_inst_5298_, v_handler_5299_, v_outbox_5300_);
lean_dec_ref(v_outbox_5300_);
return v_res_5302_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(lean_object* v_state_5303_){
_start:
{
lean_object* v_machine_5304_; lean_object* v_reader_5305_; uint8_t v_peerClosed_5306_; 
v_machine_5304_ = lean_ctor_get(v_state_5303_, 0);
v_reader_5305_ = lean_ctor_get(v_machine_5304_, 0);
v_peerClosed_5306_ = lean_ctor_get_uint8(v_reader_5305_, sizeof(void*)*6);
if (v_peerClosed_5306_ == 0)
{
lean_object* v_timer_5307_; uint8_t v_requestEnded_5308_; lean_object* v_error_5309_; lean_object* v_state_5310_; lean_object* v_input_5311_; uint8_t v_inputStopped_5312_; uint8_t v___x_5313_; 
v_timer_5307_ = lean_ctor_get(v_state_5303_, 2);
v_requestEnded_5308_ = lean_ctor_get_uint8(v_state_5303_, sizeof(void*)*9);
v_error_5309_ = lean_ctor_get(v_machine_5304_, 4);
v_state_5310_ = lean_ctor_get(v_reader_5305_, 0);
v_input_5311_ = lean_ctor_get(v_reader_5305_, 1);
v_inputStopped_5312_ = lean_ctor_get_uint8(v_reader_5305_, sizeof(void*)*6 + 1);
v___x_5313_ = 1;
if (v_requestEnded_5308_ == 0)
{
return v___x_5313_;
}
else
{
if (v_inputStopped_5312_ == 0)
{
if (lean_obj_tag(v_error_5309_) == 0)
{
lean_object* v_array_5314_; lean_object* v_idx_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; uint8_t v___x_5319_; 
v_array_5314_ = lean_ctor_get(v_input_5311_, 0);
v_idx_5315_ = lean_ctor_get(v_input_5311_, 1);
v___x_5316_ = lean_unsigned_to_nat(0u);
v___x_5317_ = lean_byte_array_size(v_array_5314_);
v___x_5318_ = lean_nat_sub(v___x_5317_, v_idx_5315_);
v___x_5319_ = lean_nat_dec_lt(v___x_5316_, v___x_5318_);
lean_dec(v___x_5318_);
if (v___x_5319_ == 0)
{
if (lean_obj_tag(v_state_5310_) == 2)
{
return v___x_5313_;
}
else
{
if (lean_obj_tag(v_timer_5307_) == 2)
{
return v___x_5313_;
}
else
{
return v_peerClosed_5306_;
}
}
}
else
{
return v___x_5319_;
}
}
else
{
return v___x_5313_;
}
}
else
{
if (lean_obj_tag(v_timer_5307_) == 2)
{
return v___x_5313_;
}
else
{
return v_peerClosed_5306_;
}
}
}
}
else
{
uint8_t v___x_5320_; 
v___x_5320_ = 0;
return v___x_5320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg___boxed(lean_object* v_state_5321_){
_start:
{
uint8_t v_res_5322_; lean_object* v_r_5323_; 
v_res_5322_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(v_state_5321_);
lean_dec_ref(v_state_5321_);
v_r_5323_ = lean_box(v_res_5322_);
return v_r_5323_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend(lean_object* v_00_u03b2_5324_, lean_object* v_state_5325_){
_start:
{
uint8_t v___x_5326_; 
v___x_5326_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(v_state_5325_);
return v___x_5326_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___boxed(lean_object* v_00_u03b2_5327_, lean_object* v_state_5328_){
_start:
{
uint8_t v_res_5329_; lean_object* v_r_5330_; 
v_res_5329_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend(v_00_u03b2_5327_, v_state_5328_);
lean_dec_ref(v_state_5328_);
v_r_5330_ = lean_box(v_res_5329_);
return v_r_5330_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__0(lean_object* v_x_5331_){
_start:
{
if (lean_obj_tag(v_x_5331_) == 0)
{
lean_object* v___x_5333_; 
v___x_5333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5333_, 0, v_x_5331_);
return v___x_5333_;
}
else
{
lean_object* v___x_5334_; 
lean_dec_ref_known(v_x_5331_, 1);
v___x_5334_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_5334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__0___boxed(lean_object* v_x_5335_, lean_object* v___y_5336_){
_start:
{
lean_object* v_res_5337_; 
v_res_5337_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__0(v_x_5335_);
return v_res_5337_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__1(lean_object* v___x_5338_, lean_object* v_x_5339_){
_start:
{
if (lean_obj_tag(v_x_5339_) == 0)
{
lean_object* v_a_5341_; lean_object* v___x_5343_; uint8_t v_isShared_5344_; uint8_t v_isSharedCheck_5349_; 
v_a_5341_ = lean_ctor_get(v_x_5339_, 0);
v_isSharedCheck_5349_ = !lean_is_exclusive(v_x_5339_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5343_ = v_x_5339_;
v_isShared_5344_ = v_isSharedCheck_5349_;
goto v_resetjp_5342_;
}
else
{
lean_inc(v_a_5341_);
lean_dec(v_x_5339_);
v___x_5343_ = lean_box(0);
v_isShared_5344_ = v_isSharedCheck_5349_;
goto v_resetjp_5342_;
}
v_resetjp_5342_:
{
lean_object* v___x_5346_; 
if (v_isShared_5344_ == 0)
{
v___x_5346_ = v___x_5343_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_a_5341_);
v___x_5346_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
lean_object* v___x_5347_; 
v___x_5347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5347_, 0, v___x_5346_);
return v___x_5347_;
}
}
}
else
{
lean_object* v_a_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5365_; 
v_a_5350_ = lean_ctor_get(v_x_5339_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v_x_5339_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5352_ = v_x_5339_;
v_isShared_5353_ = v_isSharedCheck_5365_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_a_5350_);
lean_dec(v_x_5339_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5365_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
uint8_t v___x_5354_; 
v___x_5354_ = lean_unbox(v_a_5350_);
lean_dec(v_a_5350_);
if (v___x_5354_ == 0)
{
lean_object* v___x_5355_; lean_object* v___x_5357_; 
v___x_5355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5355_, 0, v___x_5338_);
if (v_isShared_5353_ == 0)
{
lean_ctor_set(v___x_5352_, 0, v___x_5355_);
v___x_5357_ = v___x_5352_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v___x_5355_);
v___x_5357_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
lean_object* v___x_5358_; 
v___x_5358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5358_, 0, v___x_5357_);
return v___x_5358_;
}
}
else
{
lean_object* v___x_5360_; lean_object* v___x_5362_; 
v___x_5360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5360_, 0, v___x_5338_);
if (v_isShared_5353_ == 0)
{
lean_ctor_set(v___x_5352_, 0, v___x_5360_);
v___x_5362_ = v___x_5352_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v___x_5360_);
v___x_5362_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
lean_object* v___x_5363_; 
v___x_5363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5363_, 0, v___x_5362_);
return v___x_5363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__1___boxed(lean_object* v___x_5366_, lean_object* v_x_5367_, lean_object* v___y_5368_){
_start:
{
lean_object* v_res_5369_; 
v_res_5369_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__1(v___x_5366_, v_x_5367_);
return v_res_5369_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2(uint8_t v___x_5370_, lean_object* v_x_5371_){
_start:
{
if (lean_obj_tag(v_x_5371_) == 0)
{
lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5381_; 
v_isSharedCheck_5381_ = !lean_is_exclusive(v_x_5371_);
if (v_isSharedCheck_5381_ == 0)
{
lean_object* v_unused_5382_; 
v_unused_5382_ = lean_ctor_get(v_x_5371_, 0);
lean_dec(v_unused_5382_);
v___x_5374_ = v_x_5371_;
v_isShared_5375_ = v_isSharedCheck_5381_;
goto v_resetjp_5373_;
}
else
{
lean_dec(v_x_5371_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5381_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
lean_object* v___x_5376_; lean_object* v___x_5378_; 
v___x_5376_ = lean_box(v___x_5370_);
if (v_isShared_5375_ == 0)
{
lean_ctor_set_tag(v___x_5374_, 1);
lean_ctor_set(v___x_5374_, 0, v___x_5376_);
v___x_5378_ = v___x_5374_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5376_);
v___x_5378_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
lean_object* v___x_5379_; 
v___x_5379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5379_, 0, v___x_5378_);
return v___x_5379_;
}
}
}
else
{
lean_object* v___x_5383_; 
v___x_5383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5383_, 0, v_x_5371_);
return v___x_5383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2___boxed(lean_object* v___x_5384_, lean_object* v_x_5385_, lean_object* v___y_5386_){
_start:
{
uint8_t v___x_2477__boxed_5387_; lean_object* v_res_5388_; 
v___x_2477__boxed_5387_ = lean_unbox(v___x_5384_);
v_res_5388_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2(v___x_2477__boxed_5387_, v_x_5385_);
return v_res_5388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3(uint8_t v___x_5389_, uint8_t v_a_5390_, lean_object* v_data_5391_){
_start:
{
uint8_t v___y_5394_; 
if (lean_obj_tag(v_data_5391_) == 0)
{
v___y_5394_ = v___x_5389_;
goto v___jp_5393_;
}
else
{
v___y_5394_ = v_a_5390_;
goto v___jp_5393_;
}
v___jp_5393_:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5395_ = lean_box(v___y_5394_);
v___x_5396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5396_, 0, v___x_5395_);
v___x_5397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5397_, 0, v___x_5396_);
return v___x_5397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3___boxed(lean_object* v___x_5398_, lean_object* v_a_5399_, lean_object* v_data_5400_, lean_object* v___y_5401_){
_start:
{
uint8_t v___x_2510__boxed_5402_; uint8_t v_a_2511__boxed_5403_; lean_object* v_res_5404_; 
v___x_2510__boxed_5402_ = lean_unbox(v___x_5398_);
v_a_2511__boxed_5403_ = lean_unbox(v_a_5399_);
v_res_5404_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3(v___x_2510__boxed_5402_, v_a_2511__boxed_5403_, v_data_5400_);
lean_dec(v_data_5400_);
return v_res_5404_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5(lean_object* v_connectionContext_5405_, lean_object* v_recvSelector_5406_, lean_object* v_socket_5407_, uint64_t v_readSize_5408_, lean_object* v___f_5409_, lean_object* v___f_5410_, lean_object* v_x_5411_){
_start:
{
if (lean_obj_tag(v_x_5411_) == 0)
{
lean_object* v_a_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5421_; 
lean_dec_ref(v___f_5410_);
lean_dec_ref(v___f_5409_);
lean_dec(v_socket_5407_);
lean_dec_ref(v_recvSelector_5406_);
lean_dec_ref(v_connectionContext_5405_);
v_a_5413_ = lean_ctor_get(v_x_5411_, 0);
v_isSharedCheck_5421_ = !lean_is_exclusive(v_x_5411_);
if (v_isSharedCheck_5421_ == 0)
{
v___x_5415_ = v_x_5411_;
v_isShared_5416_ = v_isSharedCheck_5421_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_a_5413_);
lean_dec(v_x_5411_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5421_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
lean_object* v___x_5418_; 
if (v_isShared_5416_ == 0)
{
v___x_5418_ = v___x_5415_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v_a_5413_);
v___x_5418_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
lean_object* v___x_5419_; 
v___x_5419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5419_, 0, v___x_5418_);
return v___x_5419_;
}
}
}
else
{
lean_object* v_a_5422_; lean_object* v_token_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; 
v_a_5422_ = lean_ctor_get(v_x_5411_, 0);
lean_inc(v_a_5422_);
lean_dec_ref_known(v_x_5411_, 1);
v_token_5423_ = lean_ctor_get(v_connectionContext_5405_, 1);
lean_inc_ref(v_token_5423_);
lean_dec_ref(v_connectionContext_5405_);
v___x_5424_ = lean_box_uint64(v_readSize_5408_);
v___x_5425_ = lean_apply_2(v_recvSelector_5406_, v_socket_5407_, v___x_5424_);
v___x_5426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5426_, 0, v___x_5425_);
lean_ctor_set(v___x_5426_, 1, v___f_5409_);
v___x_5427_ = l_Std_CancellationToken_selector(v_token_5423_);
lean_inc_ref(v___f_5410_);
v___x_5428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5428_, 0, v___x_5427_);
lean_ctor_set(v___x_5428_, 1, v___f_5410_);
v___x_5429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5429_, 0, v_a_5422_);
lean_ctor_set(v___x_5429_, 1, v___f_5410_);
v___x_5430_ = lean_unsigned_to_nat(3u);
v___x_5431_ = lean_mk_empty_array_with_capacity(v___x_5430_);
v___x_5432_ = lean_array_push(v___x_5431_, v___x_5426_);
v___x_5433_ = lean_array_push(v___x_5432_, v___x_5428_);
v___x_5434_ = lean_array_push(v___x_5433_, v___x_5429_);
v___x_5435_ = l_Std_Async_Selectable_one___redArg(v___x_5434_);
return v___x_5435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5___boxed(lean_object* v_connectionContext_5436_, lean_object* v_recvSelector_5437_, lean_object* v_socket_5438_, lean_object* v_readSize_5439_, lean_object* v___f_5440_, lean_object* v___f_5441_, lean_object* v_x_5442_, lean_object* v___y_5443_){
_start:
{
uint64_t v_readSize_boxed_5444_; lean_object* v_res_5445_; 
v_readSize_boxed_5444_ = lean_unbox_uint64(v_readSize_5439_);
lean_dec_ref(v_readSize_5439_);
v_res_5445_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5(v_connectionContext_5436_, v_recvSelector_5437_, v_socket_5438_, v_readSize_boxed_5444_, v___f_5440_, v___f_5441_, v_x_5442_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4(lean_object* v___x_5446_, uint8_t v_a_5447_, lean_object* v_connectionContext_5448_, lean_object* v_recvSelector_5449_, lean_object* v_socket_5450_, uint64_t v_readSize_5451_, lean_object* v___f_5452_, lean_object* v___x_5453_, lean_object* v_x_5454_){
_start:
{
if (lean_obj_tag(v_x_5454_) == 0)
{
lean_object* v_a_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5464_; 
lean_dec_ref(v___f_5452_);
lean_dec(v_socket_5450_);
lean_dec_ref(v_recvSelector_5449_);
lean_dec_ref(v_connectionContext_5448_);
v_a_5456_ = lean_ctor_get(v_x_5454_, 0);
v_isSharedCheck_5464_ = !lean_is_exclusive(v_x_5454_);
if (v_isSharedCheck_5464_ == 0)
{
v___x_5458_ = v_x_5454_;
v_isShared_5459_ = v_isSharedCheck_5464_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_a_5456_);
lean_dec(v_x_5454_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5464_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
lean_object* v___x_5461_; 
if (v_isShared_5459_ == 0)
{
v___x_5461_ = v___x_5458_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v_a_5456_);
v___x_5461_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
lean_object* v___x_5462_; 
v___x_5462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5462_, 0, v___x_5461_);
return v___x_5462_;
}
}
}
else
{
lean_object* v_a_5465_; lean_object* v___x_5467_; uint8_t v_isShared_5468_; uint8_t v_isSharedCheck_5491_; 
v_a_5465_ = lean_ctor_get(v_x_5454_, 0);
v_isSharedCheck_5491_ = !lean_is_exclusive(v_x_5454_);
if (v_isSharedCheck_5491_ == 0)
{
v___x_5467_ = v_x_5454_;
v_isShared_5468_ = v_isSharedCheck_5491_;
goto v_resetjp_5466_;
}
else
{
lean_inc(v_a_5465_);
lean_dec(v_x_5454_);
v___x_5467_ = lean_box(0);
v_isShared_5468_ = v_isSharedCheck_5491_;
goto v_resetjp_5466_;
}
v_resetjp_5466_:
{
uint8_t v___x_5469_; 
v___x_5469_ = lean_nat_dec_le(v___x_5446_, v_a_5465_);
if (v___x_5469_ == 0)
{
lean_object* v___x_5470_; lean_object* v___f_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___f_5474_; lean_object* v___x_5475_; lean_object* v___f_5476_; lean_object* v___x_5477_; lean_object* v___f_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; 
lean_del_object(v___x_5467_);
v___x_5470_ = lean_box(v___x_5469_);
v___f_5471_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_5471_, 0, v___x_5470_);
v___x_5472_ = lean_box(v___x_5469_);
v___x_5473_ = lean_box(v_a_5447_);
v___f_5474_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__3___boxed), 4, 2);
lean_closure_set(v___f_5474_, 0, v___x_5472_);
lean_closure_set(v___f_5474_, 1, v___x_5473_);
v___x_5475_ = lean_box(v___x_5469_);
v___f_5476_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleContinueEvent___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_5476_, 0, v___x_5475_);
v___x_5477_ = lean_box_uint64(v_readSize_5451_);
v___f_5478_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_5478_, 0, v_connectionContext_5448_);
lean_closure_set(v___f_5478_, 1, v_recvSelector_5449_);
lean_closure_set(v___f_5478_, 2, v_socket_5450_);
lean_closure_set(v___f_5478_, 3, v___x_5477_);
lean_closure_set(v___f_5478_, 4, v___f_5474_);
lean_closure_set(v___f_5478_, 5, v___f_5476_);
v___x_5479_ = lean_nat_sub(v___x_5446_, v_a_5465_);
lean_dec(v_a_5465_);
v___x_5480_ = lean_nat_to_int(v___x_5479_);
v___x_5481_ = lean_unsigned_to_nat(0u);
v___x_5482_ = l_Std_Async_Selector_sleep(v___x_5480_);
lean_dec(v___x_5480_);
v___x_5483_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5481_, v___x_5469_, v___x_5482_, v___f_5478_);
v___x_5484_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5481_, v___x_5469_, v___x_5483_, v___f_5471_);
v___x_5485_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5481_, v___x_5469_, v___x_5484_, v___f_5452_);
return v___x_5485_;
}
else
{
lean_object* v___x_5486_; lean_object* v___x_5488_; 
lean_dec(v_a_5465_);
lean_dec_ref(v___f_5452_);
lean_dec(v_socket_5450_);
lean_dec_ref(v_recvSelector_5449_);
lean_dec_ref(v_connectionContext_5448_);
v___x_5486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5486_, 0, v___x_5453_);
if (v_isShared_5468_ == 0)
{
lean_ctor_set(v___x_5467_, 0, v___x_5486_);
v___x_5488_ = v___x_5467_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v___x_5486_);
v___x_5488_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
lean_object* v___x_5489_; 
v___x_5489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5489_, 0, v___x_5488_);
return v___x_5489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4___boxed(lean_object* v___x_5492_, lean_object* v_a_5493_, lean_object* v_connectionContext_5494_, lean_object* v_recvSelector_5495_, lean_object* v_socket_5496_, lean_object* v_readSize_5497_, lean_object* v___f_5498_, lean_object* v___x_5499_, lean_object* v_x_5500_, lean_object* v___y_5501_){
_start:
{
uint8_t v_a_2587__boxed_5502_; uint64_t v_readSize_boxed_5503_; lean_object* v_res_5504_; 
v_a_2587__boxed_5502_ = lean_unbox(v_a_5493_);
v_readSize_boxed_5503_ = lean_unbox_uint64(v_readSize_5497_);
lean_dec_ref(v_readSize_5497_);
v_res_5504_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4(v___x_5492_, v_a_2587__boxed_5502_, v_connectionContext_5494_, v_recvSelector_5495_, v_socket_5496_, v_readSize_boxed_5503_, v___f_5498_, v___x_5499_, v_x_5500_);
lean_dec(v___x_5492_);
return v_res_5504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6(lean_object* v___f_5505_, lean_object* v_x_5506_, lean_object* v_____s_5507_){
_start:
{
lean_object* v___x_5509_; uint8_t v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; 
v___x_5509_ = lean_unsigned_to_nat(0u);
v___x_5510_ = 0;
v___x_5511_ = lean_io_mono_ms_now();
v___x_5512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5512_, 0, v___x_5511_);
v___x_5513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5513_, 0, v___x_5512_);
v___x_5514_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5509_, v___x_5510_, v___x_5513_, v___f_5505_);
return v___x_5514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6___boxed(lean_object* v___f_5515_, lean_object* v_x_5516_, lean_object* v_____s_5517_, lean_object* v___y_5518_){
_start:
{
lean_object* v_res_5519_; 
v_res_5519_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6(v___f_5515_, v_x_5516_, v_____s_5517_);
return v_res_5519_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7(lean_object* v_a_5520_, lean_object* v_x_5521_){
_start:
{
if (lean_obj_tag(v_x_5521_) == 0)
{
lean_object* v___x_5523_; 
v___x_5523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5523_, 0, v_x_5521_);
return v___x_5523_;
}
else
{
lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5531_; 
v_isSharedCheck_5531_ = !lean_is_exclusive(v_x_5521_);
if (v_isSharedCheck_5531_ == 0)
{
lean_object* v_unused_5532_; 
v_unused_5532_ = lean_ctor_get(v_x_5521_, 0);
lean_dec(v_unused_5532_);
v___x_5525_ = v_x_5521_;
v_isShared_5526_ = v_isSharedCheck_5531_;
goto v_resetjp_5524_;
}
else
{
lean_dec(v_x_5521_);
v___x_5525_ = lean_box(0);
v_isShared_5526_ = v_isSharedCheck_5531_;
goto v_resetjp_5524_;
}
v_resetjp_5524_:
{
lean_object* v___x_5527_; lean_object* v___x_5529_; 
v___x_5527_ = l_IO_Promise_result_x21___redArg(v_a_5520_);
if (v_isShared_5526_ == 0)
{
lean_ctor_set(v___x_5525_, 0, v___x_5527_);
v___x_5529_ = v___x_5525_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5527_);
v___x_5529_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
return v___x_5529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7___boxed(lean_object* v_a_5533_, lean_object* v_x_5534_, lean_object* v___y_5535_){
_start:
{
lean_object* v_res_5536_; 
v_res_5536_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7(v_a_5533_, v_x_5534_);
lean_dec(v_a_5533_);
return v_res_5536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8(lean_object* v___f_5537_, lean_object* v___x_5538_, lean_object* v___x_5539_, uint8_t v___x_5540_, lean_object* v_x_5541_){
_start:
{
if (lean_obj_tag(v_x_5541_) == 0)
{
lean_object* v_a_5543_; lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5551_; 
lean_dec(v___x_5538_);
lean_dec_ref(v___f_5537_);
v_a_5543_ = lean_ctor_get(v_x_5541_, 0);
v_isSharedCheck_5551_ = !lean_is_exclusive(v_x_5541_);
if (v_isSharedCheck_5551_ == 0)
{
v___x_5545_ = v_x_5541_;
v_isShared_5546_ = v_isSharedCheck_5551_;
goto v_resetjp_5544_;
}
else
{
lean_inc(v_a_5543_);
lean_dec(v_x_5541_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5551_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
lean_object* v___x_5548_; 
if (v_isShared_5546_ == 0)
{
v___x_5548_ = v___x_5545_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5543_);
v___x_5548_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
lean_object* v___x_5549_; 
v___x_5549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5549_, 0, v___x_5548_);
return v___x_5549_;
}
}
}
else
{
lean_object* v_a_5552_; lean_object* v___x_5554_; uint8_t v_isShared_5555_; uint8_t v_isSharedCheck_5563_; 
v_a_5552_ = lean_ctor_get(v_x_5541_, 0);
v_isSharedCheck_5563_ = !lean_is_exclusive(v_x_5541_);
if (v_isSharedCheck_5563_ == 0)
{
v___x_5554_ = v_x_5541_;
v_isShared_5555_ = v_isSharedCheck_5563_;
goto v_resetjp_5553_;
}
else
{
lean_inc(v_a_5552_);
lean_dec(v_x_5541_);
v___x_5554_ = lean_box(0);
v_isShared_5555_ = v_isSharedCheck_5563_;
goto v_resetjp_5553_;
}
v_resetjp_5553_:
{
lean_object* v___f_5556_; lean_object* v___x_5557_; lean_object* v___x_5559_; 
lean_inc(v_a_5552_);
v___f_5556_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__7___boxed), 3, 1);
lean_closure_set(v___f_5556_, 0, v_a_5552_);
lean_inc(v___x_5538_);
v___x_5557_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_5537_, v___x_5538_, v_a_5552_, v___x_5539_);
if (v_isShared_5555_ == 0)
{
lean_ctor_set(v___x_5554_, 0, v___x_5557_);
v___x_5559_ = v___x_5554_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5562_; 
v_reuseFailAlloc_5562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5562_, 0, v___x_5557_);
v___x_5559_ = v_reuseFailAlloc_5562_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
lean_object* v___x_5560_; lean_object* v___x_5561_; 
v___x_5560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5560_, 0, v___x_5559_);
v___x_5561_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5538_, v___x_5540_, v___x_5560_, v___f_5556_);
return v___x_5561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8___boxed(lean_object* v___f_5564_, lean_object* v___x_5565_, lean_object* v___x_5566_, lean_object* v___x_5567_, lean_object* v_x_5568_, lean_object* v___y_5569_){
_start:
{
uint8_t v___x_2734__boxed_5570_; lean_object* v_res_5571_; 
v___x_2734__boxed_5570_ = lean_unbox(v___x_5567_);
v_res_5571_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8(v___f_5564_, v___x_5565_, v___x_5566_, v___x_2734__boxed_5570_, v_x_5568_);
return v_res_5571_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9(lean_object* v_timeout_5574_, uint8_t v_a_5575_, lean_object* v_connectionContext_5576_, lean_object* v_recvSelector_5577_, lean_object* v_socket_5578_, uint64_t v_readSize_5579_, lean_object* v___f_5580_, lean_object* v_x_5581_){
_start:
{
if (lean_obj_tag(v_x_5581_) == 0)
{
lean_object* v_a_5583_; lean_object* v___x_5585_; uint8_t v_isShared_5586_; uint8_t v_isSharedCheck_5591_; 
lean_dec_ref(v___f_5580_);
lean_dec(v_socket_5578_);
lean_dec_ref(v_recvSelector_5577_);
lean_dec_ref(v_connectionContext_5576_);
v_a_5583_ = lean_ctor_get(v_x_5581_, 0);
v_isSharedCheck_5591_ = !lean_is_exclusive(v_x_5581_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5585_ = v_x_5581_;
v_isShared_5586_ = v_isSharedCheck_5591_;
goto v_resetjp_5584_;
}
else
{
lean_inc(v_a_5583_);
lean_dec(v_x_5581_);
v___x_5585_ = lean_box(0);
v_isShared_5586_ = v_isSharedCheck_5591_;
goto v_resetjp_5584_;
}
v_resetjp_5584_:
{
lean_object* v___x_5588_; 
if (v_isShared_5586_ == 0)
{
v___x_5588_ = v___x_5585_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_a_5583_);
v___x_5588_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
lean_object* v___x_5589_; 
v___x_5589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5589_, 0, v___x_5588_);
return v___x_5589_;
}
}
}
else
{
lean_object* v_a_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5615_; 
v_a_5592_ = lean_ctor_get(v_x_5581_, 0);
v_isSharedCheck_5615_ = !lean_is_exclusive(v_x_5581_);
if (v_isSharedCheck_5615_ == 0)
{
v___x_5594_ = v_x_5581_;
v_isShared_5595_ = v_isSharedCheck_5615_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_a_5592_);
lean_dec(v_x_5581_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5615_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___f_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___f_5602_; lean_object* v___f_5603_; lean_object* v___x_5604_; uint8_t v___x_5605_; lean_object* v___x_5606_; lean_object* v___f_5607_; lean_object* v___x_5608_; lean_object* v___x_5610_; 
v___x_5596_ = l_Int_toNat(v_timeout_5574_);
v___x_5597_ = lean_nat_add(v_a_5592_, v___x_5596_);
lean_dec(v___x_5596_);
lean_dec(v_a_5592_);
v___x_5598_ = lean_box(0);
v___f_5599_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___closed__0));
v___x_5600_ = lean_box(v_a_5575_);
v___x_5601_ = lean_box_uint64(v_readSize_5579_);
v___f_5602_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__4___boxed), 10, 8);
lean_closure_set(v___f_5602_, 0, v___x_5597_);
lean_closure_set(v___f_5602_, 1, v___x_5600_);
lean_closure_set(v___f_5602_, 2, v_connectionContext_5576_);
lean_closure_set(v___f_5602_, 3, v_recvSelector_5577_);
lean_closure_set(v___f_5602_, 4, v_socket_5578_);
lean_closure_set(v___f_5602_, 5, v___x_5601_);
lean_closure_set(v___f_5602_, 6, v___f_5599_);
lean_closure_set(v___f_5602_, 7, v___x_5598_);
v___f_5603_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__6___boxed), 4, 1);
lean_closure_set(v___f_5603_, 0, v___f_5602_);
v___x_5604_ = lean_unsigned_to_nat(0u);
v___x_5605_ = 0;
v___x_5606_ = lean_box(v___x_5605_);
v___f_5607_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__8___boxed), 6, 4);
lean_closure_set(v___f_5607_, 0, v___f_5603_);
lean_closure_set(v___f_5607_, 1, v___x_5604_);
lean_closure_set(v___f_5607_, 2, v___x_5598_);
lean_closure_set(v___f_5607_, 3, v___x_5606_);
v___x_5608_ = lean_io_promise_new();
if (v_isShared_5595_ == 0)
{
lean_ctor_set(v___x_5594_, 0, v___x_5608_);
v___x_5610_ = v___x_5594_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v___x_5608_);
v___x_5610_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5609_;
}
v_reusejp_5609_:
{
lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; 
v___x_5611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5611_, 0, v___x_5610_);
v___x_5612_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5604_, v___x_5605_, v___x_5611_, v___f_5607_);
v___x_5613_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5604_, v___x_5605_, v___x_5612_, v___f_5580_);
return v___x_5613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___boxed(lean_object* v_timeout_5616_, lean_object* v_a_5617_, lean_object* v_connectionContext_5618_, lean_object* v_recvSelector_5619_, lean_object* v_socket_5620_, lean_object* v_readSize_5621_, lean_object* v___f_5622_, lean_object* v_x_5623_, lean_object* v___y_5624_){
_start:
{
uint8_t v_a_2795__boxed_5625_; uint64_t v_readSize_boxed_5626_; lean_object* v_res_5627_; 
v_a_2795__boxed_5625_ = lean_unbox(v_a_5617_);
v_readSize_boxed_5626_ = lean_unbox_uint64(v_readSize_5621_);
lean_dec_ref(v_readSize_5621_);
v_res_5627_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9(v_timeout_5616_, v_a_2795__boxed_5625_, v_connectionContext_5618_, v_recvSelector_5619_, v_socket_5620_, v_readSize_boxed_5626_, v___f_5622_, v_x_5623_);
lean_dec(v_timeout_5616_);
return v_res_5627_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10(lean_object* v_timeout_5628_, lean_object* v_connectionContext_5629_, lean_object* v_recvSelector_5630_, lean_object* v_socket_5631_, uint64_t v_readSize_5632_, lean_object* v___f_5633_, lean_object* v_x_5634_){
_start:
{
if (lean_obj_tag(v_x_5634_) == 0)
{
lean_object* v_a_5636_; lean_object* v___x_5638_; uint8_t v_isShared_5639_; uint8_t v_isSharedCheck_5644_; 
lean_dec_ref(v___f_5633_);
lean_dec(v_socket_5631_);
lean_dec_ref(v_recvSelector_5630_);
lean_dec_ref(v_connectionContext_5629_);
lean_dec(v_timeout_5628_);
v_a_5636_ = lean_ctor_get(v_x_5634_, 0);
v_isSharedCheck_5644_ = !lean_is_exclusive(v_x_5634_);
if (v_isSharedCheck_5644_ == 0)
{
v___x_5638_ = v_x_5634_;
v_isShared_5639_ = v_isSharedCheck_5644_;
goto v_resetjp_5637_;
}
else
{
lean_inc(v_a_5636_);
lean_dec(v_x_5634_);
v___x_5638_ = lean_box(0);
v_isShared_5639_ = v_isSharedCheck_5644_;
goto v_resetjp_5637_;
}
v_resetjp_5637_:
{
lean_object* v___x_5641_; 
if (v_isShared_5639_ == 0)
{
v___x_5641_ = v___x_5638_;
goto v_reusejp_5640_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_a_5636_);
v___x_5641_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5640_;
}
v_reusejp_5640_:
{
lean_object* v___x_5642_; 
v___x_5642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5642_, 0, v___x_5641_);
return v___x_5642_;
}
}
}
else
{
lean_object* v_a_5645_; lean_object* v___x_5647_; uint8_t v_isShared_5648_; uint8_t v_isSharedCheck_5661_; 
v_a_5645_ = lean_ctor_get(v_x_5634_, 0);
v_isSharedCheck_5661_ = !lean_is_exclusive(v_x_5634_);
if (v_isSharedCheck_5661_ == 0)
{
v___x_5647_ = v_x_5634_;
v_isShared_5648_ = v_isSharedCheck_5661_;
goto v_resetjp_5646_;
}
else
{
lean_inc(v_a_5645_);
lean_dec(v_x_5634_);
v___x_5647_ = lean_box(0);
v_isShared_5648_ = v_isSharedCheck_5661_;
goto v_resetjp_5646_;
}
v_resetjp_5646_:
{
uint8_t v___x_5649_; 
v___x_5649_ = lean_unbox(v_a_5645_);
if (v___x_5649_ == 0)
{
lean_object* v___x_5650_; 
lean_del_object(v___x_5647_);
lean_dec(v_a_5645_);
lean_dec_ref(v___f_5633_);
lean_dec(v_socket_5631_);
lean_dec_ref(v_recvSelector_5630_);
lean_dec_ref(v_connectionContext_5629_);
lean_dec(v_timeout_5628_);
v___x_5650_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_5650_;
}
else
{
lean_object* v___x_5651_; lean_object* v___f_5652_; lean_object* v___x_5653_; uint8_t v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5657_; 
v___x_5651_ = lean_box_uint64(v_readSize_5632_);
v___f_5652_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__9___boxed), 9, 7);
lean_closure_set(v___f_5652_, 0, v_timeout_5628_);
lean_closure_set(v___f_5652_, 1, v_a_5645_);
lean_closure_set(v___f_5652_, 2, v_connectionContext_5629_);
lean_closure_set(v___f_5652_, 3, v_recvSelector_5630_);
lean_closure_set(v___f_5652_, 4, v_socket_5631_);
lean_closure_set(v___f_5652_, 5, v___x_5651_);
lean_closure_set(v___f_5652_, 6, v___f_5633_);
v___x_5653_ = lean_unsigned_to_nat(0u);
v___x_5654_ = 0;
v___x_5655_ = lean_io_mono_ms_now();
if (v_isShared_5648_ == 0)
{
lean_ctor_set(v___x_5647_, 0, v___x_5655_);
v___x_5657_ = v___x_5647_;
goto v_reusejp_5656_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v___x_5655_);
v___x_5657_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5656_;
}
v_reusejp_5656_:
{
lean_object* v___x_5658_; lean_object* v___x_5659_; 
v___x_5658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5658_, 0, v___x_5657_);
v___x_5659_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5653_, v___x_5654_, v___x_5658_, v___f_5652_);
return v___x_5659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10___boxed(lean_object* v_timeout_5662_, lean_object* v_connectionContext_5663_, lean_object* v_recvSelector_5664_, lean_object* v_socket_5665_, lean_object* v_readSize_5666_, lean_object* v___f_5667_, lean_object* v_x_5668_, lean_object* v___y_5669_){
_start:
{
uint64_t v_readSize_boxed_5670_; lean_object* v_res_5671_; 
v_readSize_boxed_5670_ = lean_unbox_uint64(v_readSize_5666_);
lean_dec_ref(v_readSize_5666_);
v_res_5671_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10(v_timeout_5662_, v_connectionContext_5663_, v_recvSelector_5664_, v_socket_5665_, v_readSize_boxed_5670_, v___f_5667_, v_x_5668_);
return v_res_5671_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11(lean_object* v_x_5677_){
_start:
{
if (lean_obj_tag(v_x_5677_) == 0)
{
lean_object* v___x_5679_; 
lean_dec_ref_known(v_x_5677_, 1);
v___x_5679_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___closed__1));
return v___x_5679_;
}
else
{
lean_object* v___x_5680_; 
v___x_5680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5680_, 0, v_x_5677_);
return v___x_5680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11___boxed(lean_object* v_x_5681_, lean_object* v___y_5682_){
_start:
{
lean_object* v_res_5683_; 
v_res_5683_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__11(v_x_5681_);
return v_res_5683_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(lean_object* v_inst_5686_, lean_object* v_socket_5687_, lean_object* v_timeout_5688_, uint64_t v_readSize_5689_, lean_object* v_connectionContext_5690_){
_start:
{
lean_object* v_recvSelector_5692_; lean_object* v_shutdown_5693_; lean_object* v___f_5694_; lean_object* v___x_5695_; lean_object* v___f_5696_; lean_object* v___f_5697_; lean_object* v___x_5698_; uint8_t v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; 
v_recvSelector_5692_ = lean_ctor_get(v_inst_5686_, 2);
lean_inc_ref(v_recvSelector_5692_);
v_shutdown_5693_ = lean_ctor_get(v_inst_5686_, 4);
lean_inc_ref(v_shutdown_5693_);
lean_dec_ref(v_inst_5686_);
v___f_5694_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___closed__0));
v___x_5695_ = lean_box_uint64(v_readSize_5689_);
lean_inc(v_socket_5687_);
v___f_5696_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___lam__10___boxed), 8, 6);
lean_closure_set(v___f_5696_, 0, v_timeout_5688_);
lean_closure_set(v___f_5696_, 1, v_connectionContext_5690_);
lean_closure_set(v___f_5696_, 2, v_recvSelector_5692_);
lean_closure_set(v___f_5696_, 3, v_socket_5687_);
lean_closure_set(v___f_5696_, 4, v___x_5695_);
lean_closure_set(v___f_5696_, 5, v___f_5694_);
v___f_5697_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___closed__1));
v___x_5698_ = lean_unsigned_to_nat(0u);
v___x_5699_ = 0;
v___x_5700_ = lean_apply_2(v_shutdown_5693_, v_socket_5687_, lean_box(0));
v___x_5701_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5698_, v___x_5699_, v___x_5700_, v___f_5697_);
v___x_5702_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5698_, v___x_5699_, v___x_5701_, v___f_5696_);
return v___x_5702_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg___boxed(lean_object* v_inst_5703_, lean_object* v_socket_5704_, lean_object* v_timeout_5705_, lean_object* v_readSize_5706_, lean_object* v_connectionContext_5707_, lean_object* v_a_5708_){
_start:
{
uint64_t v_readSize_boxed_5709_; lean_object* v_res_5710_; 
v_readSize_boxed_5709_ = lean_unbox_uint64(v_readSize_5706_);
lean_dec_ref(v_readSize_5706_);
v_res_5710_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(v_inst_5703_, v_socket_5704_, v_timeout_5705_, v_readSize_boxed_5709_, v_connectionContext_5707_);
return v_res_5710_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger(lean_object* v_00_u03b1_5711_, lean_object* v_inst_5712_, lean_object* v_socket_5713_, lean_object* v_timeout_5714_, uint64_t v_readSize_5715_, lean_object* v_connectionContext_5716_){
_start:
{
lean_object* v___x_5718_; 
v___x_5718_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(v_inst_5712_, v_socket_5713_, v_timeout_5714_, v_readSize_5715_, v_connectionContext_5716_);
return v___x_5718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___boxed(lean_object* v_00_u03b1_5719_, lean_object* v_inst_5720_, lean_object* v_socket_5721_, lean_object* v_timeout_5722_, lean_object* v_readSize_5723_, lean_object* v_connectionContext_5724_, lean_object* v_a_5725_){
_start:
{
uint64_t v_readSize_boxed_5726_; lean_object* v_res_5727_; 
v_readSize_boxed_5726_ = lean_unbox_uint64(v_readSize_5723_);
lean_dec_ref(v_readSize_5723_);
v_res_5727_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger(v_00_u03b1_5719_, v_inst_5720_, v_socket_5721_, v_timeout_5722_, v_readSize_boxed_5726_, v_connectionContext_5724_);
return v_res_5727_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_armTimer___redArg(lean_object* v_config_5728_, lean_object* v_wd_5729_, lean_object* v_outbox_5730_, lean_object* v_x_5731_){
_start:
{
switch(lean_obj_tag(v_x_5731_))
{
case 0:
{
lean_object* v___x_5733_; 
v___x_5733_ = l_Std_Http_Internal_Outbox_idle_x3f___redArg(v_outbox_5730_);
if (lean_obj_tag(v___x_5733_) == 1)
{
lean_object* v_val_5734_; lean_object* v_keepAliveTimeout_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; 
v_val_5734_ = lean_ctor_get(v___x_5733_, 0);
lean_inc(v_val_5734_);
lean_dec_ref_known(v___x_5733_, 1);
v_keepAliveTimeout_5735_ = lean_ctor_get(v_config_5728_, 5);
lean_inc(v_keepAliveTimeout_5735_);
lean_dec_ref(v_config_5728_);
v___x_5736_ = l_Std_Async_Watchdog_armAfter___redArg(v_wd_5729_, v_val_5734_, v_keepAliveTimeout_5735_);
v___x_5737_ = l_Std_Http_Internal_Outbox_writeDeadline_x3f___redArg(v_outbox_5730_);
return v___x_5737_;
}
else
{
lean_object* v_keepAliveTimeout_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; 
lean_dec(v___x_5733_);
v_keepAliveTimeout_5738_ = lean_ctor_get(v_config_5728_, 5);
lean_inc(v_keepAliveTimeout_5738_);
lean_dec_ref(v_config_5728_);
v___x_5739_ = l_Std_Async_Watchdog_arm(v_wd_5729_, v_keepAliveTimeout_5738_);
lean_dec(v_keepAliveTimeout_5738_);
lean_dec_ref(v_wd_5729_);
v___x_5740_ = lean_box(0);
return v___x_5740_;
}
}
case 1:
{
lean_object* v_deadline_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; 
lean_dec_ref(v_config_5728_);
v_deadline_5741_ = lean_ctor_get(v_x_5731_, 0);
lean_inc(v_deadline_5741_);
lean_dec_ref_known(v_x_5731_, 1);
v___x_5742_ = l_Std_Async_Watchdog_armUntil(v_wd_5729_, v_deadline_5741_);
lean_dec_ref(v_wd_5729_);
v___x_5743_ = lean_box(0);
return v___x_5743_;
}
default: 
{
lean_object* v_timeout_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; 
lean_dec_ref(v_config_5728_);
v_timeout_5744_ = lean_ctor_get(v_x_5731_, 0);
lean_inc(v_timeout_5744_);
lean_dec_ref_known(v_x_5731_, 1);
v___x_5745_ = l_Std_Async_Watchdog_arm(v_wd_5729_, v_timeout_5744_);
lean_dec(v_timeout_5744_);
lean_dec_ref(v_wd_5729_);
v___x_5746_ = lean_box(0);
return v___x_5746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_armTimer___redArg___boxed(lean_object* v_config_5747_, lean_object* v_wd_5748_, lean_object* v_outbox_5749_, lean_object* v_x_5750_, lean_object* v_a_5751_){
_start:
{
lean_object* v_res_5752_; 
v_res_5752_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_armTimer___redArg(v_config_5747_, v_wd_5748_, v_outbox_5749_, v_x_5750_);
lean_dec_ref(v_outbox_5749_);
return v_res_5752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_armTimer(lean_object* v_00_u03b1_5753_, lean_object* v_config_5754_, lean_object* v_wd_5755_, lean_object* v_outbox_5756_, lean_object* v_x_5757_){
_start:
{
lean_object* v___x_5759_; 
v___x_5759_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_armTimer___redArg(v_config_5754_, v_wd_5755_, v_outbox_5756_, v_x_5757_);
return v___x_5759_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_armTimer___boxed(lean_object* v_00_u03b1_5760_, lean_object* v_config_5761_, lean_object* v_wd_5762_, lean_object* v_outbox_5763_, lean_object* v_x_5764_, lean_object* v_a_5765_){
_start:
{
lean_object* v_res_5766_; 
v_res_5766_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_armTimer(v_00_u03b1_5760_, v_config_5761_, v_wd_5762_, v_outbox_5763_, v_x_5764_);
lean_dec_ref(v_outbox_5763_);
return v_res_5766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg___lam__0(lean_object* v_close_5767_, lean_object* v_body_5768_, lean_object* v_x_5769_){
_start:
{
if (lean_obj_tag(v_x_5769_) == 0)
{
lean_object* v_a_5771_; lean_object* v___x_5773_; uint8_t v_isShared_5774_; uint8_t v_isSharedCheck_5779_; 
lean_dec(v_body_5768_);
lean_dec_ref(v_close_5767_);
v_a_5771_ = lean_ctor_get(v_x_5769_, 0);
v_isSharedCheck_5779_ = !lean_is_exclusive(v_x_5769_);
if (v_isSharedCheck_5779_ == 0)
{
v___x_5773_ = v_x_5769_;
v_isShared_5774_ = v_isSharedCheck_5779_;
goto v_resetjp_5772_;
}
else
{
lean_inc(v_a_5771_);
lean_dec(v_x_5769_);
v___x_5773_ = lean_box(0);
v_isShared_5774_ = v_isSharedCheck_5779_;
goto v_resetjp_5772_;
}
v_resetjp_5772_:
{
lean_object* v___x_5776_; 
if (v_isShared_5774_ == 0)
{
v___x_5776_ = v___x_5773_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v_a_5771_);
v___x_5776_ = v_reuseFailAlloc_5778_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
lean_object* v___x_5777_; 
v___x_5777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5777_, 0, v___x_5776_);
return v___x_5777_;
}
}
}
else
{
lean_object* v_a_5780_; uint8_t v___x_5781_; 
v_a_5780_ = lean_ctor_get(v_x_5769_, 0);
lean_inc(v_a_5780_);
lean_dec_ref_known(v_x_5769_, 1);
v___x_5781_ = lean_unbox(v_a_5780_);
lean_dec(v_a_5780_);
if (v___x_5781_ == 0)
{
lean_object* v___x_5782_; 
v___x_5782_ = lean_apply_2(v_close_5767_, v_body_5768_, lean_box(0));
return v___x_5782_;
}
else
{
lean_object* v___x_5783_; 
lean_dec(v_body_5768_);
lean_dec_ref(v_close_5767_);
v___x_5783_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_5783_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg___lam__0___boxed(lean_object* v_close_5784_, lean_object* v_body_5785_, lean_object* v_x_5786_, lean_object* v___y_5787_){
_start:
{
lean_object* v_res_5788_; 
v_res_5788_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg___lam__0(v_close_5784_, v_body_5785_, v_x_5786_);
return v_res_5788_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg(lean_object* v_inst_5789_, lean_object* v_x_5790_){
_start:
{
if (lean_obj_tag(v_x_5790_) == 3)
{
lean_object* v_x_5794_; 
v_x_5794_ = lean_ctor_get(v_x_5790_, 0);
lean_inc_ref(v_x_5794_);
lean_dec_ref_known(v_x_5790_, 1);
if (lean_obj_tag(v_x_5794_) == 1)
{
lean_object* v_a_5795_; lean_object* v_close_5796_; lean_object* v_isClosed_5797_; lean_object* v_body_5798_; lean_object* v___f_5799_; lean_object* v___x_5800_; uint8_t v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; 
v_a_5795_ = lean_ctor_get(v_x_5794_, 0);
lean_inc(v_a_5795_);
lean_dec_ref_known(v_x_5794_, 1);
v_close_5796_ = lean_ctor_get(v_inst_5789_, 1);
lean_inc_ref(v_close_5796_);
v_isClosed_5797_ = lean_ctor_get(v_inst_5789_, 2);
lean_inc_ref(v_isClosed_5797_);
lean_dec_ref(v_inst_5789_);
v_body_5798_ = lean_ctor_get(v_a_5795_, 1);
lean_inc_n(v_body_5798_, 2);
lean_dec(v_a_5795_);
v___f_5799_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_5799_, 0, v_close_5796_);
lean_closure_set(v___f_5799_, 1, v_body_5798_);
v___x_5800_ = lean_unsigned_to_nat(0u);
v___x_5801_ = 0;
v___x_5802_ = lean_apply_2(v_isClosed_5797_, v_body_5798_, lean_box(0));
v___x_5803_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5800_, v___x_5801_, v___x_5802_, v___f_5799_);
return v___x_5803_;
}
else
{
lean_dec_ref(v_x_5794_);
lean_dec_ref(v_inst_5789_);
goto v___jp_5792_;
}
}
else
{
lean_dec(v_x_5790_);
lean_dec_ref(v_inst_5789_);
goto v___jp_5792_;
}
v___jp_5792_:
{
lean_object* v___x_5793_; 
v___x_5793_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_5793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg___boxed(lean_object* v_inst_5804_, lean_object* v_x_5805_, lean_object* v_a_5806_){
_start:
{
lean_object* v_res_5807_; 
v_res_5807_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg(v_inst_5804_, v_x_5805_);
return v_res_5807_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent(lean_object* v_00_u03b2_5808_, lean_object* v_inst_5809_, lean_object* v_x_5810_){
_start:
{
lean_object* v___x_5812_; 
v___x_5812_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg(v_inst_5809_, v_x_5810_);
return v___x_5812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___boxed(lean_object* v_00_u03b2_5813_, lean_object* v_inst_5814_, lean_object* v_x_5815_, lean_object* v_a_5816_){
_start:
{
lean_object* v_res_5817_; 
v_res_5817_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent(v_00_u03b2_5813_, v_inst_5814_, v_x_5815_);
return v_res_5817_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__0(lean_object* v_x_5818_){
_start:
{
if (lean_obj_tag(v_x_5818_) == 0)
{
lean_object* v_a_5820_; lean_object* v___x_5822_; uint8_t v_isShared_5823_; uint8_t v_isSharedCheck_5828_; 
v_a_5820_ = lean_ctor_get(v_x_5818_, 0);
v_isSharedCheck_5828_ = !lean_is_exclusive(v_x_5818_);
if (v_isSharedCheck_5828_ == 0)
{
v___x_5822_ = v_x_5818_;
v_isShared_5823_ = v_isSharedCheck_5828_;
goto v_resetjp_5821_;
}
else
{
lean_inc(v_a_5820_);
lean_dec(v_x_5818_);
v___x_5822_ = lean_box(0);
v_isShared_5823_ = v_isSharedCheck_5828_;
goto v_resetjp_5821_;
}
v_resetjp_5821_:
{
lean_object* v___x_5825_; 
if (v_isShared_5823_ == 0)
{
v___x_5825_ = v___x_5822_;
goto v_reusejp_5824_;
}
else
{
lean_object* v_reuseFailAlloc_5827_; 
v_reuseFailAlloc_5827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5827_, 0, v_a_5820_);
v___x_5825_ = v_reuseFailAlloc_5827_;
goto v_reusejp_5824_;
}
v_reusejp_5824_:
{
lean_object* v___x_5826_; 
v___x_5826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5826_, 0, v___x_5825_);
return v___x_5826_;
}
}
}
else
{
lean_object* v_a_5829_; lean_object* v___x_5831_; uint8_t v_isShared_5832_; uint8_t v_isSharedCheck_5847_; 
v_a_5829_ = lean_ctor_get(v_x_5818_, 0);
v_isSharedCheck_5847_ = !lean_is_exclusive(v_x_5818_);
if (v_isSharedCheck_5847_ == 0)
{
v___x_5831_ = v_x_5818_;
v_isShared_5832_ = v_isSharedCheck_5847_;
goto v_resetjp_5830_;
}
else
{
lean_inc(v_a_5829_);
lean_dec(v_x_5818_);
v___x_5831_ = lean_box(0);
v_isShared_5832_ = v_isSharedCheck_5847_;
goto v_resetjp_5830_;
}
v_resetjp_5830_:
{
lean_object* v_snd_5833_; uint8_t v___x_5834_; 
v_snd_5833_ = lean_ctor_get(v_a_5829_, 1);
v___x_5834_ = lean_unbox(v_snd_5833_);
if (v___x_5834_ == 0)
{
lean_object* v_fst_5835_; lean_object* v___x_5836_; lean_object* v___x_5838_; 
v_fst_5835_ = lean_ctor_get(v_a_5829_, 0);
lean_inc(v_fst_5835_);
lean_dec(v_a_5829_);
v___x_5836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5836_, 0, v_fst_5835_);
if (v_isShared_5832_ == 0)
{
lean_ctor_set(v___x_5831_, 0, v___x_5836_);
v___x_5838_ = v___x_5831_;
goto v_reusejp_5837_;
}
else
{
lean_object* v_reuseFailAlloc_5840_; 
v_reuseFailAlloc_5840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5840_, 0, v___x_5836_);
v___x_5838_ = v_reuseFailAlloc_5840_;
goto v_reusejp_5837_;
}
v_reusejp_5837_:
{
lean_object* v___x_5839_; 
v___x_5839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5839_, 0, v___x_5838_);
return v___x_5839_;
}
}
else
{
lean_object* v_fst_5841_; lean_object* v___x_5842_; lean_object* v___x_5844_; 
v_fst_5841_ = lean_ctor_get(v_a_5829_, 0);
lean_inc(v_fst_5841_);
lean_dec(v_a_5829_);
v___x_5842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5842_, 0, v_fst_5841_);
if (v_isShared_5832_ == 0)
{
lean_ctor_set(v___x_5831_, 0, v___x_5842_);
v___x_5844_ = v___x_5831_;
goto v_reusejp_5843_;
}
else
{
lean_object* v_reuseFailAlloc_5846_; 
v_reuseFailAlloc_5846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5846_, 0, v___x_5842_);
v___x_5844_ = v_reuseFailAlloc_5846_;
goto v_reusejp_5843_;
}
v_reusejp_5843_:
{
lean_object* v___x_5845_; 
v___x_5845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5845_, 0, v___x_5844_);
return v___x_5845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__0___boxed(lean_object* v_x_5848_, lean_object* v___y_5849_){
_start:
{
lean_object* v_res_5850_; 
v_res_5850_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__0(v_x_5848_);
return v_res_5850_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__1(lean_object* v_x_5851_){
_start:
{
lean_object* v_fst_5852_; 
v_fst_5852_ = lean_ctor_get(v_x_5851_, 0);
lean_inc(v_fst_5852_);
return v_fst_5852_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__1___boxed(lean_object* v_x_5853_){
_start:
{
lean_object* v_res_5854_; 
v_res_5854_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__1(v_x_5853_);
lean_dec_ref(v_x_5853_);
return v_res_5854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__2(lean_object* v_responseBodyInstance_5855_, lean_object* v_____do__lift_5856_){
_start:
{
if (lean_obj_tag(v_____do__lift_5856_) == 1)
{
lean_object* v_a_5858_; lean_object* v_close_5859_; lean_object* v_body_5860_; lean_object* v___x_5861_; 
v_a_5858_ = lean_ctor_get(v_____do__lift_5856_, 0);
lean_inc(v_a_5858_);
lean_dec_ref_known(v_____do__lift_5856_, 1);
v_close_5859_ = lean_ctor_get(v_responseBodyInstance_5855_, 1);
lean_inc_ref(v_close_5859_);
lean_dec_ref(v_responseBodyInstance_5855_);
v_body_5860_ = lean_ctor_get(v_a_5858_, 1);
lean_inc(v_body_5860_);
lean_dec(v_a_5858_);
v___x_5861_ = lean_apply_2(v_close_5859_, v_body_5860_, lean_box(0));
return v___x_5861_;
}
else
{
lean_object* v___x_5862_; 
lean_dec_ref(v_____do__lift_5856_);
lean_dec_ref(v_responseBodyInstance_5855_);
v___x_5862_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_5862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__2___boxed(lean_object* v_responseBodyInstance_5863_, lean_object* v_____do__lift_5864_, lean_object* v___y_5865_){
_start:
{
lean_object* v_res_5866_; 
v_res_5866_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__2(v_responseBodyInstance_5863_, v_____do__lift_5864_);
return v_res_5866_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__3(lean_object* v___x_5867_, lean_object* v_x_5868_){
_start:
{
if (lean_obj_tag(v_x_5868_) == 0)
{
lean_object* v_a_5870_; lean_object* v___x_5872_; uint8_t v_isShared_5873_; uint8_t v_isSharedCheck_5878_; 
lean_dec_ref(v___x_5867_);
v_a_5870_ = lean_ctor_get(v_x_5868_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v_x_5868_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5872_ = v_x_5868_;
v_isShared_5873_ = v_isSharedCheck_5878_;
goto v_resetjp_5871_;
}
else
{
lean_inc(v_a_5870_);
lean_dec(v_x_5868_);
v___x_5872_ = lean_box(0);
v_isShared_5873_ = v_isSharedCheck_5878_;
goto v_resetjp_5871_;
}
v_resetjp_5871_:
{
lean_object* v___x_5875_; 
if (v_isShared_5873_ == 0)
{
v___x_5875_ = v___x_5872_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5870_);
v___x_5875_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
lean_object* v___x_5876_; 
v___x_5876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5876_, 0, v___x_5875_);
return v___x_5876_;
}
}
}
else
{
lean_object* v___x_5880_; uint8_t v_isShared_5881_; uint8_t v_isSharedCheck_5887_; 
v_isSharedCheck_5887_ = !lean_is_exclusive(v_x_5868_);
if (v_isSharedCheck_5887_ == 0)
{
lean_object* v_unused_5888_; 
v_unused_5888_ = lean_ctor_get(v_x_5868_, 0);
lean_dec(v_unused_5888_);
v___x_5880_ = v_x_5868_;
v_isShared_5881_ = v_isSharedCheck_5887_;
goto v_resetjp_5879_;
}
else
{
lean_dec(v_x_5868_);
v___x_5880_ = lean_box(0);
v_isShared_5881_ = v_isSharedCheck_5887_;
goto v_resetjp_5879_;
}
v_resetjp_5879_:
{
lean_object* v___x_5882_; lean_object* v___x_5884_; 
v___x_5882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5882_, 0, v___x_5867_);
if (v_isShared_5881_ == 0)
{
lean_ctor_set(v___x_5880_, 0, v___x_5882_);
v___x_5884_ = v___x_5880_;
goto v_reusejp_5883_;
}
else
{
lean_object* v_reuseFailAlloc_5886_; 
v_reuseFailAlloc_5886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5886_, 0, v___x_5882_);
v___x_5884_ = v_reuseFailAlloc_5886_;
goto v_reusejp_5883_;
}
v_reusejp_5883_:
{
lean_object* v___x_5885_; 
v___x_5885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5885_, 0, v___x_5884_);
return v___x_5885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__3___boxed(lean_object* v___x_5889_, lean_object* v_x_5890_, lean_object* v___y_5891_){
_start:
{
lean_object* v_res_5892_; 
v_res_5892_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__3(v___x_5889_, v_x_5890_);
return v_res_5892_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__5(lean_object* v_h_5893_, lean_object* v_responseBodyInstance_5894_, lean_object* v_handler_5895_, lean_object* v_config_5896_, lean_object* v_a_5897_, lean_object* v___x_5898_, uint8_t v___x_5899_, lean_object* v___f_5900_, lean_object* v_____r_5901_, lean_object* v_event_5902_){
_start:
{
lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; 
v___x_5904_ = lean_unsigned_to_nat(0u);
v___x_5905_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handleRecvEvent___redArg(v_h_5893_, v_responseBodyInstance_5894_, v_handler_5895_, v_config_5896_, v_a_5897_, v_event_5902_, v___x_5898_);
v___x_5906_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5904_, v___x_5899_, v___x_5905_, v___f_5900_);
return v___x_5906_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__5___boxed(lean_object* v_h_5907_, lean_object* v_responseBodyInstance_5908_, lean_object* v_handler_5909_, lean_object* v_config_5910_, lean_object* v_a_5911_, lean_object* v___x_5912_, lean_object* v___x_5913_, lean_object* v___f_5914_, lean_object* v_____r_5915_, lean_object* v_event_5916_, lean_object* v___y_5917_){
_start:
{
uint8_t v___x_9029__boxed_5918_; lean_object* v_res_5919_; 
v___x_9029__boxed_5918_ = lean_unbox(v___x_5913_);
v_res_5919_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__5(v_h_5907_, v_responseBodyInstance_5908_, v_handler_5909_, v_config_5910_, v_a_5911_, v___x_5912_, v___x_9029__boxed_5918_, v___f_5914_, v_____r_5915_, v_event_5916_);
return v_res_5919_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__4(lean_object* v___f_5920_, lean_object* v_x_5921_){
_start:
{
if (lean_obj_tag(v_x_5921_) == 0)
{
lean_object* v_a_5923_; lean_object* v___x_5925_; uint8_t v_isShared_5926_; uint8_t v_isSharedCheck_5931_; 
lean_dec_ref(v___f_5920_);
v_a_5923_ = lean_ctor_get(v_x_5921_, 0);
v_isSharedCheck_5931_ = !lean_is_exclusive(v_x_5921_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5925_ = v_x_5921_;
v_isShared_5926_ = v_isSharedCheck_5931_;
goto v_resetjp_5924_;
}
else
{
lean_inc(v_a_5923_);
lean_dec(v_x_5921_);
v___x_5925_ = lean_box(0);
v_isShared_5926_ = v_isSharedCheck_5931_;
goto v_resetjp_5924_;
}
v_resetjp_5924_:
{
lean_object* v___x_5928_; 
if (v_isShared_5926_ == 0)
{
v___x_5928_ = v___x_5925_;
goto v_reusejp_5927_;
}
else
{
lean_object* v_reuseFailAlloc_5930_; 
v_reuseFailAlloc_5930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5930_, 0, v_a_5923_);
v___x_5928_ = v_reuseFailAlloc_5930_;
goto v_reusejp_5927_;
}
v_reusejp_5927_:
{
lean_object* v___x_5929_; 
v___x_5929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5929_, 0, v___x_5928_);
return v___x_5929_;
}
}
}
else
{
lean_object* v_a_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; 
v_a_5932_ = lean_ctor_get(v_x_5921_, 0);
lean_inc(v_a_5932_);
lean_dec_ref_known(v_x_5921_, 1);
v___x_5933_ = lean_box(0);
v___x_5934_ = lean_apply_3(v___f_5920_, v___x_5933_, v_a_5932_, lean_box(0));
return v___x_5934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__4___boxed(lean_object* v___f_5935_, lean_object* v_x_5936_, lean_object* v___y_5937_){
_start:
{
lean_object* v_res_5938_; 
v_res_5938_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__4(v___f_5935_, v_x_5936_);
return v_res_5938_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__6(lean_object* v_sources_5939_, lean_object* v_wd_5940_, lean_object* v_connectionContext_5941_, uint8_t v___x_5942_, lean_object* v___f_5943_, lean_object* v_x_5944_){
_start:
{
if (lean_obj_tag(v_x_5944_) == 0)
{
lean_object* v_a_5946_; lean_object* v___x_5948_; uint8_t v_isShared_5949_; uint8_t v_isSharedCheck_5954_; 
lean_dec_ref(v___f_5943_);
lean_dec_ref(v_connectionContext_5941_);
lean_dec_ref(v_wd_5940_);
v_a_5946_ = lean_ctor_get(v_x_5944_, 0);
v_isSharedCheck_5954_ = !lean_is_exclusive(v_x_5944_);
if (v_isSharedCheck_5954_ == 0)
{
v___x_5948_ = v_x_5944_;
v_isShared_5949_ = v_isSharedCheck_5954_;
goto v_resetjp_5947_;
}
else
{
lean_inc(v_a_5946_);
lean_dec(v_x_5944_);
v___x_5948_ = lean_box(0);
v_isShared_5949_ = v_isSharedCheck_5954_;
goto v_resetjp_5947_;
}
v_resetjp_5947_:
{
lean_object* v___x_5951_; 
if (v_isShared_5949_ == 0)
{
v___x_5951_ = v___x_5948_;
goto v_reusejp_5950_;
}
else
{
lean_object* v_reuseFailAlloc_5953_; 
v_reuseFailAlloc_5953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5953_, 0, v_a_5946_);
v___x_5951_ = v_reuseFailAlloc_5953_;
goto v_reusejp_5950_;
}
v_reusejp_5950_:
{
lean_object* v___x_5952_; 
v___x_5952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5952_, 0, v___x_5951_);
return v___x_5952_;
}
}
}
else
{
lean_object* v___x_5956_; uint8_t v_isShared_5957_; uint8_t v_isSharedCheck_5966_; 
v_isSharedCheck_5966_ = !lean_is_exclusive(v_x_5944_);
if (v_isSharedCheck_5966_ == 0)
{
lean_object* v_unused_5967_; 
v_unused_5967_ = lean_ctor_get(v_x_5944_, 0);
lean_dec(v_unused_5967_);
v___x_5956_ = v_x_5944_;
v_isShared_5957_ = v_isSharedCheck_5966_;
goto v_resetjp_5955_;
}
else
{
lean_dec(v_x_5944_);
v___x_5956_ = lean_box(0);
v_isShared_5957_ = v_isSharedCheck_5966_;
goto v_resetjp_5955_;
}
v_resetjp_5955_:
{
uint8_t v_idle_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5962_; 
v_idle_5958_ = lean_ctor_get_uint8(v_sources_5939_, sizeof(void*)*8);
v___x_5959_ = lean_unsigned_to_nat(0u);
v___x_5960_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_cancelledEvent___redArg(v_wd_5940_, v_connectionContext_5941_, v_idle_5958_);
if (v_isShared_5957_ == 0)
{
lean_ctor_set(v___x_5956_, 0, v___x_5960_);
v___x_5962_ = v___x_5956_;
goto v_reusejp_5961_;
}
else
{
lean_object* v_reuseFailAlloc_5965_; 
v_reuseFailAlloc_5965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5965_, 0, v___x_5960_);
v___x_5962_ = v_reuseFailAlloc_5965_;
goto v_reusejp_5961_;
}
v_reusejp_5961_:
{
lean_object* v___x_5963_; lean_object* v___x_5964_; 
v___x_5963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5963_, 0, v___x_5962_);
v___x_5964_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5959_, v___x_5942_, v___x_5963_, v___f_5943_);
return v___x_5964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__6___boxed(lean_object* v_sources_5968_, lean_object* v_wd_5969_, lean_object* v_connectionContext_5970_, lean_object* v___x_5971_, lean_object* v___f_5972_, lean_object* v_x_5973_, lean_object* v___y_5974_){
_start:
{
uint8_t v___x_9084__boxed_5975_; lean_object* v_res_5976_; 
v___x_9084__boxed_5975_ = lean_unbox(v___x_5971_);
v_res_5976_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__6(v_sources_5968_, v_wd_5969_, v_connectionContext_5970_, v___x_9084__boxed_5975_, v___f_5972_, v_x_5973_);
lean_dec_ref(v_sources_5968_);
return v_res_5976_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__7(lean_object* v___f_5977_, lean_object* v_a_5978_, lean_object* v_responseBodyInstance_5979_, uint8_t v___x_5980_, lean_object* v___f_5981_, lean_object* v_x_5982_){
_start:
{
if (lean_obj_tag(v_x_5982_) == 0)
{
lean_object* v_a_5984_; lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_5992_; 
lean_dec_ref(v___f_5981_);
lean_dec_ref(v_responseBodyInstance_5979_);
lean_dec(v_a_5978_);
lean_dec_ref(v___f_5977_);
v_a_5984_ = lean_ctor_get(v_x_5982_, 0);
v_isSharedCheck_5992_ = !lean_is_exclusive(v_x_5982_);
if (v_isSharedCheck_5992_ == 0)
{
v___x_5986_ = v_x_5982_;
v_isShared_5987_ = v_isSharedCheck_5992_;
goto v_resetjp_5985_;
}
else
{
lean_inc(v_a_5984_);
lean_dec(v_x_5982_);
v___x_5986_ = lean_box(0);
v_isShared_5987_ = v_isSharedCheck_5992_;
goto v_resetjp_5985_;
}
v_resetjp_5985_:
{
lean_object* v___x_5989_; 
if (v_isShared_5987_ == 0)
{
v___x_5989_ = v___x_5986_;
goto v_reusejp_5988_;
}
else
{
lean_object* v_reuseFailAlloc_5991_; 
v_reuseFailAlloc_5991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5991_, 0, v_a_5984_);
v___x_5989_ = v_reuseFailAlloc_5991_;
goto v_reusejp_5988_;
}
v_reusejp_5988_:
{
lean_object* v___x_5990_; 
v___x_5990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5990_, 0, v___x_5989_);
return v___x_5990_;
}
}
}
else
{
lean_object* v_a_5993_; uint8_t v___x_5994_; 
v_a_5993_ = lean_ctor_get(v_x_5982_, 0);
lean_inc(v_a_5993_);
lean_dec_ref_known(v_x_5982_, 1);
v___x_5994_ = lean_unbox(v_a_5993_);
lean_dec(v_a_5993_);
if (v___x_5994_ == 0)
{
lean_object* v___x_5995_; lean_object* v___x_5996_; 
lean_dec_ref(v___f_5981_);
lean_dec_ref(v_responseBodyInstance_5979_);
v___x_5995_ = lean_box(0);
v___x_5996_ = lean_apply_3(v___f_5977_, v___x_5995_, v_a_5978_, lean_box(0));
return v___x_5996_;
}
else
{
lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; 
lean_dec_ref(v___f_5977_);
v___x_5997_ = lean_unsigned_to_nat(0u);
v___x_5998_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_discardEvent___redArg(v_responseBodyInstance_5979_, v_a_5978_);
v___x_5999_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5997_, v___x_5980_, v___x_5998_, v___f_5981_);
return v___x_5999_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__7___boxed(lean_object* v___f_6000_, lean_object* v_a_6001_, lean_object* v_responseBodyInstance_6002_, lean_object* v___x_6003_, lean_object* v___f_6004_, lean_object* v_x_6005_, lean_object* v___y_6006_){
_start:
{
uint8_t v___x_9140__boxed_6007_; lean_object* v_res_6008_; 
v___x_9140__boxed_6007_ = lean_unbox(v___x_6003_);
v_res_6008_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__7(v___f_6000_, v_a_6001_, v_responseBodyInstance_6002_, v___x_9140__boxed_6007_, v___f_6004_, v_x_6005_);
return v_res_6008_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__8(lean_object* v___f_6009_, lean_object* v_responseBodyInstance_6010_, uint8_t v___x_6011_, lean_object* v___f_6012_, lean_object* v_wd_6013_, lean_object* v_x_6014_){
_start:
{
if (lean_obj_tag(v_x_6014_) == 0)
{
lean_object* v_a_6016_; lean_object* v___x_6018_; uint8_t v_isShared_6019_; uint8_t v_isSharedCheck_6024_; 
lean_dec_ref(v_wd_6013_);
lean_dec_ref(v___f_6012_);
lean_dec_ref(v_responseBodyInstance_6010_);
lean_dec_ref(v___f_6009_);
v_a_6016_ = lean_ctor_get(v_x_6014_, 0);
v_isSharedCheck_6024_ = !lean_is_exclusive(v_x_6014_);
if (v_isSharedCheck_6024_ == 0)
{
v___x_6018_ = v_x_6014_;
v_isShared_6019_ = v_isSharedCheck_6024_;
goto v_resetjp_6017_;
}
else
{
lean_inc(v_a_6016_);
lean_dec(v_x_6014_);
v___x_6018_ = lean_box(0);
v_isShared_6019_ = v_isSharedCheck_6024_;
goto v_resetjp_6017_;
}
v_resetjp_6017_:
{
lean_object* v___x_6021_; 
if (v_isShared_6019_ == 0)
{
v___x_6021_ = v___x_6018_;
goto v_reusejp_6020_;
}
else
{
lean_object* v_reuseFailAlloc_6023_; 
v_reuseFailAlloc_6023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_a_6016_);
v___x_6021_ = v_reuseFailAlloc_6023_;
goto v_reusejp_6020_;
}
v_reusejp_6020_:
{
lean_object* v___x_6022_; 
v___x_6022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6021_);
return v___x_6022_;
}
}
}
else
{
lean_object* v_a_6025_; lean_object* v___x_6027_; uint8_t v_isShared_6028_; uint8_t v_isSharedCheck_6039_; 
v_a_6025_ = lean_ctor_get(v_x_6014_, 0);
v_isSharedCheck_6039_ = !lean_is_exclusive(v_x_6014_);
if (v_isSharedCheck_6039_ == 0)
{
v___x_6027_ = v_x_6014_;
v_isShared_6028_ = v_isSharedCheck_6039_;
goto v_resetjp_6026_;
}
else
{
lean_inc(v_a_6025_);
lean_dec(v_x_6014_);
v___x_6027_ = lean_box(0);
v_isShared_6028_ = v_isSharedCheck_6039_;
goto v_resetjp_6026_;
}
v_resetjp_6026_:
{
lean_object* v___x_6029_; lean_object* v___f_6030_; lean_object* v___x_6031_; uint8_t v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6035_; 
v___x_6029_ = lean_box(v___x_6011_);
v___f_6030_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__7___boxed), 7, 5);
lean_closure_set(v___f_6030_, 0, v___f_6009_);
lean_closure_set(v___f_6030_, 1, v_a_6025_);
lean_closure_set(v___f_6030_, 2, v_responseBodyInstance_6010_);
lean_closure_set(v___f_6030_, 3, v___x_6029_);
lean_closure_set(v___f_6030_, 4, v___f_6012_);
v___x_6031_ = lean_unsigned_to_nat(0u);
v___x_6032_ = l_Std_Async_Watchdog_disarm(v_wd_6013_);
v___x_6033_ = lean_box(v___x_6032_);
if (v_isShared_6028_ == 0)
{
lean_ctor_set(v___x_6027_, 0, v___x_6033_);
v___x_6035_ = v___x_6027_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6038_; 
v_reuseFailAlloc_6038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6038_, 0, v___x_6033_);
v___x_6035_ = v_reuseFailAlloc_6038_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; 
v___x_6036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6035_);
v___x_6037_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6031_, v___x_6011_, v___x_6036_, v___f_6030_);
return v___x_6037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__8___boxed(lean_object* v___f_6040_, lean_object* v_responseBodyInstance_6041_, lean_object* v___x_6042_, lean_object* v___f_6043_, lean_object* v_wd_6044_, lean_object* v_x_6045_, lean_object* v___y_6046_){
_start:
{
uint8_t v___x_9189__boxed_6047_; lean_object* v_res_6048_; 
v___x_9189__boxed_6047_ = lean_unbox(v___x_6042_);
v_res_6048_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__8(v___f_6040_, v_responseBodyInstance_6041_, v___x_9189__boxed_6047_, v___f_6043_, v_wd_6044_, v_x_6045_);
return v_res_6048_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__9(lean_object* v_wd_6049_, lean_object* v_connectionContext_6050_, uint8_t v___x_6051_, lean_object* v___f_6052_, lean_object* v___f_6053_, lean_object* v_responseBodyInstance_6054_, lean_object* v_inst_6055_, lean_object* v_h_6056_, lean_object* v_config_6057_, lean_object* v_handler_6058_, lean_object* v_____r_6059_, lean_object* v_sources_6060_){
_start:
{
lean_object* v___x_6062_; lean_object* v___f_6063_; lean_object* v___x_6064_; lean_object* v___f_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; 
v___x_6062_ = lean_box(v___x_6051_);
lean_inc_ref_n(v_wd_6049_, 2);
lean_inc_ref(v_sources_6060_);
v___f_6063_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__6___boxed), 7, 5);
lean_closure_set(v___f_6063_, 0, v_sources_6060_);
lean_closure_set(v___f_6063_, 1, v_wd_6049_);
lean_closure_set(v___f_6063_, 2, v_connectionContext_6050_);
lean_closure_set(v___f_6063_, 3, v___x_6062_);
lean_closure_set(v___f_6063_, 4, v___f_6052_);
v___x_6064_ = lean_box(v___x_6051_);
lean_inc_ref(v_responseBodyInstance_6054_);
v___f_6065_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__8___boxed), 7, 5);
lean_closure_set(v___f_6065_, 0, v___f_6053_);
lean_closure_set(v___f_6065_, 1, v_responseBodyInstance_6054_);
lean_closure_set(v___f_6065_, 2, v___x_6064_);
lean_closure_set(v___f_6065_, 3, v___f_6063_);
lean_closure_set(v___f_6065_, 4, v_wd_6049_);
v___x_6066_ = lean_unsigned_to_nat(0u);
v___x_6067_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_pollNextEvent___redArg(v_inst_6055_, v_h_6056_, v_responseBodyInstance_6054_, v_config_6057_, v_handler_6058_, v_wd_6049_, v_sources_6060_);
v___x_6068_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6066_, v___x_6051_, v___x_6067_, v___f_6065_);
return v___x_6068_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__9___boxed(lean_object* v_wd_6069_, lean_object* v_connectionContext_6070_, lean_object* v___x_6071_, lean_object* v___f_6072_, lean_object* v___f_6073_, lean_object* v_responseBodyInstance_6074_, lean_object* v_inst_6075_, lean_object* v_h_6076_, lean_object* v_config_6077_, lean_object* v_handler_6078_, lean_object* v_____r_6079_, lean_object* v_sources_6080_, lean_object* v___y_6081_){
_start:
{
uint8_t v___x_9251__boxed_6082_; lean_object* v_res_6083_; 
v___x_9251__boxed_6082_ = lean_unbox(v___x_6071_);
v_res_6083_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__9(v_wd_6069_, v_connectionContext_6070_, v___x_9251__boxed_6082_, v___f_6072_, v___f_6073_, v_responseBodyInstance_6074_, v_inst_6075_, v_h_6076_, v_config_6077_, v_handler_6078_, v_____r_6079_, v_sources_6080_);
return v_res_6083_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__10(lean_object* v_socket_6084_, lean_object* v_timer_6085_, lean_object* v_expect_6086_, lean_object* v_response_6087_, lean_object* v_responseBody_6088_, lean_object* v_requestBody_6089_, lean_object* v_connectionContext_6090_, uint8_t v_idle_6091_, lean_object* v___f_6092_, lean_object* v_x_6093_){
_start:
{
if (lean_obj_tag(v_x_6093_) == 0)
{
lean_object* v_a_6095_; lean_object* v___x_6097_; uint8_t v_isShared_6098_; uint8_t v_isSharedCheck_6103_; 
lean_dec_ref(v___f_6092_);
lean_dec_ref(v_connectionContext_6090_);
lean_dec(v_requestBody_6089_);
lean_dec(v_responseBody_6088_);
lean_dec(v_response_6087_);
lean_dec(v_expect_6086_);
lean_dec(v_timer_6085_);
lean_dec(v_socket_6084_);
v_a_6095_ = lean_ctor_get(v_x_6093_, 0);
v_isSharedCheck_6103_ = !lean_is_exclusive(v_x_6093_);
if (v_isSharedCheck_6103_ == 0)
{
v___x_6097_ = v_x_6093_;
v_isShared_6098_ = v_isSharedCheck_6103_;
goto v_resetjp_6096_;
}
else
{
lean_inc(v_a_6095_);
lean_dec(v_x_6093_);
v___x_6097_ = lean_box(0);
v_isShared_6098_ = v_isSharedCheck_6103_;
goto v_resetjp_6096_;
}
v_resetjp_6096_:
{
lean_object* v___x_6100_; 
if (v_isShared_6098_ == 0)
{
v___x_6100_ = v___x_6097_;
goto v_reusejp_6099_;
}
else
{
lean_object* v_reuseFailAlloc_6102_; 
v_reuseFailAlloc_6102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6102_, 0, v_a_6095_);
v___x_6100_ = v_reuseFailAlloc_6102_;
goto v_reusejp_6099_;
}
v_reusejp_6099_:
{
lean_object* v___x_6101_; 
v___x_6101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6100_);
return v___x_6101_;
}
}
}
else
{
lean_object* v_a_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; 
v_a_6104_ = lean_ctor_get(v_x_6093_, 0);
lean_inc(v_a_6104_);
lean_dec_ref_known(v_x_6093_, 1);
v___x_6105_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_6105_, 0, v_socket_6084_);
lean_ctor_set(v___x_6105_, 1, v_timer_6085_);
lean_ctor_set(v___x_6105_, 2, v_a_6104_);
lean_ctor_set(v___x_6105_, 3, v_expect_6086_);
lean_ctor_set(v___x_6105_, 4, v_response_6087_);
lean_ctor_set(v___x_6105_, 5, v_responseBody_6088_);
lean_ctor_set(v___x_6105_, 6, v_requestBody_6089_);
lean_ctor_set(v___x_6105_, 7, v_connectionContext_6090_);
lean_ctor_set_uint8(v___x_6105_, sizeof(void*)*8, v_idle_6091_);
v___x_6106_ = lean_box(0);
v___x_6107_ = lean_apply_3(v___f_6092_, v___x_6106_, v___x_6105_, lean_box(0));
return v___x_6107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__10___boxed(lean_object* v_socket_6108_, lean_object* v_timer_6109_, lean_object* v_expect_6110_, lean_object* v_response_6111_, lean_object* v_responseBody_6112_, lean_object* v_requestBody_6113_, lean_object* v_connectionContext_6114_, lean_object* v_idle_6115_, lean_object* v___f_6116_, lean_object* v_x_6117_, lean_object* v___y_6118_){
_start:
{
uint8_t v_idle_boxed_6119_; lean_object* v_res_6120_; 
v_idle_boxed_6119_ = lean_unbox(v_idle_6115_);
v_res_6120_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__10(v_socket_6108_, v_timer_6109_, v_expect_6110_, v_response_6111_, v_responseBody_6112_, v_requestBody_6113_, v_connectionContext_6114_, v_idle_boxed_6119_, v___f_6116_, v_x_6117_);
return v_res_6120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__11(lean_object* v___f_6121_, lean_object* v_config_6122_, lean_object* v_wd_6123_, lean_object* v_a_6124_, uint8_t v___x_6125_, lean_object* v_x_6126_){
_start:
{
if (lean_obj_tag(v_x_6126_) == 0)
{
lean_object* v_a_6128_; lean_object* v___x_6130_; uint8_t v_isShared_6131_; uint8_t v_isSharedCheck_6136_; 
lean_dec_ref(v_wd_6123_);
lean_dec_ref(v_config_6122_);
lean_dec_ref(v___f_6121_);
v_a_6128_ = lean_ctor_get(v_x_6126_, 0);
v_isSharedCheck_6136_ = !lean_is_exclusive(v_x_6126_);
if (v_isSharedCheck_6136_ == 0)
{
v___x_6130_ = v_x_6126_;
v_isShared_6131_ = v_isSharedCheck_6136_;
goto v_resetjp_6129_;
}
else
{
lean_inc(v_a_6128_);
lean_dec(v_x_6126_);
v___x_6130_ = lean_box(0);
v_isShared_6131_ = v_isSharedCheck_6136_;
goto v_resetjp_6129_;
}
v_resetjp_6129_:
{
lean_object* v___x_6133_; 
if (v_isShared_6131_ == 0)
{
v___x_6133_ = v___x_6130_;
goto v_reusejp_6132_;
}
else
{
lean_object* v_reuseFailAlloc_6135_; 
v_reuseFailAlloc_6135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6135_, 0, v_a_6128_);
v___x_6133_ = v_reuseFailAlloc_6135_;
goto v_reusejp_6132_;
}
v_reusejp_6132_:
{
lean_object* v___x_6134_; 
v___x_6134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6134_, 0, v___x_6133_);
return v___x_6134_;
}
}
}
else
{
lean_object* v_a_6137_; lean_object* v___x_6139_; uint8_t v_isShared_6140_; uint8_t v_isSharedCheck_6161_; 
v_a_6137_ = lean_ctor_get(v_x_6126_, 0);
v_isSharedCheck_6161_ = !lean_is_exclusive(v_x_6126_);
if (v_isSharedCheck_6161_ == 0)
{
v___x_6139_ = v_x_6126_;
v_isShared_6140_ = v_isSharedCheck_6161_;
goto v_resetjp_6138_;
}
else
{
lean_inc(v_a_6137_);
lean_dec(v_x_6126_);
v___x_6139_ = lean_box(0);
v_isShared_6140_ = v_isSharedCheck_6161_;
goto v_resetjp_6138_;
}
v_resetjp_6138_:
{
lean_object* v_timer_6141_; 
v_timer_6141_ = lean_ctor_get(v_a_6137_, 1);
if (lean_obj_tag(v_timer_6141_) == 1)
{
lean_object* v_socket_6142_; lean_object* v_expect_6143_; lean_object* v_response_6144_; lean_object* v_responseBody_6145_; lean_object* v_requestBody_6146_; lean_object* v_connectionContext_6147_; uint8_t v_idle_6148_; lean_object* v_val_6149_; lean_object* v___x_6150_; lean_object* v___f_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6155_; 
lean_inc_ref(v_timer_6141_);
v_socket_6142_ = lean_ctor_get(v_a_6137_, 0);
lean_inc(v_socket_6142_);
v_expect_6143_ = lean_ctor_get(v_a_6137_, 3);
lean_inc(v_expect_6143_);
v_response_6144_ = lean_ctor_get(v_a_6137_, 4);
lean_inc(v_response_6144_);
v_responseBody_6145_ = lean_ctor_get(v_a_6137_, 5);
lean_inc(v_responseBody_6145_);
v_requestBody_6146_ = lean_ctor_get(v_a_6137_, 6);
lean_inc(v_requestBody_6146_);
v_connectionContext_6147_ = lean_ctor_get(v_a_6137_, 7);
lean_inc_ref(v_connectionContext_6147_);
v_idle_6148_ = lean_ctor_get_uint8(v_a_6137_, sizeof(void*)*8);
lean_dec(v_a_6137_);
v_val_6149_ = lean_ctor_get(v_timer_6141_, 0);
lean_inc(v_val_6149_);
v___x_6150_ = lean_box(v_idle_6148_);
v___f_6151_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__10___boxed), 11, 9);
lean_closure_set(v___f_6151_, 0, v_socket_6142_);
lean_closure_set(v___f_6151_, 1, v_timer_6141_);
lean_closure_set(v___f_6151_, 2, v_expect_6143_);
lean_closure_set(v___f_6151_, 3, v_response_6144_);
lean_closure_set(v___f_6151_, 4, v_responseBody_6145_);
lean_closure_set(v___f_6151_, 5, v_requestBody_6146_);
lean_closure_set(v___f_6151_, 6, v_connectionContext_6147_);
lean_closure_set(v___f_6151_, 7, v___x_6150_);
lean_closure_set(v___f_6151_, 8, v___f_6121_);
v___x_6152_ = lean_unsigned_to_nat(0u);
v___x_6153_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_armTimer___redArg(v_config_6122_, v_wd_6123_, v_a_6124_, v_val_6149_);
if (v_isShared_6140_ == 0)
{
lean_ctor_set(v___x_6139_, 0, v___x_6153_);
v___x_6155_ = v___x_6139_;
goto v_reusejp_6154_;
}
else
{
lean_object* v_reuseFailAlloc_6158_; 
v_reuseFailAlloc_6158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6158_, 0, v___x_6153_);
v___x_6155_ = v_reuseFailAlloc_6158_;
goto v_reusejp_6154_;
}
v_reusejp_6154_:
{
lean_object* v___x_6156_; lean_object* v___x_6157_; 
v___x_6156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6156_, 0, v___x_6155_);
v___x_6157_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6152_, v___x_6125_, v___x_6156_, v___f_6151_);
return v___x_6157_;
}
}
else
{
lean_object* v___x_6159_; lean_object* v___x_6160_; 
lean_del_object(v___x_6139_);
lean_dec_ref(v_wd_6123_);
lean_dec_ref(v_config_6122_);
v___x_6159_ = lean_box(0);
v___x_6160_ = lean_apply_3(v___f_6121_, v___x_6159_, v_a_6137_, lean_box(0));
return v___x_6160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__11___boxed(lean_object* v___f_6162_, lean_object* v_config_6163_, lean_object* v_wd_6164_, lean_object* v_a_6165_, lean_object* v___x_6166_, lean_object* v_x_6167_, lean_object* v___y_6168_){
_start:
{
uint8_t v___x_9320__boxed_6169_; lean_object* v_res_6170_; 
v___x_9320__boxed_6169_ = lean_unbox(v___x_6166_);
v_res_6170_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__11(v___f_6162_, v_config_6163_, v_wd_6164_, v_a_6165_, v___x_9320__boxed_6169_, v_x_6167_);
lean_dec_ref(v_a_6165_);
return v_res_6170_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__12(lean_object* v___x_6171_, lean_object* v_h_6172_, lean_object* v_responseBodyInstance_6173_, lean_object* v_handler_6174_, lean_object* v_config_6175_, lean_object* v_a_6176_, uint8_t v___x_6177_, lean_object* v___f_6178_, lean_object* v_wd_6179_, lean_object* v_connectionContext_6180_, lean_object* v_inst_6181_, lean_object* v_socket_6182_, lean_object* v_maximumRecvSize_6183_, lean_object* v_x_6184_){
_start:
{
if (lean_obj_tag(v_x_6184_) == 0)
{
lean_object* v_a_6186_; lean_object* v___x_6188_; uint8_t v_isShared_6189_; uint8_t v_isSharedCheck_6194_; 
lean_dec(v_maximumRecvSize_6183_);
lean_dec(v_socket_6182_);
lean_dec_ref(v_inst_6181_);
lean_dec_ref(v_connectionContext_6180_);
lean_dec_ref(v_wd_6179_);
lean_dec_ref(v___f_6178_);
lean_dec_ref(v_a_6176_);
lean_dec_ref(v_config_6175_);
lean_dec(v_handler_6174_);
lean_dec_ref(v_responseBodyInstance_6173_);
lean_dec_ref(v_h_6172_);
lean_dec(v___x_6171_);
v_a_6186_ = lean_ctor_get(v_x_6184_, 0);
v_isSharedCheck_6194_ = !lean_is_exclusive(v_x_6184_);
if (v_isSharedCheck_6194_ == 0)
{
v___x_6188_ = v_x_6184_;
v_isShared_6189_ = v_isSharedCheck_6194_;
goto v_resetjp_6187_;
}
else
{
lean_inc(v_a_6186_);
lean_dec(v_x_6184_);
v___x_6188_ = lean_box(0);
v_isShared_6189_ = v_isSharedCheck_6194_;
goto v_resetjp_6187_;
}
v_resetjp_6187_:
{
lean_object* v___x_6191_; 
if (v_isShared_6189_ == 0)
{
v___x_6191_ = v___x_6188_;
goto v_reusejp_6190_;
}
else
{
lean_object* v_reuseFailAlloc_6193_; 
v_reuseFailAlloc_6193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6193_, 0, v_a_6186_);
v___x_6191_ = v_reuseFailAlloc_6193_;
goto v_reusejp_6190_;
}
v_reusejp_6190_:
{
lean_object* v___x_6192_; 
v___x_6192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6192_, 0, v___x_6191_);
return v___x_6192_;
}
}
}
else
{
lean_object* v_a_6195_; lean_object* v___x_6197_; uint8_t v_isShared_6198_; uint8_t v_isSharedCheck_6241_; 
v_a_6195_ = lean_ctor_get(v_x_6184_, 0);
v_isSharedCheck_6241_ = !lean_is_exclusive(v_x_6184_);
if (v_isSharedCheck_6241_ == 0)
{
v___x_6197_ = v_x_6184_;
v_isShared_6198_ = v_isSharedCheck_6241_;
goto v_resetjp_6196_;
}
else
{
lean_inc(v_a_6195_);
lean_dec(v_x_6184_);
v___x_6197_ = lean_box(0);
v_isShared_6198_ = v_isSharedCheck_6241_;
goto v_resetjp_6196_;
}
v_resetjp_6196_:
{
lean_object* v_machine_6205_; lean_object* v_requestStream_6206_; lean_object* v_timer_6207_; lean_object* v_response_6208_; lean_object* v_respStream_6209_; lean_object* v_inputWanted_6210_; lean_object* v_handler_6211_; lean_object* v_pendingHead_6212_; lean_object* v_dateSecond_6213_; uint8_t v_requestEnded_6214_; uint8_t v_aborted_6215_; uint8_t v___y_6229_; 
v_machine_6205_ = lean_ctor_get(v_a_6195_, 0);
v_requestStream_6206_ = lean_ctor_get(v_a_6195_, 1);
v_timer_6207_ = lean_ctor_get(v_a_6195_, 2);
v_response_6208_ = lean_ctor_get(v_a_6195_, 3);
v_respStream_6209_ = lean_ctor_get(v_a_6195_, 4);
v_inputWanted_6210_ = lean_ctor_get(v_a_6195_, 5);
v_handler_6211_ = lean_ctor_get(v_a_6195_, 6);
v_pendingHead_6212_ = lean_ctor_get(v_a_6195_, 7);
v_dateSecond_6213_ = lean_ctor_get(v_a_6195_, 8);
v_requestEnded_6214_ = lean_ctor_get_uint8(v_a_6195_, sizeof(void*)*9);
v_aborted_6215_ = lean_ctor_get_uint8(v_a_6195_, sizeof(void*)*9 + 1);
if (lean_obj_tag(v_inputWanted_6210_) == 0)
{
uint8_t v___x_6232_; 
v___x_6232_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_isRunning___redArg(v_handler_6211_);
if (v___x_6232_ == 0)
{
if (lean_obj_tag(v_respStream_6209_) == 0)
{
lean_object* v_writer_6233_; lean_object* v_state_6234_; 
v_writer_6233_ = lean_ctor_get(v_machine_6205_, 1);
v_state_6234_ = lean_ctor_get(v_writer_6233_, 2);
switch(lean_obj_tag(v_state_6234_))
{
case 6:
{
lean_dec(v_maximumRecvSize_6183_);
lean_dec(v_socket_6182_);
lean_dec_ref(v_inst_6181_);
lean_dec_ref(v_connectionContext_6180_);
lean_dec_ref(v_wd_6179_);
lean_dec_ref(v___f_6178_);
lean_dec_ref(v_a_6176_);
lean_dec_ref(v_config_6175_);
lean_dec(v_handler_6174_);
lean_dec_ref(v_responseBodyInstance_6173_);
lean_dec_ref(v_h_6172_);
lean_dec(v___x_6171_);
goto v___jp_6199_;
}
case 7:
{
lean_dec(v_maximumRecvSize_6183_);
lean_dec(v_socket_6182_);
lean_dec_ref(v_inst_6181_);
lean_dec_ref(v_connectionContext_6180_);
lean_dec_ref(v_wd_6179_);
lean_dec_ref(v___f_6178_);
lean_dec_ref(v_a_6176_);
lean_dec_ref(v_config_6175_);
lean_dec(v_handler_6174_);
lean_dec_ref(v_responseBodyInstance_6173_);
lean_dec_ref(v_h_6172_);
lean_dec(v___x_6171_);
goto v___jp_6199_;
}
default: 
{
switch(lean_obj_tag(v_state_6234_))
{
case 0:
{
v___y_6229_ = v___x_6232_;
goto v___jp_6228_;
}
case 1:
{
v___y_6229_ = v___x_6232_;
goto v___jp_6228_;
}
default: 
{
lean_object* v_reader_6235_; lean_object* v_state_6236_; 
v_reader_6235_ = lean_ctor_get(v_machine_6205_, 0);
v_state_6236_ = lean_ctor_get(v_reader_6235_, 0);
if (lean_obj_tag(v_state_6236_) == 2)
{
lean_object* v_a_6237_; 
v_a_6237_ = lean_ctor_get(v_state_6236_, 0);
if (lean_obj_tag(v_a_6237_) == 0)
{
lean_object* v_remaining_6238_; lean_object* v___x_6239_; uint8_t v___x_6240_; 
v_remaining_6238_ = lean_ctor_get(v_a_6237_, 0);
v___x_6239_ = lean_unsigned_to_nat(0u);
v___x_6240_ = lean_nat_dec_eq(v_remaining_6238_, v___x_6239_);
if (v___x_6240_ == 0)
{
v___y_6229_ = v___x_6240_;
goto v___jp_6228_;
}
else
{
lean_dec(v_maximumRecvSize_6183_);
lean_dec(v_socket_6182_);
lean_dec_ref(v_inst_6181_);
lean_dec_ref(v_connectionContext_6180_);
lean_dec_ref(v_wd_6179_);
lean_dec_ref(v___f_6178_);
lean_dec_ref(v_a_6176_);
lean_dec_ref(v_config_6175_);
lean_dec(v_handler_6174_);
lean_dec_ref(v_responseBodyInstance_6173_);
lean_dec_ref(v_h_6172_);
lean_dec(v___x_6171_);
goto v___jp_6199_;
}
}
else
{
v___y_6229_ = v___x_6232_;
goto v___jp_6228_;
}
}
else
{
v___y_6229_ = v___x_6232_;
goto v___jp_6228_;
}
}
}
}
}
}
else
{
lean_inc_ref(v_respStream_6209_);
lean_inc(v_inputWanted_6210_);
lean_inc(v_dateSecond_6213_);
lean_inc(v_pendingHead_6212_);
lean_inc(v_handler_6211_);
lean_inc_ref(v_response_6208_);
lean_inc(v_timer_6207_);
lean_inc_ref(v_requestStream_6206_);
lean_inc_ref(v_machine_6205_);
lean_del_object(v___x_6197_);
lean_dec(v_a_6195_);
goto v___jp_6216_;
}
}
else
{
lean_inc(v_inputWanted_6210_);
lean_inc(v_dateSecond_6213_);
lean_inc(v_pendingHead_6212_);
lean_inc(v_handler_6211_);
lean_inc(v_respStream_6209_);
lean_inc_ref(v_response_6208_);
lean_inc(v_timer_6207_);
lean_inc_ref(v_requestStream_6206_);
lean_inc_ref(v_machine_6205_);
lean_del_object(v___x_6197_);
lean_dec(v_a_6195_);
goto v___jp_6216_;
}
}
else
{
lean_inc_ref(v_inputWanted_6210_);
lean_inc(v_dateSecond_6213_);
lean_inc(v_pendingHead_6212_);
lean_inc(v_handler_6211_);
lean_inc(v_respStream_6209_);
lean_inc_ref(v_response_6208_);
lean_inc(v_timer_6207_);
lean_inc_ref(v_requestStream_6206_);
lean_inc_ref(v_machine_6205_);
lean_del_object(v___x_6197_);
lean_dec(v_a_6195_);
goto v___jp_6216_;
}
v___jp_6199_:
{
lean_object* v___x_6200_; lean_object* v___x_6202_; 
v___x_6200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6200_, 0, v_a_6195_);
if (v_isShared_6198_ == 0)
{
lean_ctor_set(v___x_6197_, 0, v___x_6200_);
v___x_6202_ = v___x_6197_;
goto v_reusejp_6201_;
}
else
{
lean_object* v_reuseFailAlloc_6204_; 
v_reuseFailAlloc_6204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6204_, 0, v___x_6200_);
v___x_6202_ = v_reuseFailAlloc_6204_;
goto v_reusejp_6201_;
}
v_reusejp_6201_:
{
lean_object* v___x_6203_; 
v___x_6203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6202_);
return v___x_6203_;
}
}
v___jp_6216_:
{
lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___f_6219_; lean_object* v___f_6220_; lean_object* v___x_6221_; lean_object* v___f_6222_; lean_object* v___x_6223_; lean_object* v___f_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; 
v___x_6217_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_6217_, 0, v_machine_6205_);
lean_ctor_set(v___x_6217_, 1, v_requestStream_6206_);
lean_ctor_set(v___x_6217_, 2, v_timer_6207_);
lean_ctor_set(v___x_6217_, 3, v_response_6208_);
lean_ctor_set(v___x_6217_, 4, v_respStream_6209_);
lean_ctor_set(v___x_6217_, 5, v___x_6171_);
lean_ctor_set(v___x_6217_, 6, v_handler_6211_);
lean_ctor_set(v___x_6217_, 7, v_pendingHead_6212_);
lean_ctor_set(v___x_6217_, 8, v_dateSecond_6213_);
lean_ctor_set_uint8(v___x_6217_, sizeof(void*)*9, v_requestEnded_6214_);
lean_ctor_set_uint8(v___x_6217_, sizeof(void*)*9 + 1, v_aborted_6215_);
v___x_6218_ = lean_box(v___x_6177_);
lean_inc_ref(v___x_6217_);
lean_inc_ref(v_a_6176_);
lean_inc_ref_n(v_config_6175_, 2);
lean_inc(v_handler_6174_);
lean_inc_ref(v_responseBodyInstance_6173_);
lean_inc_ref(v_h_6172_);
v___f_6219_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__5___boxed), 11, 8);
lean_closure_set(v___f_6219_, 0, v_h_6172_);
lean_closure_set(v___f_6219_, 1, v_responseBodyInstance_6173_);
lean_closure_set(v___f_6219_, 2, v_handler_6174_);
lean_closure_set(v___f_6219_, 3, v_config_6175_);
lean_closure_set(v___f_6219_, 4, v_a_6176_);
lean_closure_set(v___f_6219_, 5, v___x_6217_);
lean_closure_set(v___f_6219_, 6, v___x_6218_);
lean_closure_set(v___f_6219_, 7, v___f_6178_);
lean_inc_ref(v___f_6219_);
v___f_6220_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__4___boxed), 3, 1);
lean_closure_set(v___f_6220_, 0, v___f_6219_);
v___x_6221_ = lean_box(v___x_6177_);
lean_inc_ref(v_connectionContext_6180_);
lean_inc_ref(v_wd_6179_);
v___f_6222_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__9___boxed), 13, 10);
lean_closure_set(v___f_6222_, 0, v_wd_6179_);
lean_closure_set(v___f_6222_, 1, v_connectionContext_6180_);
lean_closure_set(v___f_6222_, 2, v___x_6221_);
lean_closure_set(v___f_6222_, 3, v___f_6220_);
lean_closure_set(v___f_6222_, 4, v___f_6219_);
lean_closure_set(v___f_6222_, 5, v_responseBodyInstance_6173_);
lean_closure_set(v___f_6222_, 6, v_inst_6181_);
lean_closure_set(v___f_6222_, 7, v_h_6172_);
lean_closure_set(v___f_6222_, 8, v_config_6175_);
lean_closure_set(v___f_6222_, 9, v_handler_6174_);
v___x_6223_ = lean_box(v___x_6177_);
v___f_6224_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__11___boxed), 7, 5);
lean_closure_set(v___f_6224_, 0, v___f_6222_);
lean_closure_set(v___f_6224_, 1, v_config_6175_);
lean_closure_set(v___f_6224_, 2, v_wd_6179_);
lean_closure_set(v___f_6224_, 3, v_a_6176_);
lean_closure_set(v___f_6224_, 4, v___x_6223_);
v___x_6225_ = lean_unsigned_to_nat(0u);
v___x_6226_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_buildPollSources___redArg(v_socket_6182_, v_connectionContext_6180_, v___x_6217_, v_inputWanted_6210_, v_maximumRecvSize_6183_);
v___x_6227_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6225_, v___x_6177_, v___x_6226_, v___f_6224_);
return v___x_6227_;
}
v___jp_6228_:
{
lean_object* v_reader_6230_; lean_object* v_state_6231_; 
v_reader_6230_ = lean_ctor_get(v_machine_6205_, 0);
v_state_6231_ = lean_ctor_get(v_reader_6230_, 0);
if (lean_obj_tag(v_state_6231_) == 2)
{
lean_inc(v_dateSecond_6213_);
lean_inc(v_pendingHead_6212_);
lean_inc(v_handler_6211_);
lean_inc(v_inputWanted_6210_);
lean_inc(v_respStream_6209_);
lean_inc_ref(v_response_6208_);
lean_inc(v_timer_6207_);
lean_inc_ref(v_requestStream_6206_);
lean_inc_ref(v_machine_6205_);
lean_del_object(v___x_6197_);
lean_dec(v_a_6195_);
goto v___jp_6216_;
}
else
{
if (v___y_6229_ == 0)
{
lean_dec(v_maximumRecvSize_6183_);
lean_dec(v_socket_6182_);
lean_dec_ref(v_inst_6181_);
lean_dec_ref(v_connectionContext_6180_);
lean_dec_ref(v_wd_6179_);
lean_dec_ref(v___f_6178_);
lean_dec_ref(v_a_6176_);
lean_dec_ref(v_config_6175_);
lean_dec(v_handler_6174_);
lean_dec_ref(v_responseBodyInstance_6173_);
lean_dec_ref(v_h_6172_);
lean_dec(v___x_6171_);
goto v___jp_6199_;
}
else
{
lean_inc(v_dateSecond_6213_);
lean_inc(v_pendingHead_6212_);
lean_inc(v_handler_6211_);
lean_inc(v_inputWanted_6210_);
lean_inc(v_respStream_6209_);
lean_inc_ref(v_response_6208_);
lean_inc(v_timer_6207_);
lean_inc_ref(v_requestStream_6206_);
lean_inc_ref(v_machine_6205_);
lean_del_object(v___x_6197_);
lean_dec(v_a_6195_);
goto v___jp_6216_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__12___boxed(lean_object* v___x_6242_, lean_object* v_h_6243_, lean_object* v_responseBodyInstance_6244_, lean_object* v_handler_6245_, lean_object* v_config_6246_, lean_object* v_a_6247_, lean_object* v___x_6248_, lean_object* v___f_6249_, lean_object* v_wd_6250_, lean_object* v_connectionContext_6251_, lean_object* v_inst_6252_, lean_object* v_socket_6253_, lean_object* v_maximumRecvSize_6254_, lean_object* v_x_6255_, lean_object* v___y_6256_){
_start:
{
uint8_t v___x_9387__boxed_6257_; lean_object* v_res_6258_; 
v___x_9387__boxed_6257_ = lean_unbox(v___x_6248_);
v_res_6258_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__12(v___x_6242_, v_h_6243_, v_responseBodyInstance_6244_, v_handler_6245_, v_config_6246_, v_a_6247_, v___x_9387__boxed_6257_, v___f_6249_, v_wd_6250_, v_connectionContext_6251_, v_inst_6252_, v_socket_6253_, v_maximumRecvSize_6254_, v_x_6255_);
return v_res_6258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__13(lean_object* v_h_6259_, lean_object* v_handler_6260_, lean_object* v_extensions_6261_, lean_object* v_connectionContext_6262_, uint8_t v___x_6263_, lean_object* v___f_6264_, lean_object* v_x_6265_){
_start:
{
if (lean_obj_tag(v_x_6265_) == 0)
{
lean_object* v_a_6267_; lean_object* v___x_6269_; uint8_t v_isShared_6270_; uint8_t v_isSharedCheck_6275_; 
lean_dec_ref(v___f_6264_);
lean_dec_ref(v_connectionContext_6262_);
lean_dec(v_extensions_6261_);
lean_dec(v_handler_6260_);
lean_dec_ref(v_h_6259_);
v_a_6267_ = lean_ctor_get(v_x_6265_, 0);
v_isSharedCheck_6275_ = !lean_is_exclusive(v_x_6265_);
if (v_isSharedCheck_6275_ == 0)
{
v___x_6269_ = v_x_6265_;
v_isShared_6270_ = v_isSharedCheck_6275_;
goto v_resetjp_6268_;
}
else
{
lean_inc(v_a_6267_);
lean_dec(v_x_6265_);
v___x_6269_ = lean_box(0);
v_isShared_6270_ = v_isSharedCheck_6275_;
goto v_resetjp_6268_;
}
v_resetjp_6268_:
{
lean_object* v___x_6272_; 
if (v_isShared_6270_ == 0)
{
v___x_6272_ = v___x_6269_;
goto v_reusejp_6271_;
}
else
{
lean_object* v_reuseFailAlloc_6274_; 
v_reuseFailAlloc_6274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6274_, 0, v_a_6267_);
v___x_6272_ = v_reuseFailAlloc_6274_;
goto v_reusejp_6271_;
}
v_reusejp_6271_:
{
lean_object* v___x_6273_; 
v___x_6273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6273_, 0, v___x_6272_);
return v___x_6273_;
}
}
}
else
{
lean_object* v_a_6276_; lean_object* v___x_6277_; lean_object* v___x_6278_; lean_object* v___x_6279_; 
v_a_6276_ = lean_ctor_get(v_x_6265_, 0);
lean_inc(v_a_6276_);
lean_dec_ref_known(v_x_6265_, 1);
v___x_6277_ = lean_unsigned_to_nat(0u);
v___x_6278_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_dispatchPendingRequest___redArg(v_h_6259_, v_handler_6260_, v_extensions_6261_, v_connectionContext_6262_, v_a_6276_);
v___x_6279_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6277_, v___x_6263_, v___x_6278_, v___f_6264_);
return v___x_6279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__13___boxed(lean_object* v_h_6280_, lean_object* v_handler_6281_, lean_object* v_extensions_6282_, lean_object* v_connectionContext_6283_, lean_object* v___x_6284_, lean_object* v___f_6285_, lean_object* v_x_6286_, lean_object* v___y_6287_){
_start:
{
uint8_t v___x_9487__boxed_6288_; lean_object* v_res_6289_; 
v___x_9487__boxed_6288_ = lean_unbox(v___x_6284_);
v_res_6289_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__13(v_h_6280_, v_handler_6281_, v_extensions_6282_, v_connectionContext_6283_, v___x_9487__boxed_6288_, v___f_6285_, v_x_6286_);
return v_res_6289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__14(lean_object* v_h_6290_, lean_object* v_responseBodyInstance_6291_, lean_object* v_handler_6292_, lean_object* v_config_6293_, lean_object* v_connectionContext_6294_, lean_object* v_events_6295_, lean_object* v___x_6296_, uint8_t v___x_6297_, lean_object* v___f_6298_, lean_object* v_____r_6299_){
_start:
{
lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; 
v___x_6301_ = lean_unsigned_to_nat(0u);
v___x_6302_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_processH1Events___redArg(v_h_6290_, v_responseBodyInstance_6291_, v_handler_6292_, v_config_6293_, v_connectionContext_6294_, v_events_6295_, v___x_6296_);
v___x_6303_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6301_, v___x_6297_, v___x_6302_, v___f_6298_);
return v___x_6303_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__14___boxed(lean_object* v_h_6304_, lean_object* v_responseBodyInstance_6305_, lean_object* v_handler_6306_, lean_object* v_config_6307_, lean_object* v_connectionContext_6308_, lean_object* v_events_6309_, lean_object* v___x_6310_, lean_object* v___x_6311_, lean_object* v___f_6312_, lean_object* v_____r_6313_, lean_object* v___y_6314_){
_start:
{
uint8_t v___x_9526__boxed_6315_; lean_object* v_res_6316_; 
v___x_9526__boxed_6315_ = lean_unbox(v___x_6311_);
v_res_6316_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__14(v_h_6304_, v_responseBodyInstance_6305_, v_handler_6306_, v_config_6307_, v_connectionContext_6308_, v_events_6309_, v___x_6310_, v___x_9526__boxed_6315_, v___f_6312_, v_____r_6313_);
return v_res_6316_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__15(lean_object* v_h_6317_, lean_object* v_handler_6318_, lean_object* v_a_6319_, lean_object* v___f_6320_, lean_object* v___f_6321_, lean_object* v_x_6322_){
_start:
{
if (lean_obj_tag(v_x_6322_) == 0)
{
lean_object* v_a_6324_; lean_object* v___x_6326_; uint8_t v_isShared_6327_; uint8_t v_isSharedCheck_6332_; 
lean_dec_ref(v___f_6321_);
lean_dec_ref(v___f_6320_);
lean_dec(v_handler_6318_);
lean_dec_ref(v_h_6317_);
v_a_6324_ = lean_ctor_get(v_x_6322_, 0);
v_isSharedCheck_6332_ = !lean_is_exclusive(v_x_6322_);
if (v_isSharedCheck_6332_ == 0)
{
v___x_6326_ = v_x_6322_;
v_isShared_6327_ = v_isSharedCheck_6332_;
goto v_resetjp_6325_;
}
else
{
lean_inc(v_a_6324_);
lean_dec(v_x_6322_);
v___x_6326_ = lean_box(0);
v_isShared_6327_ = v_isSharedCheck_6332_;
goto v_resetjp_6325_;
}
v_resetjp_6325_:
{
lean_object* v___x_6329_; 
if (v_isShared_6327_ == 0)
{
v___x_6329_ = v___x_6326_;
goto v_reusejp_6328_;
}
else
{
lean_object* v_reuseFailAlloc_6331_; 
v_reuseFailAlloc_6331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6331_, 0, v_a_6324_);
v___x_6329_ = v_reuseFailAlloc_6331_;
goto v_reusejp_6328_;
}
v_reusejp_6328_:
{
lean_object* v___x_6330_; 
v___x_6330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6330_, 0, v___x_6329_);
return v___x_6330_;
}
}
}
else
{
lean_object* v_a_6333_; uint8_t v___x_6334_; 
v_a_6333_ = lean_ctor_get(v_x_6322_, 0);
lean_inc(v_a_6333_);
lean_dec_ref_known(v_x_6322_, 1);
v___x_6334_ = lean_unbox(v_a_6333_);
if (v___x_6334_ == 0)
{
lean_object* v___x_6335_; lean_object* v___x_6336_; uint8_t v___x_6337_; lean_object* v___x_6338_; 
lean_dec_ref(v___f_6321_);
v___x_6335_ = lean_unsigned_to_nat(0u);
v___x_6336_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_h_6317_, v_handler_6318_, v_a_6319_);
v___x_6337_ = lean_unbox(v_a_6333_);
lean_dec(v_a_6333_);
v___x_6338_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6335_, v___x_6337_, v___x_6336_, v___f_6320_);
return v___x_6338_;
}
else
{
lean_object* v___x_6339_; lean_object* v___x_6340_; 
lean_dec(v_a_6333_);
lean_dec_ref(v___f_6320_);
lean_dec(v_handler_6318_);
lean_dec_ref(v_h_6317_);
v___x_6339_ = lean_box(0);
v___x_6340_ = lean_apply_2(v___f_6321_, v___x_6339_, lean_box(0));
return v___x_6340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__15___boxed(lean_object* v_h_6341_, lean_object* v_handler_6342_, lean_object* v_a_6343_, lean_object* v___f_6344_, lean_object* v___f_6345_, lean_object* v_x_6346_, lean_object* v___y_6347_){
_start:
{
lean_object* v_res_6348_; 
v_res_6348_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__15(v_h_6341_, v_handler_6342_, v_a_6343_, v___f_6344_, v___f_6345_, v_x_6346_);
lean_dec_ref(v_a_6343_);
return v_res_6348_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__16(lean_object* v_h_6349_, lean_object* v_handler_6350_, lean_object* v_a_6351_, lean_object* v___f_6352_, lean_object* v___x_6353_, lean_object* v_responseBodyInstance_6354_, lean_object* v_config_6355_, uint8_t v___x_6356_, lean_object* v___f_6357_, lean_object* v_wd_6358_, lean_object* v_connectionContext_6359_, lean_object* v_inst_6360_, lean_object* v_socket_6361_, lean_object* v_maximumRecvSize_6362_, lean_object* v_extensions_6363_, lean_object* v_events_6364_, lean_object* v___x_6365_, lean_object* v___f_6366_, lean_object* v___f_6367_, lean_object* v_x_6368_){
_start:
{
if (lean_obj_tag(v_x_6368_) == 0)
{
lean_object* v_a_6370_; lean_object* v___x_6372_; uint8_t v_isShared_6373_; uint8_t v_isSharedCheck_6378_; 
lean_dec_ref(v___f_6367_);
lean_dec_ref(v___f_6366_);
lean_dec_ref(v___x_6365_);
lean_dec_ref(v_events_6364_);
lean_dec(v_extensions_6363_);
lean_dec(v_maximumRecvSize_6362_);
lean_dec(v_socket_6361_);
lean_dec_ref(v_inst_6360_);
lean_dec_ref(v_connectionContext_6359_);
lean_dec_ref(v_wd_6358_);
lean_dec_ref(v___f_6357_);
lean_dec_ref(v_config_6355_);
lean_dec_ref(v_responseBodyInstance_6354_);
lean_dec(v___x_6353_);
lean_dec_ref(v___f_6352_);
lean_dec_ref(v_a_6351_);
lean_dec(v_handler_6350_);
lean_dec_ref(v_h_6349_);
v_a_6370_ = lean_ctor_get(v_x_6368_, 0);
v_isSharedCheck_6378_ = !lean_is_exclusive(v_x_6368_);
if (v_isSharedCheck_6378_ == 0)
{
v___x_6372_ = v_x_6368_;
v_isShared_6373_ = v_isSharedCheck_6378_;
goto v_resetjp_6371_;
}
else
{
lean_inc(v_a_6370_);
lean_dec(v_x_6368_);
v___x_6372_ = lean_box(0);
v_isShared_6373_ = v_isSharedCheck_6378_;
goto v_resetjp_6371_;
}
v_resetjp_6371_:
{
lean_object* v___x_6375_; 
if (v_isShared_6373_ == 0)
{
v___x_6375_ = v___x_6372_;
goto v_reusejp_6374_;
}
else
{
lean_object* v_reuseFailAlloc_6377_; 
v_reuseFailAlloc_6377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6377_, 0, v_a_6370_);
v___x_6375_ = v_reuseFailAlloc_6377_;
goto v_reusejp_6374_;
}
v_reusejp_6374_:
{
lean_object* v___x_6376_; 
v___x_6376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6376_, 0, v___x_6375_);
return v___x_6376_;
}
}
}
else
{
lean_object* v_a_6379_; uint8_t v___x_6380_; 
v_a_6379_ = lean_ctor_get(v_x_6368_, 0);
lean_inc(v_a_6379_);
lean_dec_ref_known(v_x_6368_, 1);
v___x_6380_ = lean_unbox(v_a_6379_);
if (v___x_6380_ == 0)
{
lean_object* v___x_6381_; lean_object* v___x_6382_; uint8_t v___x_6383_; lean_object* v___x_6384_; 
lean_dec_ref(v___f_6367_);
lean_dec_ref(v___f_6366_);
lean_dec_ref(v___x_6365_);
lean_dec_ref(v_events_6364_);
lean_dec(v_extensions_6363_);
lean_dec(v_maximumRecvSize_6362_);
lean_dec(v_socket_6361_);
lean_dec_ref(v_inst_6360_);
lean_dec_ref(v_connectionContext_6359_);
lean_dec_ref(v_wd_6358_);
lean_dec_ref(v___f_6357_);
lean_dec_ref(v_config_6355_);
lean_dec_ref(v_responseBodyInstance_6354_);
lean_dec(v___x_6353_);
v___x_6381_ = lean_unsigned_to_nat(0u);
v___x_6382_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_h_6349_, v_handler_6350_, v_a_6351_);
lean_dec_ref(v_a_6351_);
v___x_6383_ = lean_unbox(v_a_6379_);
lean_dec(v_a_6379_);
v___x_6384_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6381_, v___x_6383_, v___x_6382_, v___f_6352_);
return v___x_6384_;
}
else
{
lean_object* v___x_6385_; lean_object* v___f_6386_; lean_object* v___x_6387_; lean_object* v___f_6388_; lean_object* v___x_6389_; lean_object* v___f_6390_; lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; uint8_t v___x_6397_; 
lean_dec(v_a_6379_);
lean_dec_ref(v___f_6352_);
v___x_6385_ = lean_box(v___x_6356_);
lean_inc_ref_n(v_connectionContext_6359_, 3);
lean_inc_ref(v_a_6351_);
lean_inc_ref_n(v_config_6355_, 2);
lean_inc_n(v_handler_6350_, 3);
lean_inc_ref_n(v_responseBodyInstance_6354_, 2);
lean_inc_ref_n(v_h_6349_, 3);
v___f_6386_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__12___boxed), 15, 13);
lean_closure_set(v___f_6386_, 0, v___x_6353_);
lean_closure_set(v___f_6386_, 1, v_h_6349_);
lean_closure_set(v___f_6386_, 2, v_responseBodyInstance_6354_);
lean_closure_set(v___f_6386_, 3, v_handler_6350_);
lean_closure_set(v___f_6386_, 4, v_config_6355_);
lean_closure_set(v___f_6386_, 5, v_a_6351_);
lean_closure_set(v___f_6386_, 6, v___x_6385_);
lean_closure_set(v___f_6386_, 7, v___f_6357_);
lean_closure_set(v___f_6386_, 8, v_wd_6358_);
lean_closure_set(v___f_6386_, 9, v_connectionContext_6359_);
lean_closure_set(v___f_6386_, 10, v_inst_6360_);
lean_closure_set(v___f_6386_, 11, v_socket_6361_);
lean_closure_set(v___f_6386_, 12, v_maximumRecvSize_6362_);
v___x_6387_ = lean_box(v___x_6356_);
v___f_6388_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__13___boxed), 8, 6);
lean_closure_set(v___f_6388_, 0, v_h_6349_);
lean_closure_set(v___f_6388_, 1, v_handler_6350_);
lean_closure_set(v___f_6388_, 2, v_extensions_6363_);
lean_closure_set(v___f_6388_, 3, v_connectionContext_6359_);
lean_closure_set(v___f_6388_, 4, v___x_6387_);
lean_closure_set(v___f_6388_, 5, v___f_6386_);
v___x_6389_ = lean_box(v___x_6356_);
lean_inc_ref(v___f_6388_);
lean_inc_ref(v___x_6365_);
lean_inc_ref(v_events_6364_);
v___f_6390_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__14___boxed), 11, 9);
lean_closure_set(v___f_6390_, 0, v_h_6349_);
lean_closure_set(v___f_6390_, 1, v_responseBodyInstance_6354_);
lean_closure_set(v___f_6390_, 2, v_handler_6350_);
lean_closure_set(v___f_6390_, 3, v_config_6355_);
lean_closure_set(v___f_6390_, 4, v_connectionContext_6359_);
lean_closure_set(v___f_6390_, 5, v_events_6364_);
lean_closure_set(v___f_6390_, 6, v___x_6365_);
lean_closure_set(v___f_6390_, 7, v___x_6389_);
lean_closure_set(v___f_6390_, 8, v___f_6388_);
v___x_6394_ = lean_unsigned_to_nat(0u);
v___x_6395_ = lean_array_get_size(v_events_6364_);
v___x_6396_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_applyResponse___redArg___lam__8___closed__20));
v___x_6397_ = lean_nat_dec_lt(v___x_6394_, v___x_6395_);
if (v___x_6397_ == 0)
{
lean_dec_ref(v___f_6390_);
lean_dec_ref(v___f_6367_);
lean_dec_ref(v___f_6366_);
lean_dec_ref(v_a_6351_);
goto v___jp_6391_;
}
else
{
if (v___x_6397_ == 0)
{
lean_dec_ref(v___f_6390_);
lean_dec_ref(v___f_6367_);
lean_dec_ref(v___f_6366_);
lean_dec_ref(v_a_6351_);
goto v___jp_6391_;
}
else
{
size_t v___x_6398_; size_t v___x_6399_; lean_object* v___x_6400_; uint8_t v___x_6401_; 
v___x_6398_ = ((size_t)0ULL);
v___x_6399_ = lean_usize_of_nat(v___x_6395_);
lean_inc_ref(v_events_6364_);
v___x_6400_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_6396_, v___f_6366_, v_events_6364_, v___x_6398_, v___x_6399_);
v___x_6401_ = lean_unbox(v___x_6400_);
lean_dec(v___x_6400_);
if (v___x_6401_ == 0)
{
lean_dec_ref(v___f_6390_);
lean_dec_ref(v___f_6367_);
lean_dec_ref(v_a_6351_);
goto v___jp_6391_;
}
else
{
lean_object* v___f_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; 
lean_dec_ref(v___f_6388_);
lean_dec_ref(v___x_6365_);
lean_dec_ref(v_events_6364_);
lean_dec_ref(v_connectionContext_6359_);
lean_dec_ref(v_config_6355_);
lean_dec_ref(v_responseBodyInstance_6354_);
lean_inc_ref(v_a_6351_);
v___f_6402_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__15___boxed), 7, 5);
lean_closure_set(v___f_6402_, 0, v_h_6349_);
lean_closure_set(v___f_6402_, 1, v_handler_6350_);
lean_closure_set(v___f_6402_, 2, v_a_6351_);
lean_closure_set(v___f_6402_, 3, v___f_6367_);
lean_closure_set(v___f_6402_, 4, v___f_6390_);
v___x_6403_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg(v_a_6351_);
v___x_6404_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6394_, v___x_6356_, v___x_6403_, v___f_6402_);
return v___x_6404_;
}
}
}
v___jp_6391_:
{
lean_object* v___x_6392_; lean_object* v___x_6393_; 
v___x_6392_ = lean_box(0);
v___x_6393_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__14(v_h_6349_, v_responseBodyInstance_6354_, v_handler_6350_, v_config_6355_, v_connectionContext_6359_, v_events_6364_, v___x_6365_, v___x_6356_, v___f_6388_, v___x_6392_);
return v___x_6393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__16___boxed(lean_object** _args){
lean_object* v_h_6405_ = _args[0];
lean_object* v_handler_6406_ = _args[1];
lean_object* v_a_6407_ = _args[2];
lean_object* v___f_6408_ = _args[3];
lean_object* v___x_6409_ = _args[4];
lean_object* v_responseBodyInstance_6410_ = _args[5];
lean_object* v_config_6411_ = _args[6];
lean_object* v___x_6412_ = _args[7];
lean_object* v___f_6413_ = _args[8];
lean_object* v_wd_6414_ = _args[9];
lean_object* v_connectionContext_6415_ = _args[10];
lean_object* v_inst_6416_ = _args[11];
lean_object* v_socket_6417_ = _args[12];
lean_object* v_maximumRecvSize_6418_ = _args[13];
lean_object* v_extensions_6419_ = _args[14];
lean_object* v_events_6420_ = _args[15];
lean_object* v___x_6421_ = _args[16];
lean_object* v___f_6422_ = _args[17];
lean_object* v___f_6423_ = _args[18];
lean_object* v_x_6424_ = _args[19];
lean_object* v___y_6425_ = _args[20];
_start:
{
uint8_t v___x_9617__boxed_6426_; lean_object* v_res_6427_; 
v___x_9617__boxed_6426_ = lean_unbox(v___x_6412_);
v_res_6427_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__16(v_h_6405_, v_handler_6406_, v_a_6407_, v___f_6408_, v___x_6409_, v_responseBodyInstance_6410_, v_config_6411_, v___x_9617__boxed_6426_, v___f_6413_, v_wd_6414_, v_connectionContext_6415_, v_inst_6416_, v_socket_6417_, v_maximumRecvSize_6418_, v_extensions_6419_, v_events_6420_, v___x_6421_, v___f_6422_, v___f_6423_, v_x_6424_);
return v_res_6427_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__17(uint8_t v___x_6428_, lean_object* v_h_6429_, lean_object* v_handler_6430_, lean_object* v_a_6431_, lean_object* v___x_6432_, lean_object* v_responseBodyInstance_6433_, lean_object* v_config_6434_, uint8_t v___x_6435_, lean_object* v___f_6436_, lean_object* v_wd_6437_, lean_object* v_connectionContext_6438_, lean_object* v_inst_6439_, lean_object* v_socket_6440_, lean_object* v_maximumRecvSize_6441_, lean_object* v_extensions_6442_, lean_object* v___f_6443_, lean_object* v_x_6444_){
_start:
{
if (lean_obj_tag(v_x_6444_) == 0)
{
lean_object* v_a_6446_; lean_object* v___x_6448_; uint8_t v_isShared_6449_; uint8_t v_isSharedCheck_6454_; 
lean_dec_ref(v___f_6443_);
lean_dec(v_extensions_6442_);
lean_dec(v_maximumRecvSize_6441_);
lean_dec(v_socket_6440_);
lean_dec_ref(v_inst_6439_);
lean_dec_ref(v_connectionContext_6438_);
lean_dec_ref(v_wd_6437_);
lean_dec_ref(v___f_6436_);
lean_dec_ref(v_config_6434_);
lean_dec_ref(v_responseBodyInstance_6433_);
lean_dec(v___x_6432_);
lean_dec_ref(v_a_6431_);
lean_dec(v_handler_6430_);
lean_dec_ref(v_h_6429_);
v_a_6446_ = lean_ctor_get(v_x_6444_, 0);
v_isSharedCheck_6454_ = !lean_is_exclusive(v_x_6444_);
if (v_isSharedCheck_6454_ == 0)
{
v___x_6448_ = v_x_6444_;
v_isShared_6449_ = v_isSharedCheck_6454_;
goto v_resetjp_6447_;
}
else
{
lean_inc(v_a_6446_);
lean_dec(v_x_6444_);
v___x_6448_ = lean_box(0);
v_isShared_6449_ = v_isSharedCheck_6454_;
goto v_resetjp_6447_;
}
v_resetjp_6447_:
{
lean_object* v___x_6451_; 
if (v_isShared_6449_ == 0)
{
v___x_6451_ = v___x_6448_;
goto v_reusejp_6450_;
}
else
{
lean_object* v_reuseFailAlloc_6453_; 
v_reuseFailAlloc_6453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6453_, 0, v_a_6446_);
v___x_6451_ = v_reuseFailAlloc_6453_;
goto v_reusejp_6450_;
}
v_reusejp_6450_:
{
lean_object* v___x_6452_; 
v___x_6452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6452_, 0, v___x_6451_);
return v___x_6452_;
}
}
}
else
{
lean_object* v_a_6455_; lean_object* v_machine_6456_; lean_object* v_requestStream_6457_; lean_object* v_timer_6458_; lean_object* v_response_6459_; lean_object* v_respStream_6460_; lean_object* v_inputWanted_6461_; lean_object* v_handler_6462_; lean_object* v_pendingHead_6463_; lean_object* v_dateSecond_6464_; uint8_t v_requestEnded_6465_; uint8_t v_aborted_6466_; lean_object* v___x_6468_; uint8_t v_isShared_6469_; uint8_t v_isSharedCheck_6485_; 
v_a_6455_ = lean_ctor_get(v_x_6444_, 0);
lean_inc(v_a_6455_);
lean_dec_ref_known(v_x_6444_, 1);
v_machine_6456_ = lean_ctor_get(v_a_6455_, 0);
v_requestStream_6457_ = lean_ctor_get(v_a_6455_, 1);
v_timer_6458_ = lean_ctor_get(v_a_6455_, 2);
v_response_6459_ = lean_ctor_get(v_a_6455_, 3);
v_respStream_6460_ = lean_ctor_get(v_a_6455_, 4);
v_inputWanted_6461_ = lean_ctor_get(v_a_6455_, 5);
v_handler_6462_ = lean_ctor_get(v_a_6455_, 6);
v_pendingHead_6463_ = lean_ctor_get(v_a_6455_, 7);
v_dateSecond_6464_ = lean_ctor_get(v_a_6455_, 8);
v_requestEnded_6465_ = lean_ctor_get_uint8(v_a_6455_, sizeof(void*)*9);
v_aborted_6466_ = lean_ctor_get_uint8(v_a_6455_, sizeof(void*)*9 + 1);
v_isSharedCheck_6485_ = !lean_is_exclusive(v_a_6455_);
if (v_isSharedCheck_6485_ == 0)
{
v___x_6468_ = v_a_6455_;
v_isShared_6469_ = v_isSharedCheck_6485_;
goto v_resetjp_6467_;
}
else
{
lean_inc(v_dateSecond_6464_);
lean_inc(v_pendingHead_6463_);
lean_inc(v_handler_6462_);
lean_inc(v_inputWanted_6461_);
lean_inc(v_respStream_6460_);
lean_inc(v_response_6459_);
lean_inc(v_timer_6458_);
lean_inc(v_requestStream_6457_);
lean_inc(v_machine_6456_);
lean_dec(v_a_6455_);
v___x_6468_ = lean_box(0);
v_isShared_6469_ = v_isSharedCheck_6485_;
goto v_resetjp_6467_;
}
v_resetjp_6467_:
{
lean_object* v___x_6470_; lean_object* v_snd_6471_; lean_object* v_fst_6472_; lean_object* v_events_6473_; lean_object* v_output_6474_; lean_object* v___x_6476_; 
v___x_6470_ = l_Std_Http_Protocol_H1_Machine_step(v___x_6428_, v_machine_6456_);
v_snd_6471_ = lean_ctor_get(v___x_6470_, 1);
lean_inc(v_snd_6471_);
v_fst_6472_ = lean_ctor_get(v___x_6470_, 0);
lean_inc(v_fst_6472_);
lean_dec_ref(v___x_6470_);
v_events_6473_ = lean_ctor_get(v_snd_6471_, 0);
lean_inc_ref(v_events_6473_);
v_output_6474_ = lean_ctor_get(v_snd_6471_, 1);
lean_inc_ref(v_output_6474_);
lean_dec(v_snd_6471_);
if (v_isShared_6469_ == 0)
{
lean_ctor_set(v___x_6468_, 0, v_fst_6472_);
v___x_6476_ = v___x_6468_;
goto v_reusejp_6475_;
}
else
{
lean_object* v_reuseFailAlloc_6484_; 
v_reuseFailAlloc_6484_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v_reuseFailAlloc_6484_, 0, v_fst_6472_);
lean_ctor_set(v_reuseFailAlloc_6484_, 1, v_requestStream_6457_);
lean_ctor_set(v_reuseFailAlloc_6484_, 2, v_timer_6458_);
lean_ctor_set(v_reuseFailAlloc_6484_, 3, v_response_6459_);
lean_ctor_set(v_reuseFailAlloc_6484_, 4, v_respStream_6460_);
lean_ctor_set(v_reuseFailAlloc_6484_, 5, v_inputWanted_6461_);
lean_ctor_set(v_reuseFailAlloc_6484_, 6, v_handler_6462_);
lean_ctor_set(v_reuseFailAlloc_6484_, 7, v_pendingHead_6463_);
lean_ctor_set(v_reuseFailAlloc_6484_, 8, v_dateSecond_6464_);
lean_ctor_set_uint8(v_reuseFailAlloc_6484_, sizeof(void*)*9, v_requestEnded_6465_);
lean_ctor_set_uint8(v_reuseFailAlloc_6484_, sizeof(void*)*9 + 1, v_aborted_6466_);
v___x_6476_ = v_reuseFailAlloc_6484_;
goto v_reusejp_6475_;
}
v_reusejp_6475_:
{
lean_object* v___f_6477_; lean_object* v___x_6478_; lean_object* v___f_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; 
lean_inc_ref(v___x_6476_);
v___f_6477_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_6477_, 0, v___x_6476_);
v___x_6478_ = lean_box(v___x_6435_);
lean_inc_ref(v_inst_6439_);
lean_inc_ref(v___f_6477_);
lean_inc_ref(v_a_6431_);
v___f_6479_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__16___boxed), 21, 19);
lean_closure_set(v___f_6479_, 0, v_h_6429_);
lean_closure_set(v___f_6479_, 1, v_handler_6430_);
lean_closure_set(v___f_6479_, 2, v_a_6431_);
lean_closure_set(v___f_6479_, 3, v___f_6477_);
lean_closure_set(v___f_6479_, 4, v___x_6432_);
lean_closure_set(v___f_6479_, 5, v_responseBodyInstance_6433_);
lean_closure_set(v___f_6479_, 6, v_config_6434_);
lean_closure_set(v___f_6479_, 7, v___x_6478_);
lean_closure_set(v___f_6479_, 8, v___f_6436_);
lean_closure_set(v___f_6479_, 9, v_wd_6437_);
lean_closure_set(v___f_6479_, 10, v_connectionContext_6438_);
lean_closure_set(v___f_6479_, 11, v_inst_6439_);
lean_closure_set(v___f_6479_, 12, v_socket_6440_);
lean_closure_set(v___f_6479_, 13, v_maximumRecvSize_6441_);
lean_closure_set(v___f_6479_, 14, v_extensions_6442_);
lean_closure_set(v___f_6479_, 15, v_events_6473_);
lean_closure_set(v___f_6479_, 16, v___x_6476_);
lean_closure_set(v___f_6479_, 17, v___f_6443_);
lean_closure_set(v___f_6479_, 18, v___f_6477_);
v___x_6480_ = lean_unsigned_to_nat(65536u);
v___x_6481_ = lean_unsigned_to_nat(0u);
v___x_6482_ = l_Std_Http_Internal_Outbox_push___redArg(v_inst_6439_, v_a_6431_, v_output_6474_, v___x_6480_);
v___x_6483_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6481_, v___x_6435_, v___x_6482_, v___f_6479_);
return v___x_6483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__17___boxed(lean_object** _args){
lean_object* v___x_6486_ = _args[0];
lean_object* v_h_6487_ = _args[1];
lean_object* v_handler_6488_ = _args[2];
lean_object* v_a_6489_ = _args[3];
lean_object* v___x_6490_ = _args[4];
lean_object* v_responseBodyInstance_6491_ = _args[5];
lean_object* v_config_6492_ = _args[6];
lean_object* v___x_6493_ = _args[7];
lean_object* v___f_6494_ = _args[8];
lean_object* v_wd_6495_ = _args[9];
lean_object* v_connectionContext_6496_ = _args[10];
lean_object* v_inst_6497_ = _args[11];
lean_object* v_socket_6498_ = _args[12];
lean_object* v_maximumRecvSize_6499_ = _args[13];
lean_object* v_extensions_6500_ = _args[14];
lean_object* v___f_6501_ = _args[15];
lean_object* v_x_6502_ = _args[16];
lean_object* v___y_6503_ = _args[17];
_start:
{
uint8_t v___x_9726__boxed_6504_; uint8_t v___x_9729__boxed_6505_; lean_object* v_res_6506_; 
v___x_9726__boxed_6504_ = lean_unbox(v___x_6486_);
v___x_9729__boxed_6505_ = lean_unbox(v___x_6493_);
v_res_6506_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__17(v___x_9726__boxed_6504_, v_h_6487_, v_handler_6488_, v_a_6489_, v___x_6490_, v_responseBodyInstance_6491_, v_config_6492_, v___x_9729__boxed_6505_, v___f_6494_, v_wd_6495_, v_connectionContext_6496_, v_inst_6497_, v_socket_6498_, v_maximumRecvSize_6499_, v_extensions_6500_, v___f_6501_, v_x_6502_);
return v_res_6506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__18(lean_object* v_h_6507_, lean_object* v_handler_6508_, lean_object* v_a_6509_, lean_object* v___x_6510_, lean_object* v_responseBodyInstance_6511_, lean_object* v_config_6512_, uint8_t v___x_6513_, lean_object* v___f_6514_, lean_object* v_wd_6515_, lean_object* v_connectionContext_6516_, lean_object* v_inst_6517_, lean_object* v_socket_6518_, lean_object* v_maximumRecvSize_6519_, lean_object* v_extensions_6520_, lean_object* v___f_6521_, lean_object* v_x_6522_, lean_object* v_____s_6523_){
_start:
{
lean_object* v_machine_6525_; lean_object* v_reader_6526_; lean_object* v_writer_6527_; lean_object* v_state_6528_; uint8_t v___x_6529_; lean_object* v___x_6530_; lean_object* v___x_6531_; lean_object* v___f_6532_; lean_object* v___y_6534_; lean_object* v_val_6535_; 
v_machine_6525_ = lean_ctor_get(v_____s_6523_, 0);
v_reader_6526_ = lean_ctor_get(v_machine_6525_, 0);
v_writer_6527_ = lean_ctor_get(v_machine_6525_, 1);
v_state_6528_ = lean_ctor_get(v_reader_6526_, 0);
v___x_6529_ = 0;
v___x_6530_ = lean_box(v___x_6529_);
v___x_6531_ = lean_box(v___x_6513_);
lean_inc_ref(v_config_6512_);
v___f_6532_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__17___boxed), 18, 16);
lean_closure_set(v___f_6532_, 0, v___x_6530_);
lean_closure_set(v___f_6532_, 1, v_h_6507_);
lean_closure_set(v___f_6532_, 2, v_handler_6508_);
lean_closure_set(v___f_6532_, 3, v_a_6509_);
lean_closure_set(v___f_6532_, 4, v___x_6510_);
lean_closure_set(v___f_6532_, 5, v_responseBodyInstance_6511_);
lean_closure_set(v___f_6532_, 6, v_config_6512_);
lean_closure_set(v___f_6532_, 7, v___x_6531_);
lean_closure_set(v___f_6532_, 8, v___f_6514_);
lean_closure_set(v___f_6532_, 9, v_wd_6515_);
lean_closure_set(v___f_6532_, 10, v_connectionContext_6516_);
lean_closure_set(v___f_6532_, 11, v_inst_6517_);
lean_closure_set(v___f_6532_, 12, v_socket_6518_);
lean_closure_set(v___f_6532_, 13, v_maximumRecvSize_6519_);
lean_closure_set(v___f_6532_, 14, v_extensions_6520_);
lean_closure_set(v___f_6532_, 15, v___f_6521_);
if (lean_obj_tag(v_state_6528_) == 6)
{
lean_object* v_state_6557_; 
v_state_6557_ = lean_ctor_get(v_writer_6527_, 2);
if (lean_obj_tag(v_state_6557_) == 7)
{
lean_object* v_outputData_6558_; lean_object* v_size_6559_; lean_object* v___x_6560_; uint8_t v___x_6561_; 
v_outputData_6558_ = lean_ctor_get(v_writer_6527_, 1);
v_size_6559_ = lean_ctor_get(v_outputData_6558_, 1);
v___x_6560_ = lean_unsigned_to_nat(0u);
v___x_6561_ = lean_nat_dec_eq(v_size_6559_, v___x_6560_);
if (v___x_6561_ == 0)
{
goto v___jp_6538_;
}
else
{
lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; 
lean_dec_ref(v___f_6532_);
lean_dec_ref(v_config_6512_);
v___x_6562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6562_, 0, v_____s_6523_);
v___x_6563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6563_, 0, v___x_6562_);
v___x_6564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6564_, 0, v___x_6563_);
return v___x_6564_;
}
}
else
{
goto v___jp_6538_;
}
}
else
{
goto v___jp_6538_;
}
v___jp_6533_:
{
lean_object* v___x_6536_; lean_object* v___x_6537_; 
v___x_6536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6536_, 0, v_val_6535_);
v___x_6537_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___y_6534_, v___x_6513_, v___x_6536_, v___f_6532_);
return v___x_6537_;
}
v___jp_6538_:
{
lean_object* v___x_6539_; lean_object* v___x_6540_; 
v___x_6539_ = lean_unsigned_to_nat(0u);
v___x_6540_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_refreshDate___redArg(v_config_6512_, v_____s_6523_);
lean_dec_ref(v_config_6512_);
if (lean_obj_tag(v___x_6540_) == 0)
{
lean_object* v_a_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6548_; 
v_a_6541_ = lean_ctor_get(v___x_6540_, 0);
v_isSharedCheck_6548_ = !lean_is_exclusive(v___x_6540_);
if (v_isSharedCheck_6548_ == 0)
{
v___x_6543_ = v___x_6540_;
v_isShared_6544_ = v_isSharedCheck_6548_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_a_6541_);
lean_dec(v___x_6540_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6548_;
goto v_resetjp_6542_;
}
v_resetjp_6542_:
{
lean_object* v___x_6546_; 
if (v_isShared_6544_ == 0)
{
lean_ctor_set_tag(v___x_6543_, 1);
v___x_6546_ = v___x_6543_;
goto v_reusejp_6545_;
}
else
{
lean_object* v_reuseFailAlloc_6547_; 
v_reuseFailAlloc_6547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6547_, 0, v_a_6541_);
v___x_6546_ = v_reuseFailAlloc_6547_;
goto v_reusejp_6545_;
}
v_reusejp_6545_:
{
v___y_6534_ = v___x_6539_;
v_val_6535_ = v___x_6546_;
goto v___jp_6533_;
}
}
}
else
{
lean_object* v_a_6549_; lean_object* v___x_6551_; uint8_t v_isShared_6552_; uint8_t v_isSharedCheck_6556_; 
v_a_6549_ = lean_ctor_get(v___x_6540_, 0);
v_isSharedCheck_6556_ = !lean_is_exclusive(v___x_6540_);
if (v_isSharedCheck_6556_ == 0)
{
v___x_6551_ = v___x_6540_;
v_isShared_6552_ = v_isSharedCheck_6556_;
goto v_resetjp_6550_;
}
else
{
lean_inc(v_a_6549_);
lean_dec(v___x_6540_);
v___x_6551_ = lean_box(0);
v_isShared_6552_ = v_isSharedCheck_6556_;
goto v_resetjp_6550_;
}
v_resetjp_6550_:
{
lean_object* v___x_6554_; 
if (v_isShared_6552_ == 0)
{
lean_ctor_set_tag(v___x_6551_, 0);
v___x_6554_ = v___x_6551_;
goto v_reusejp_6553_;
}
else
{
lean_object* v_reuseFailAlloc_6555_; 
v_reuseFailAlloc_6555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6555_, 0, v_a_6549_);
v___x_6554_ = v_reuseFailAlloc_6555_;
goto v_reusejp_6553_;
}
v_reusejp_6553_:
{
v___y_6534_ = v___x_6539_;
v_val_6535_ = v___x_6554_;
goto v___jp_6533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__18___boxed(lean_object** _args){
lean_object* v_h_6565_ = _args[0];
lean_object* v_handler_6566_ = _args[1];
lean_object* v_a_6567_ = _args[2];
lean_object* v___x_6568_ = _args[3];
lean_object* v_responseBodyInstance_6569_ = _args[4];
lean_object* v_config_6570_ = _args[5];
lean_object* v___x_6571_ = _args[6];
lean_object* v___f_6572_ = _args[7];
lean_object* v_wd_6573_ = _args[8];
lean_object* v_connectionContext_6574_ = _args[9];
lean_object* v_inst_6575_ = _args[10];
lean_object* v_socket_6576_ = _args[11];
lean_object* v_maximumRecvSize_6577_ = _args[12];
lean_object* v_extensions_6578_ = _args[13];
lean_object* v___f_6579_ = _args[14];
lean_object* v_x_6580_ = _args[15];
lean_object* v_____s_6581_ = _args[16];
lean_object* v___y_6582_ = _args[17];
_start:
{
uint8_t v___x_9809__boxed_6583_; lean_object* v_res_6584_; 
v___x_9809__boxed_6583_ = lean_unbox(v___x_6571_);
v_res_6584_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__18(v_h_6565_, v_handler_6566_, v_a_6567_, v___x_6568_, v_responseBodyInstance_6569_, v_config_6570_, v___x_9809__boxed_6583_, v___f_6572_, v_wd_6573_, v_connectionContext_6574_, v_inst_6575_, v_socket_6576_, v_maximumRecvSize_6577_, v_extensions_6578_, v___f_6579_, v_x_6580_, v_____s_6581_);
return v_res_6584_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__19(lean_object* v_a_6585_, lean_object* v_maximumRecvSize_6586_, lean_object* v_inst_6587_, lean_object* v_socket_6588_, lean_object* v_lingeringTimeout_6589_, lean_object* v_serverContext_6590_, lean_object* v_x_6591_){
_start:
{
if (lean_obj_tag(v_x_6591_) == 0)
{
lean_object* v_a_6595_; lean_object* v___x_6597_; uint8_t v_isShared_6598_; uint8_t v_isSharedCheck_6603_; 
lean_dec_ref(v_serverContext_6590_);
lean_dec(v_lingeringTimeout_6589_);
lean_dec(v_socket_6588_);
lean_dec_ref(v_inst_6587_);
v_a_6595_ = lean_ctor_get(v_x_6591_, 0);
v_isSharedCheck_6603_ = !lean_is_exclusive(v_x_6591_);
if (v_isSharedCheck_6603_ == 0)
{
v___x_6597_ = v_x_6591_;
v_isShared_6598_ = v_isSharedCheck_6603_;
goto v_resetjp_6596_;
}
else
{
lean_inc(v_a_6595_);
lean_dec(v_x_6591_);
v___x_6597_ = lean_box(0);
v_isShared_6598_ = v_isSharedCheck_6603_;
goto v_resetjp_6596_;
}
v_resetjp_6596_:
{
lean_object* v___x_6600_; 
if (v_isShared_6598_ == 0)
{
v___x_6600_ = v___x_6597_;
goto v_reusejp_6599_;
}
else
{
lean_object* v_reuseFailAlloc_6602_; 
v_reuseFailAlloc_6602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6602_, 0, v_a_6595_);
v___x_6600_ = v_reuseFailAlloc_6602_;
goto v_reusejp_6599_;
}
v_reusejp_6599_:
{
lean_object* v___x_6601_; 
v___x_6601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6601_, 0, v___x_6600_);
return v___x_6601_;
}
}
}
else
{
lean_object* v_a_6604_; uint8_t v___x_6605_; 
v_a_6604_ = lean_ctor_get(v_x_6591_, 0);
lean_inc(v_a_6604_);
lean_dec_ref_known(v_x_6591_, 1);
v___x_6605_ = lean_unbox(v_a_6604_);
lean_dec(v_a_6604_);
if (v___x_6605_ == 0)
{
uint8_t v___x_6606_; 
v___x_6606_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_peerMayStillSend___redArg(v_a_6585_);
if (v___x_6606_ == 0)
{
lean_dec_ref(v_serverContext_6590_);
lean_dec(v_lingeringTimeout_6589_);
lean_dec(v_socket_6588_);
lean_dec_ref(v_inst_6587_);
goto v___jp_6593_;
}
else
{
uint64_t v___x_6607_; lean_object* v___x_6608_; 
v___x_6607_ = lean_uint64_of_nat(v_maximumRecvSize_6586_);
v___x_6608_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_linger___redArg(v_inst_6587_, v_socket_6588_, v_lingeringTimeout_6589_, v___x_6607_, v_serverContext_6590_);
return v___x_6608_;
}
}
else
{
lean_dec_ref(v_serverContext_6590_);
lean_dec(v_lingeringTimeout_6589_);
lean_dec(v_socket_6588_);
lean_dec_ref(v_inst_6587_);
goto v___jp_6593_;
}
}
v___jp_6593_:
{
lean_object* v___x_6594_; 
v___x_6594_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
return v___x_6594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__19___boxed(lean_object* v_a_6609_, lean_object* v_maximumRecvSize_6610_, lean_object* v_inst_6611_, lean_object* v_socket_6612_, lean_object* v_lingeringTimeout_6613_, lean_object* v_serverContext_6614_, lean_object* v_x_6615_, lean_object* v___y_6616_){
_start:
{
lean_object* v_res_6617_; 
v_res_6617_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__19(v_a_6609_, v_maximumRecvSize_6610_, v_inst_6611_, v_socket_6612_, v_lingeringTimeout_6613_, v_serverContext_6614_, v_x_6615_);
lean_dec(v_maximumRecvSize_6610_);
lean_dec_ref(v_a_6609_);
return v_res_6617_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__20(lean_object* v_a_6618_, uint8_t v___x_6619_, lean_object* v___f_6620_, lean_object* v_x_6621_){
_start:
{
if (lean_obj_tag(v_x_6621_) == 0)
{
lean_object* v___x_6623_; 
lean_dec_ref(v___f_6620_);
v___x_6623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6623_, 0, v_x_6621_);
return v___x_6623_;
}
else
{
lean_object* v___x_6625_; uint8_t v_isShared_6626_; uint8_t v_isSharedCheck_6635_; 
v_isSharedCheck_6635_ = !lean_is_exclusive(v_x_6621_);
if (v_isSharedCheck_6635_ == 0)
{
lean_object* v_unused_6636_; 
v_unused_6636_ = lean_ctor_get(v_x_6621_, 0);
lean_dec(v_unused_6636_);
v___x_6625_ = v_x_6621_;
v_isShared_6626_ = v_isSharedCheck_6635_;
goto v_resetjp_6624_;
}
else
{
lean_dec(v_x_6621_);
v___x_6625_ = lean_box(0);
v_isShared_6626_ = v_isSharedCheck_6635_;
goto v_resetjp_6624_;
}
v_resetjp_6624_:
{
lean_object* v___x_6627_; uint8_t v___x_6628_; lean_object* v___x_6629_; lean_object* v___x_6631_; 
v___x_6627_ = lean_unsigned_to_nat(0u);
v___x_6628_ = l_Std_Http_Internal_Outbox_failed___redArg(v_a_6618_);
v___x_6629_ = lean_box(v___x_6628_);
if (v_isShared_6626_ == 0)
{
lean_ctor_set(v___x_6625_, 0, v___x_6629_);
v___x_6631_ = v___x_6625_;
goto v_reusejp_6630_;
}
else
{
lean_object* v_reuseFailAlloc_6634_; 
v_reuseFailAlloc_6634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6634_, 0, v___x_6629_);
v___x_6631_ = v_reuseFailAlloc_6634_;
goto v_reusejp_6630_;
}
v_reusejp_6630_:
{
lean_object* v___x_6632_; lean_object* v___x_6633_; 
v___x_6632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6632_, 0, v___x_6631_);
v___x_6633_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6627_, v___x_6619_, v___x_6632_, v___f_6620_);
return v___x_6633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__20___boxed(lean_object* v_a_6637_, lean_object* v___x_6638_, lean_object* v___f_6639_, lean_object* v_x_6640_, lean_object* v___y_6641_){
_start:
{
uint8_t v___x_9951__boxed_6642_; lean_object* v_res_6643_; 
v___x_9951__boxed_6642_ = lean_unbox(v___x_6638_);
v_res_6643_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__20(v_a_6637_, v___x_9951__boxed_6642_, v___f_6639_, v_x_6640_);
lean_dec_ref(v_a_6637_);
return v_res_6643_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__21(lean_object* v_h_6644_, lean_object* v_handler_6645_, lean_object* v_a_6646_, uint8_t v___x_6647_, lean_object* v___f_6648_, lean_object* v_x_6649_){
_start:
{
if (lean_obj_tag(v_x_6649_) == 0)
{
lean_object* v___x_6651_; 
lean_dec_ref(v___f_6648_);
lean_dec(v_handler_6645_);
lean_dec_ref(v_h_6644_);
v___x_6651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6651_, 0, v_x_6649_);
return v___x_6651_;
}
else
{
lean_object* v___x_6652_; lean_object* v___x_6653_; lean_object* v___x_6654_; 
lean_dec_ref_known(v_x_6649_, 1);
v___x_6652_ = lean_unsigned_to_nat(0u);
v___x_6653_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportWriteFailure___redArg(v_h_6644_, v_handler_6645_, v_a_6646_);
v___x_6654_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6652_, v___x_6647_, v___x_6653_, v___f_6648_);
return v___x_6654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__21___boxed(lean_object* v_h_6655_, lean_object* v_handler_6656_, lean_object* v_a_6657_, lean_object* v___x_6658_, lean_object* v___f_6659_, lean_object* v_x_6660_, lean_object* v___y_6661_){
_start:
{
uint8_t v___x_9996__boxed_6662_; lean_object* v_res_6663_; 
v___x_9996__boxed_6662_ = lean_unbox(v___x_6658_);
v_res_6663_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__21(v_h_6655_, v_handler_6656_, v_a_6657_, v___x_9996__boxed_6662_, v___f_6659_, v_x_6660_);
lean_dec_ref(v_a_6657_);
return v_res_6663_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__22(lean_object* v_a_6664_, uint8_t v___x_6665_, lean_object* v___f_6666_, lean_object* v_____r_6667_){
_start:
{
lean_object* v___x_6669_; lean_object* v___x_6670_; lean_object* v___x_6671_; 
v___x_6669_ = lean_unsigned_to_nat(0u);
v___x_6670_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_a_6664_);
v___x_6671_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6669_, v___x_6665_, v___x_6670_, v___f_6666_);
return v___x_6671_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__22___boxed(lean_object* v_a_6672_, lean_object* v___x_6673_, lean_object* v___f_6674_, lean_object* v_____r_6675_, lean_object* v___y_6676_){
_start:
{
uint8_t v___x_10021__boxed_6677_; lean_object* v_res_6678_; 
v___x_10021__boxed_6677_ = lean_unbox(v___x_6673_);
v_res_6678_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__22(v_a_6672_, v___x_10021__boxed_6677_, v___f_6674_, v_____r_6675_);
return v_res_6678_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__23(lean_object* v___f_6679_, lean_object* v_x_6680_){
_start:
{
if (lean_obj_tag(v_x_6680_) == 0)
{
lean_object* v___x_6682_; 
lean_dec_ref(v___f_6679_);
v___x_6682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6682_, 0, v_x_6680_);
return v___x_6682_;
}
else
{
lean_object* v_a_6683_; lean_object* v___x_6684_; 
v_a_6683_ = lean_ctor_get(v_x_6680_, 0);
lean_inc(v_a_6683_);
lean_dec_ref_known(v_x_6680_, 1);
v___x_6684_ = lean_apply_2(v___f_6679_, v_a_6683_, lean_box(0));
return v___x_6684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__23___boxed(lean_object* v___f_6685_, lean_object* v_x_6686_, lean_object* v___y_6687_){
_start:
{
lean_object* v_res_6688_; 
v_res_6688_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__23(v___f_6685_, v_x_6686_);
return v_res_6688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__24(lean_object* v_a_6689_, lean_object* v___f_6690_, uint8_t v___x_6691_, lean_object* v___f_6692_, lean_object* v___f_6693_, lean_object* v_____r_6694_){
_start:
{
lean_object* v_handler_6696_; lean_object* v___x_6697_; 
v_handler_6696_ = lean_ctor_get(v_a_6689_, 6);
lean_inc(v_handler_6696_);
lean_dec_ref(v_a_6689_);
v___x_6697_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_HandlerState_task_x3f___redArg(v_handler_6696_);
if (lean_obj_tag(v___x_6697_) == 1)
{
lean_object* v_val_6698_; lean_object* v___x_6699_; lean_object* v___x_6700_; lean_object* v___x_6701_; lean_object* v___x_6702_; lean_object* v___x_6703_; lean_object* v___x_6704_; lean_object* v___x_6705_; 
lean_dec_ref(v___f_6693_);
v_val_6698_ = lean_ctor_get(v___x_6697_, 0);
lean_inc(v_val_6698_);
lean_dec_ref_known(v___x_6697_, 1);
v___x_6699_ = lean_alloc_closure((void*)(l_Std_Async_Async_ofTask___boxed), 3, 2);
lean_closure_set(v___x_6699_, 0, lean_box(0));
lean_closure_set(v___x_6699_, 1, v_val_6698_);
v___x_6700_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___boxed), 6, 5);
lean_closure_set(v___x_6700_, 0, lean_box(0));
lean_closure_set(v___x_6700_, 1, lean_box(0));
lean_closure_set(v___x_6700_, 2, lean_box(0));
lean_closure_set(v___x_6700_, 3, v___x_6699_);
lean_closure_set(v___x_6700_, 4, v___f_6690_);
v___x_6701_ = lean_unsigned_to_nat(0u);
v___x_6702_ = lean_alloc_closure((void*)(l_Std_Async_BaseAsync_toRawBaseIO___boxed), 3, 2);
lean_closure_set(v___x_6702_, 0, lean_box(0));
lean_closure_set(v___x_6702_, 1, v___x_6700_);
v___x_6703_ = lean_io_as_task(v___x_6702_, v___x_6701_);
lean_dec_ref(v___x_6703_);
v___x_6704_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_reportFailure___redArg___lam__0___closed__1));
v___x_6705_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6701_, v___x_6691_, v___x_6704_, v___f_6692_);
return v___x_6705_;
}
else
{
lean_object* v___x_6706_; lean_object* v___x_6707_; 
lean_dec(v___x_6697_);
lean_dec_ref(v___f_6692_);
lean_dec_ref(v___f_6690_);
v___x_6706_ = lean_box(0);
v___x_6707_ = lean_apply_2(v___f_6693_, v___x_6706_, lean_box(0));
return v___x_6707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__24___boxed(lean_object* v_a_6708_, lean_object* v___f_6709_, lean_object* v___x_6710_, lean_object* v___f_6711_, lean_object* v___f_6712_, lean_object* v_____r_6713_, lean_object* v___y_6714_){
_start:
{
uint8_t v___x_10063__boxed_6715_; lean_object* v_res_6716_; 
v___x_10063__boxed_6715_ = lean_unbox(v___x_6710_);
v_res_6716_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__24(v_a_6708_, v___f_6709_, v___x_10063__boxed_6715_, v___f_6711_, v___f_6712_, v_____r_6713_);
return v_res_6716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__26(lean_object* v_close_6717_, lean_object* v_val_6718_, uint8_t v___x_6719_, lean_object* v___f_6720_, lean_object* v___f_6721_, lean_object* v_x_6722_){
_start:
{
if (lean_obj_tag(v_x_6722_) == 0)
{
lean_object* v_a_6724_; lean_object* v___x_6726_; uint8_t v_isShared_6727_; uint8_t v_isSharedCheck_6732_; 
lean_dec_ref(v___f_6721_);
lean_dec_ref(v___f_6720_);
lean_dec(v_val_6718_);
lean_dec_ref(v_close_6717_);
v_a_6724_ = lean_ctor_get(v_x_6722_, 0);
v_isSharedCheck_6732_ = !lean_is_exclusive(v_x_6722_);
if (v_isSharedCheck_6732_ == 0)
{
v___x_6726_ = v_x_6722_;
v_isShared_6727_ = v_isSharedCheck_6732_;
goto v_resetjp_6725_;
}
else
{
lean_inc(v_a_6724_);
lean_dec(v_x_6722_);
v___x_6726_ = lean_box(0);
v_isShared_6727_ = v_isSharedCheck_6732_;
goto v_resetjp_6725_;
}
v_resetjp_6725_:
{
lean_object* v___x_6729_; 
if (v_isShared_6727_ == 0)
{
v___x_6729_ = v___x_6726_;
goto v_reusejp_6728_;
}
else
{
lean_object* v_reuseFailAlloc_6731_; 
v_reuseFailAlloc_6731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6731_, 0, v_a_6724_);
v___x_6729_ = v_reuseFailAlloc_6731_;
goto v_reusejp_6728_;
}
v_reusejp_6728_:
{
lean_object* v___x_6730_; 
v___x_6730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6730_, 0, v___x_6729_);
return v___x_6730_;
}
}
}
else
{
lean_object* v_a_6733_; uint8_t v___x_6734_; 
v_a_6733_ = lean_ctor_get(v_x_6722_, 0);
lean_inc(v_a_6733_);
lean_dec_ref_known(v_x_6722_, 1);
v___x_6734_ = lean_unbox(v_a_6733_);
lean_dec(v_a_6733_);
if (v___x_6734_ == 0)
{
lean_object* v___x_6735_; lean_object* v___x_6736_; lean_object* v___x_6737_; 
lean_dec_ref(v___f_6721_);
v___x_6735_ = lean_unsigned_to_nat(0u);
v___x_6736_ = lean_apply_2(v_close_6717_, v_val_6718_, lean_box(0));
v___x_6737_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6735_, v___x_6719_, v___x_6736_, v___f_6720_);
return v___x_6737_;
}
else
{
lean_object* v___x_6738_; lean_object* v___x_6739_; 
lean_dec_ref(v___f_6720_);
lean_dec(v_val_6718_);
lean_dec_ref(v_close_6717_);
v___x_6738_ = lean_box(0);
v___x_6739_ = lean_apply_2(v___f_6721_, v___x_6738_, lean_box(0));
return v___x_6739_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__26___boxed(lean_object* v_close_6740_, lean_object* v_val_6741_, lean_object* v___x_6742_, lean_object* v___f_6743_, lean_object* v___f_6744_, lean_object* v_x_6745_, lean_object* v___y_6746_){
_start:
{
uint8_t v___x_10107__boxed_6747_; lean_object* v_res_6748_; 
v___x_10107__boxed_6747_ = lean_unbox(v___x_6742_);
v_res_6748_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__26(v_close_6740_, v_val_6741_, v___x_10107__boxed_6747_, v___f_6743_, v___f_6744_, v_x_6745_);
return v_res_6748_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__25(lean_object* v_a_6749_, lean_object* v_responseBodyInstance_6750_, uint8_t v___x_6751_, lean_object* v___f_6752_, lean_object* v___f_6753_, lean_object* v_____r_6754_){
_start:
{
lean_object* v_respStream_6756_; 
v_respStream_6756_ = lean_ctor_get(v_a_6749_, 4);
lean_inc(v_respStream_6756_);
lean_dec_ref(v_a_6749_);
if (lean_obj_tag(v_respStream_6756_) == 1)
{
lean_object* v_val_6757_; lean_object* v_close_6758_; lean_object* v_isClosed_6759_; lean_object* v___x_6760_; lean_object* v___f_6761_; lean_object* v___x_6762_; lean_object* v___x_6763_; lean_object* v___x_6764_; 
v_val_6757_ = lean_ctor_get(v_respStream_6756_, 0);
lean_inc_n(v_val_6757_, 2);
lean_dec_ref_known(v_respStream_6756_, 1);
v_close_6758_ = lean_ctor_get(v_responseBodyInstance_6750_, 1);
lean_inc_ref(v_close_6758_);
v_isClosed_6759_ = lean_ctor_get(v_responseBodyInstance_6750_, 2);
lean_inc_ref(v_isClosed_6759_);
lean_dec_ref(v_responseBodyInstance_6750_);
v___x_6760_ = lean_box(v___x_6751_);
v___f_6761_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__26___boxed), 7, 5);
lean_closure_set(v___f_6761_, 0, v_close_6758_);
lean_closure_set(v___f_6761_, 1, v_val_6757_);
lean_closure_set(v___f_6761_, 2, v___x_6760_);
lean_closure_set(v___f_6761_, 3, v___f_6752_);
lean_closure_set(v___f_6761_, 4, v___f_6753_);
v___x_6762_ = lean_unsigned_to_nat(0u);
v___x_6763_ = lean_apply_2(v_isClosed_6759_, v_val_6757_, lean_box(0));
v___x_6764_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6762_, v___x_6751_, v___x_6763_, v___f_6761_);
return v___x_6764_;
}
else
{
lean_object* v___x_6765_; lean_object* v___x_6766_; 
lean_dec(v_respStream_6756_);
lean_dec_ref(v___f_6752_);
lean_dec_ref(v_responseBodyInstance_6750_);
v___x_6765_ = lean_box(0);
v___x_6766_ = lean_apply_2(v___f_6753_, v___x_6765_, lean_box(0));
return v___x_6766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__25___boxed(lean_object* v_a_6767_, lean_object* v_responseBodyInstance_6768_, lean_object* v___x_6769_, lean_object* v___f_6770_, lean_object* v___f_6771_, lean_object* v_____r_6772_, lean_object* v___y_6773_){
_start:
{
uint8_t v___x_10157__boxed_6774_; lean_object* v_res_6775_; 
v___x_10157__boxed_6774_ = lean_unbox(v___x_6769_);
v_res_6775_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__25(v_a_6767_, v_responseBodyInstance_6768_, v___x_10157__boxed_6774_, v___f_6770_, v___f_6771_, v_____r_6772_);
return v_res_6775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__27(lean_object* v_close_6776_, lean_object* v_socket_6777_, lean_object* v_x_6778_){
_start:
{
lean_object* v_val_6781_; lean_object* v___x_6783_; 
v___x_6783_ = lean_apply_2(v_close_6776_, v_socket_6777_, lean_box(0));
if (lean_obj_tag(v___x_6783_) == 0)
{
lean_object* v_a_6784_; lean_object* v___x_6786_; uint8_t v_isShared_6787_; uint8_t v_isSharedCheck_6791_; 
v_a_6784_ = lean_ctor_get(v___x_6783_, 0);
v_isSharedCheck_6791_ = !lean_is_exclusive(v___x_6783_);
if (v_isSharedCheck_6791_ == 0)
{
v___x_6786_ = v___x_6783_;
v_isShared_6787_ = v_isSharedCheck_6791_;
goto v_resetjp_6785_;
}
else
{
lean_inc(v_a_6784_);
lean_dec(v___x_6783_);
v___x_6786_ = lean_box(0);
v_isShared_6787_ = v_isSharedCheck_6791_;
goto v_resetjp_6785_;
}
v_resetjp_6785_:
{
lean_object* v___x_6789_; 
if (v_isShared_6787_ == 0)
{
lean_ctor_set_tag(v___x_6786_, 1);
v___x_6789_ = v___x_6786_;
goto v_reusejp_6788_;
}
else
{
lean_object* v_reuseFailAlloc_6790_; 
v_reuseFailAlloc_6790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6790_, 0, v_a_6784_);
v___x_6789_ = v_reuseFailAlloc_6790_;
goto v_reusejp_6788_;
}
v_reusejp_6788_:
{
v_val_6781_ = v___x_6789_;
goto v___jp_6780_;
}
}
}
else
{
lean_object* v_a_6792_; lean_object* v___x_6794_; uint8_t v_isShared_6795_; uint8_t v_isSharedCheck_6799_; 
v_a_6792_ = lean_ctor_get(v___x_6783_, 0);
v_isSharedCheck_6799_ = !lean_is_exclusive(v___x_6783_);
if (v_isSharedCheck_6799_ == 0)
{
v___x_6794_ = v___x_6783_;
v_isShared_6795_ = v_isSharedCheck_6799_;
goto v_resetjp_6793_;
}
else
{
lean_inc(v_a_6792_);
lean_dec(v___x_6783_);
v___x_6794_ = lean_box(0);
v_isShared_6795_ = v_isSharedCheck_6799_;
goto v_resetjp_6793_;
}
v_resetjp_6793_:
{
lean_object* v___x_6797_; 
if (v_isShared_6795_ == 0)
{
lean_ctor_set_tag(v___x_6794_, 0);
v___x_6797_ = v___x_6794_;
goto v_reusejp_6796_;
}
else
{
lean_object* v_reuseFailAlloc_6798_; 
v_reuseFailAlloc_6798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6798_, 0, v_a_6792_);
v___x_6797_ = v_reuseFailAlloc_6798_;
goto v_reusejp_6796_;
}
v_reusejp_6796_:
{
v_val_6781_ = v___x_6797_;
goto v___jp_6780_;
}
}
}
v___jp_6780_:
{
lean_object* v___x_6782_; 
v___x_6782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6782_, 0, v_val_6781_);
return v___x_6782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__27___boxed(lean_object* v_close_6800_, lean_object* v_socket_6801_, lean_object* v_x_6802_, lean_object* v___y_6803_){
_start:
{
lean_object* v_res_6804_; 
v_res_6804_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__27(v_close_6800_, v_socket_6801_, v_x_6802_);
lean_dec(v_x_6802_);
return v_res_6804_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__28(lean_object* v_inst_6806_, lean_object* v_maximumRecvSize_6807_, lean_object* v_socket_6808_, lean_object* v_lingeringTimeout_6809_, lean_object* v_serverContext_6810_, lean_object* v_a_6811_, uint8_t v___x_6812_, lean_object* v_h_6813_, lean_object* v_handler_6814_, lean_object* v___f_6815_, lean_object* v_responseBodyInstance_6816_, lean_object* v___f_6817_, lean_object* v_x_6818_){
_start:
{
if (lean_obj_tag(v_x_6818_) == 0)
{
lean_object* v_a_6820_; lean_object* v___x_6822_; uint8_t v_isShared_6823_; uint8_t v_isSharedCheck_6828_; 
lean_dec_ref(v___f_6817_);
lean_dec_ref(v_responseBodyInstance_6816_);
lean_dec_ref(v___f_6815_);
lean_dec(v_handler_6814_);
lean_dec_ref(v_h_6813_);
lean_dec_ref(v_a_6811_);
lean_dec_ref(v_serverContext_6810_);
lean_dec(v_lingeringTimeout_6809_);
lean_dec(v_socket_6808_);
lean_dec(v_maximumRecvSize_6807_);
lean_dec_ref(v_inst_6806_);
v_a_6820_ = lean_ctor_get(v_x_6818_, 0);
v_isSharedCheck_6828_ = !lean_is_exclusive(v_x_6818_);
if (v_isSharedCheck_6828_ == 0)
{
v___x_6822_ = v_x_6818_;
v_isShared_6823_ = v_isSharedCheck_6828_;
goto v_resetjp_6821_;
}
else
{
lean_inc(v_a_6820_);
lean_dec(v_x_6818_);
v___x_6822_ = lean_box(0);
v_isShared_6823_ = v_isSharedCheck_6828_;
goto v_resetjp_6821_;
}
v_resetjp_6821_:
{
lean_object* v___x_6825_; 
if (v_isShared_6823_ == 0)
{
v___x_6825_ = v___x_6822_;
goto v_reusejp_6824_;
}
else
{
lean_object* v_reuseFailAlloc_6827_; 
v_reuseFailAlloc_6827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6827_, 0, v_a_6820_);
v___x_6825_ = v_reuseFailAlloc_6827_;
goto v_reusejp_6824_;
}
v_reusejp_6824_:
{
lean_object* v___x_6826_; 
v___x_6826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6826_, 0, v___x_6825_);
return v___x_6826_;
}
}
}
else
{
lean_object* v_a_6829_; lean_object* v_close_6830_; lean_object* v___f_6831_; lean_object* v___x_6832_; lean_object* v___f_6833_; lean_object* v___x_6834_; lean_object* v___f_6835_; lean_object* v___x_6836_; lean_object* v___f_6837_; lean_object* v___f_6838_; lean_object* v___x_6839_; lean_object* v___f_6840_; lean_object* v___f_6841_; lean_object* v___x_6842_; lean_object* v___f_6843_; lean_object* v___x_6844_; lean_object* v___x_6845_; lean_object* v___x_6846_; lean_object* v___f_6847_; lean_object* v___x_6848_; lean_object* v___x_6849_; lean_object* v___x_6850_; lean_object* v___y_6852_; 
v_a_6829_ = lean_ctor_get(v_x_6818_, 0);
lean_inc_n(v_a_6829_, 4);
lean_dec_ref_known(v_x_6818_, 1);
v_close_6830_ = lean_ctor_get(v_inst_6806_, 3);
lean_inc_ref(v_close_6830_);
lean_inc(v_socket_6808_);
v___f_6831_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__19___boxed), 8, 6);
lean_closure_set(v___f_6831_, 0, v_a_6829_);
lean_closure_set(v___f_6831_, 1, v_maximumRecvSize_6807_);
lean_closure_set(v___f_6831_, 2, v_inst_6806_);
lean_closure_set(v___f_6831_, 3, v_socket_6808_);
lean_closure_set(v___f_6831_, 4, v_lingeringTimeout_6809_);
lean_closure_set(v___f_6831_, 5, v_serverContext_6810_);
v___x_6832_ = lean_box(v___x_6812_);
lean_inc_ref_n(v_a_6811_, 2);
v___f_6833_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__20___boxed), 5, 3);
lean_closure_set(v___f_6833_, 0, v_a_6811_);
lean_closure_set(v___f_6833_, 1, v___x_6832_);
lean_closure_set(v___f_6833_, 2, v___f_6831_);
v___x_6834_ = lean_box(v___x_6812_);
v___f_6835_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__21___boxed), 7, 5);
lean_closure_set(v___f_6835_, 0, v_h_6813_);
lean_closure_set(v___f_6835_, 1, v_handler_6814_);
lean_closure_set(v___f_6835_, 2, v_a_6811_);
lean_closure_set(v___f_6835_, 3, v___x_6834_);
lean_closure_set(v___f_6835_, 4, v___f_6833_);
v___x_6836_ = lean_box(v___x_6812_);
v___f_6837_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__22___boxed), 5, 3);
lean_closure_set(v___f_6837_, 0, v_a_6811_);
lean_closure_set(v___f_6837_, 1, v___x_6836_);
lean_closure_set(v___f_6837_, 2, v___f_6835_);
lean_inc_ref(v___f_6837_);
v___f_6838_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__23___boxed), 3, 1);
lean_closure_set(v___f_6838_, 0, v___f_6837_);
v___x_6839_ = lean_box(v___x_6812_);
v___f_6840_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__24___boxed), 7, 5);
lean_closure_set(v___f_6840_, 0, v_a_6829_);
lean_closure_set(v___f_6840_, 1, v___f_6815_);
lean_closure_set(v___f_6840_, 2, v___x_6839_);
lean_closure_set(v___f_6840_, 3, v___f_6838_);
lean_closure_set(v___f_6840_, 4, v___f_6837_);
lean_inc_ref(v___f_6840_);
v___f_6841_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__23___boxed), 3, 1);
lean_closure_set(v___f_6841_, 0, v___f_6840_);
v___x_6842_ = lean_box(v___x_6812_);
v___f_6843_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__25___boxed), 7, 5);
lean_closure_set(v___f_6843_, 0, v_a_6829_);
lean_closure_set(v___f_6843_, 1, v_responseBodyInstance_6816_);
lean_closure_set(v___f_6843_, 2, v___x_6842_);
lean_closure_set(v___f_6843_, 3, v___f_6841_);
lean_closure_set(v___f_6843_, 4, v___f_6840_);
v___x_6844_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__28___closed__0));
v___x_6845_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_endRequestStream___boxed), 4, 3);
lean_closure_set(v___x_6845_, 0, lean_box(0));
lean_closure_set(v___x_6845_, 1, v_a_6829_);
lean_closure_set(v___x_6845_, 2, v___x_6844_);
v___x_6846_ = lean_alloc_closure((void*)(l_Std_Async_EAsync_bind___boxed), 6, 5);
lean_closure_set(v___x_6846_, 0, lean_box(0));
lean_closure_set(v___x_6846_, 1, lean_box(0));
lean_closure_set(v___x_6846_, 2, lean_box(0));
lean_closure_set(v___x_6846_, 3, v___x_6845_);
lean_closure_set(v___x_6846_, 4, v___f_6843_);
v___f_6847_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__27___boxed), 4, 2);
lean_closure_set(v___f_6847_, 0, v_close_6830_);
lean_closure_set(v___f_6847_, 1, v_socket_6808_);
v___x_6848_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_6848_, 0, lean_box(0));
lean_closure_set(v___x_6848_, 1, lean_box(0));
lean_closure_set(v___x_6848_, 2, lean_box(0));
lean_closure_set(v___x_6848_, 3, v___f_6817_);
v___x_6849_ = lean_unsigned_to_nat(0u);
v___x_6850_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_6846_, v___f_6847_, v___x_6849_, v___x_6812_);
if (lean_obj_tag(v___x_6850_) == 0)
{
lean_object* v_a_6854_; 
lean_dec_ref(v___x_6848_);
v_a_6854_ = lean_ctor_get(v___x_6850_, 0);
lean_inc(v_a_6854_);
lean_dec_ref_known(v___x_6850_, 1);
if (lean_obj_tag(v_a_6854_) == 0)
{
lean_object* v_a_6855_; lean_object* v___x_6857_; uint8_t v_isShared_6858_; uint8_t v_isSharedCheck_6862_; 
v_a_6855_ = lean_ctor_get(v_a_6854_, 0);
v_isSharedCheck_6862_ = !lean_is_exclusive(v_a_6854_);
if (v_isSharedCheck_6862_ == 0)
{
v___x_6857_ = v_a_6854_;
v_isShared_6858_ = v_isSharedCheck_6862_;
goto v_resetjp_6856_;
}
else
{
lean_inc(v_a_6855_);
lean_dec(v_a_6854_);
v___x_6857_ = lean_box(0);
v_isShared_6858_ = v_isSharedCheck_6862_;
goto v_resetjp_6856_;
}
v_resetjp_6856_:
{
lean_object* v___x_6860_; 
if (v_isShared_6858_ == 0)
{
v___x_6860_ = v___x_6857_;
goto v_reusejp_6859_;
}
else
{
lean_object* v_reuseFailAlloc_6861_; 
v_reuseFailAlloc_6861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6861_, 0, v_a_6855_);
v___x_6860_ = v_reuseFailAlloc_6861_;
goto v_reusejp_6859_;
}
v_reusejp_6859_:
{
v___y_6852_ = v___x_6860_;
goto v___jp_6851_;
}
}
}
else
{
lean_object* v_a_6863_; lean_object* v___x_6865_; uint8_t v_isShared_6866_; uint8_t v_isSharedCheck_6871_; 
v_a_6863_ = lean_ctor_get(v_a_6854_, 0);
v_isSharedCheck_6871_ = !lean_is_exclusive(v_a_6854_);
if (v_isSharedCheck_6871_ == 0)
{
v___x_6865_ = v_a_6854_;
v_isShared_6866_ = v_isSharedCheck_6871_;
goto v_resetjp_6864_;
}
else
{
lean_inc(v_a_6863_);
lean_dec(v_a_6854_);
v___x_6865_ = lean_box(0);
v_isShared_6866_ = v_isSharedCheck_6871_;
goto v_resetjp_6864_;
}
v_resetjp_6864_:
{
lean_object* v_fst_6867_; lean_object* v___x_6869_; 
v_fst_6867_ = lean_ctor_get(v_a_6863_, 0);
lean_inc(v_fst_6867_);
lean_dec(v_a_6863_);
if (v_isShared_6866_ == 0)
{
lean_ctor_set(v___x_6865_, 0, v_fst_6867_);
v___x_6869_ = v___x_6865_;
goto v_reusejp_6868_;
}
else
{
lean_object* v_reuseFailAlloc_6870_; 
v_reuseFailAlloc_6870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6870_, 0, v_fst_6867_);
v___x_6869_ = v_reuseFailAlloc_6870_;
goto v_reusejp_6868_;
}
v_reusejp_6868_:
{
v___y_6852_ = v___x_6869_;
goto v___jp_6851_;
}
}
}
}
else
{
lean_object* v_a_6872_; lean_object* v___x_6874_; uint8_t v_isShared_6875_; uint8_t v_isSharedCheck_6880_; 
v_a_6872_ = lean_ctor_get(v___x_6850_, 0);
v_isSharedCheck_6880_ = !lean_is_exclusive(v___x_6850_);
if (v_isSharedCheck_6880_ == 0)
{
v___x_6874_ = v___x_6850_;
v_isShared_6875_ = v_isSharedCheck_6880_;
goto v_resetjp_6873_;
}
else
{
lean_inc(v_a_6872_);
lean_dec(v___x_6850_);
v___x_6874_ = lean_box(0);
v_isShared_6875_ = v_isSharedCheck_6880_;
goto v_resetjp_6873_;
}
v_resetjp_6873_:
{
lean_object* v___x_6876_; lean_object* v___x_6878_; 
v___x_6876_ = lean_task_map(v___x_6848_, v_a_6872_, v___x_6849_, v___x_6812_);
if (v_isShared_6875_ == 0)
{
lean_ctor_set(v___x_6874_, 0, v___x_6876_);
v___x_6878_ = v___x_6874_;
goto v_reusejp_6877_;
}
else
{
lean_object* v_reuseFailAlloc_6879_; 
v_reuseFailAlloc_6879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6879_, 0, v___x_6876_);
v___x_6878_ = v_reuseFailAlloc_6879_;
goto v_reusejp_6877_;
}
v_reusejp_6877_:
{
return v___x_6878_;
}
}
}
v___jp_6851_:
{
lean_object* v___x_6853_; 
v___x_6853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6853_, 0, v___y_6852_);
return v___x_6853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__28___boxed(lean_object* v_inst_6881_, lean_object* v_maximumRecvSize_6882_, lean_object* v_socket_6883_, lean_object* v_lingeringTimeout_6884_, lean_object* v_serverContext_6885_, lean_object* v_a_6886_, lean_object* v___x_6887_, lean_object* v_h_6888_, lean_object* v_handler_6889_, lean_object* v___f_6890_, lean_object* v_responseBodyInstance_6891_, lean_object* v___f_6892_, lean_object* v_x_6893_, lean_object* v___y_6894_){
_start:
{
uint8_t v___x_10240__boxed_6895_; lean_object* v_res_6896_; 
v___x_10240__boxed_6895_ = lean_unbox(v___x_6887_);
v_res_6896_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__28(v_inst_6881_, v_maximumRecvSize_6882_, v_socket_6883_, v_lingeringTimeout_6884_, v_serverContext_6885_, v_a_6886_, v___x_10240__boxed_6895_, v_h_6888_, v_handler_6889_, v___f_6890_, v_responseBodyInstance_6891_, v___f_6892_, v_x_6893_);
return v_res_6896_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__29(lean_object* v_a_6897_, lean_object* v_x_6898_){
_start:
{
if (lean_obj_tag(v_x_6898_) == 0)
{
lean_object* v_a_6900_; lean_object* v___x_6902_; uint8_t v_isShared_6903_; uint8_t v_isSharedCheck_6908_; 
v_a_6900_ = lean_ctor_get(v_x_6898_, 0);
v_isSharedCheck_6908_ = !lean_is_exclusive(v_x_6898_);
if (v_isSharedCheck_6908_ == 0)
{
v___x_6902_ = v_x_6898_;
v_isShared_6903_ = v_isSharedCheck_6908_;
goto v_resetjp_6901_;
}
else
{
lean_inc(v_a_6900_);
lean_dec(v_x_6898_);
v___x_6902_ = lean_box(0);
v_isShared_6903_ = v_isSharedCheck_6908_;
goto v_resetjp_6901_;
}
v_resetjp_6901_:
{
lean_object* v___x_6905_; 
if (v_isShared_6903_ == 0)
{
v___x_6905_ = v___x_6902_;
goto v_reusejp_6904_;
}
else
{
lean_object* v_reuseFailAlloc_6907_; 
v_reuseFailAlloc_6907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6907_, 0, v_a_6900_);
v___x_6905_ = v_reuseFailAlloc_6907_;
goto v_reusejp_6904_;
}
v_reusejp_6904_:
{
lean_object* v___x_6906_; 
v___x_6906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6906_, 0, v___x_6905_);
return v___x_6906_;
}
}
}
else
{
lean_object* v___x_6909_; lean_object* v___x_6910_; 
lean_dec_ref_known(v_x_6898_, 1);
v___x_6909_ = l_IO_Promise_result_x21___redArg(v_a_6897_);
v___x_6910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6910_, 0, v___x_6909_);
return v___x_6910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__29___boxed(lean_object* v_a_6911_, lean_object* v_x_6912_, lean_object* v___y_6913_){
_start:
{
lean_object* v_res_6914_; 
v_res_6914_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__29(v_a_6911_, v_x_6912_);
lean_dec(v_a_6911_);
return v_res_6914_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__30(lean_object* v___f_6915_, lean_object* v___x_6916_, lean_object* v___x_6917_, uint8_t v___x_6918_, lean_object* v_x_6919_){
_start:
{
if (lean_obj_tag(v_x_6919_) == 0)
{
lean_object* v_a_6921_; lean_object* v___x_6923_; uint8_t v_isShared_6924_; uint8_t v_isSharedCheck_6929_; 
lean_dec_ref(v___x_6917_);
lean_dec(v___x_6916_);
lean_dec_ref(v___f_6915_);
v_a_6921_ = lean_ctor_get(v_x_6919_, 0);
v_isSharedCheck_6929_ = !lean_is_exclusive(v_x_6919_);
if (v_isSharedCheck_6929_ == 0)
{
v___x_6923_ = v_x_6919_;
v_isShared_6924_ = v_isSharedCheck_6929_;
goto v_resetjp_6922_;
}
else
{
lean_inc(v_a_6921_);
lean_dec(v_x_6919_);
v___x_6923_ = lean_box(0);
v_isShared_6924_ = v_isSharedCheck_6929_;
goto v_resetjp_6922_;
}
v_resetjp_6922_:
{
lean_object* v___x_6926_; 
if (v_isShared_6924_ == 0)
{
v___x_6926_ = v___x_6923_;
goto v_reusejp_6925_;
}
else
{
lean_object* v_reuseFailAlloc_6928_; 
v_reuseFailAlloc_6928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6928_, 0, v_a_6921_);
v___x_6926_ = v_reuseFailAlloc_6928_;
goto v_reusejp_6925_;
}
v_reusejp_6925_:
{
lean_object* v___x_6927_; 
v___x_6927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6927_, 0, v___x_6926_);
return v___x_6927_;
}
}
}
else
{
lean_object* v_a_6930_; lean_object* v___x_6932_; uint8_t v_isShared_6933_; uint8_t v_isSharedCheck_6941_; 
v_a_6930_ = lean_ctor_get(v_x_6919_, 0);
v_isSharedCheck_6941_ = !lean_is_exclusive(v_x_6919_);
if (v_isSharedCheck_6941_ == 0)
{
v___x_6932_ = v_x_6919_;
v_isShared_6933_ = v_isSharedCheck_6941_;
goto v_resetjp_6931_;
}
else
{
lean_inc(v_a_6930_);
lean_dec(v_x_6919_);
v___x_6932_ = lean_box(0);
v_isShared_6933_ = v_isSharedCheck_6941_;
goto v_resetjp_6931_;
}
v_resetjp_6931_:
{
lean_object* v___f_6934_; lean_object* v___x_6935_; lean_object* v___x_6937_; 
lean_inc(v_a_6930_);
v___f_6934_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__29___boxed), 3, 1);
lean_closure_set(v___f_6934_, 0, v_a_6930_);
lean_inc(v___x_6916_);
v___x_6935_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(lean_box(0), lean_box(0), v___f_6915_, v___x_6916_, v_a_6930_, v___x_6917_);
if (v_isShared_6933_ == 0)
{
lean_ctor_set(v___x_6932_, 0, v___x_6935_);
v___x_6937_ = v___x_6932_;
goto v_reusejp_6936_;
}
else
{
lean_object* v_reuseFailAlloc_6940_; 
v_reuseFailAlloc_6940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6940_, 0, v___x_6935_);
v___x_6937_ = v_reuseFailAlloc_6940_;
goto v_reusejp_6936_;
}
v_reusejp_6936_:
{
lean_object* v___x_6938_; lean_object* v___x_6939_; 
v___x_6938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6938_, 0, v___x_6937_);
v___x_6939_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6916_, v___x_6918_, v___x_6938_, v___f_6934_);
return v___x_6939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__30___boxed(lean_object* v___f_6942_, lean_object* v___x_6943_, lean_object* v___x_6944_, lean_object* v___x_6945_, lean_object* v_x_6946_, lean_object* v___y_6947_){
_start:
{
uint8_t v___x_10413__boxed_6948_; lean_object* v_res_6949_; 
v___x_10413__boxed_6948_ = lean_unbox(v___x_6945_);
v_res_6949_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__30(v___f_6942_, v___x_6943_, v___x_6944_, v___x_10413__boxed_6948_, v_x_6946_);
return v_res_6949_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__31(lean_object* v_h_6950_, lean_object* v_handler_6951_, lean_object* v___x_6952_, lean_object* v_responseBodyInstance_6953_, lean_object* v_config_6954_, uint8_t v___x_6955_, lean_object* v___f_6956_, lean_object* v_wd_6957_, lean_object* v_connectionContext_6958_, lean_object* v_inst_6959_, lean_object* v_socket_6960_, lean_object* v_maximumRecvSize_6961_, lean_object* v_extensions_6962_, lean_object* v___f_6963_, lean_object* v_lingeringTimeout_6964_, lean_object* v_serverContext_6965_, lean_object* v___f_6966_, lean_object* v___f_6967_, lean_object* v___x_6968_, lean_object* v_x_6969_){
_start:
{
if (lean_obj_tag(v_x_6969_) == 0)
{
lean_object* v_a_6971_; lean_object* v___x_6973_; uint8_t v_isShared_6974_; uint8_t v_isSharedCheck_6979_; 
lean_dec_ref(v___x_6968_);
lean_dec_ref(v___f_6967_);
lean_dec_ref(v___f_6966_);
lean_dec_ref(v_serverContext_6965_);
lean_dec(v_lingeringTimeout_6964_);
lean_dec_ref(v___f_6963_);
lean_dec(v_extensions_6962_);
lean_dec(v_maximumRecvSize_6961_);
lean_dec(v_socket_6960_);
lean_dec_ref(v_inst_6959_);
lean_dec_ref(v_connectionContext_6958_);
lean_dec_ref(v_wd_6957_);
lean_dec_ref(v___f_6956_);
lean_dec_ref(v_config_6954_);
lean_dec_ref(v_responseBodyInstance_6953_);
lean_dec(v___x_6952_);
lean_dec(v_handler_6951_);
lean_dec_ref(v_h_6950_);
v_a_6971_ = lean_ctor_get(v_x_6969_, 0);
v_isSharedCheck_6979_ = !lean_is_exclusive(v_x_6969_);
if (v_isSharedCheck_6979_ == 0)
{
v___x_6973_ = v_x_6969_;
v_isShared_6974_ = v_isSharedCheck_6979_;
goto v_resetjp_6972_;
}
else
{
lean_inc(v_a_6971_);
lean_dec(v_x_6969_);
v___x_6973_ = lean_box(0);
v_isShared_6974_ = v_isSharedCheck_6979_;
goto v_resetjp_6972_;
}
v_resetjp_6972_:
{
lean_object* v___x_6976_; 
if (v_isShared_6974_ == 0)
{
v___x_6976_ = v___x_6973_;
goto v_reusejp_6975_;
}
else
{
lean_object* v_reuseFailAlloc_6978_; 
v_reuseFailAlloc_6978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6978_, 0, v_a_6971_);
v___x_6976_ = v_reuseFailAlloc_6978_;
goto v_reusejp_6975_;
}
v_reusejp_6975_:
{
lean_object* v___x_6977_; 
v___x_6977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6977_, 0, v___x_6976_);
return v___x_6977_;
}
}
}
else
{
lean_object* v_a_6980_; lean_object* v___x_6982_; uint8_t v_isShared_6983_; uint8_t v_isSharedCheck_6998_; 
v_a_6980_ = lean_ctor_get(v_x_6969_, 0);
v_isSharedCheck_6998_ = !lean_is_exclusive(v_x_6969_);
if (v_isSharedCheck_6998_ == 0)
{
v___x_6982_ = v_x_6969_;
v_isShared_6983_ = v_isSharedCheck_6998_;
goto v_resetjp_6981_;
}
else
{
lean_inc(v_a_6980_);
lean_dec(v_x_6969_);
v___x_6982_ = lean_box(0);
v_isShared_6983_ = v_isSharedCheck_6998_;
goto v_resetjp_6981_;
}
v_resetjp_6981_:
{
lean_object* v___x_6984_; lean_object* v___f_6985_; lean_object* v___x_6986_; lean_object* v___f_6987_; lean_object* v___x_6988_; lean_object* v___x_6989_; lean_object* v___f_6990_; lean_object* v___x_6991_; lean_object* v___x_6993_; 
v___x_6984_ = lean_box(v___x_6955_);
lean_inc(v_maximumRecvSize_6961_);
lean_inc(v_socket_6960_);
lean_inc_ref(v_inst_6959_);
lean_inc_ref(v_responseBodyInstance_6953_);
lean_inc(v_a_6980_);
lean_inc(v_handler_6951_);
lean_inc_ref(v_h_6950_);
v___f_6985_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__18___boxed), 18, 15);
lean_closure_set(v___f_6985_, 0, v_h_6950_);
lean_closure_set(v___f_6985_, 1, v_handler_6951_);
lean_closure_set(v___f_6985_, 2, v_a_6980_);
lean_closure_set(v___f_6985_, 3, v___x_6952_);
lean_closure_set(v___f_6985_, 4, v_responseBodyInstance_6953_);
lean_closure_set(v___f_6985_, 5, v_config_6954_);
lean_closure_set(v___f_6985_, 6, v___x_6984_);
lean_closure_set(v___f_6985_, 7, v___f_6956_);
lean_closure_set(v___f_6985_, 8, v_wd_6957_);
lean_closure_set(v___f_6985_, 9, v_connectionContext_6958_);
lean_closure_set(v___f_6985_, 10, v_inst_6959_);
lean_closure_set(v___f_6985_, 11, v_socket_6960_);
lean_closure_set(v___f_6985_, 12, v_maximumRecvSize_6961_);
lean_closure_set(v___f_6985_, 13, v_extensions_6962_);
lean_closure_set(v___f_6985_, 14, v___f_6963_);
v___x_6986_ = lean_box(v___x_6955_);
v___f_6987_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__28___boxed), 14, 12);
lean_closure_set(v___f_6987_, 0, v_inst_6959_);
lean_closure_set(v___f_6987_, 1, v_maximumRecvSize_6961_);
lean_closure_set(v___f_6987_, 2, v_socket_6960_);
lean_closure_set(v___f_6987_, 3, v_lingeringTimeout_6964_);
lean_closure_set(v___f_6987_, 4, v_serverContext_6965_);
lean_closure_set(v___f_6987_, 5, v_a_6980_);
lean_closure_set(v___f_6987_, 6, v___x_6986_);
lean_closure_set(v___f_6987_, 7, v_h_6950_);
lean_closure_set(v___f_6987_, 8, v_handler_6951_);
lean_closure_set(v___f_6987_, 9, v___f_6966_);
lean_closure_set(v___f_6987_, 10, v_responseBodyInstance_6953_);
lean_closure_set(v___f_6987_, 11, v___f_6967_);
v___x_6988_ = lean_unsigned_to_nat(0u);
v___x_6989_ = lean_box(v___x_6955_);
v___f_6990_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__30___boxed), 6, 4);
lean_closure_set(v___f_6990_, 0, v___f_6985_);
lean_closure_set(v___f_6990_, 1, v___x_6988_);
lean_closure_set(v___f_6990_, 2, v___x_6968_);
lean_closure_set(v___f_6990_, 3, v___x_6989_);
v___x_6991_ = lean_io_promise_new();
if (v_isShared_6983_ == 0)
{
lean_ctor_set(v___x_6982_, 0, v___x_6991_);
v___x_6993_ = v___x_6982_;
goto v_reusejp_6992_;
}
else
{
lean_object* v_reuseFailAlloc_6997_; 
v_reuseFailAlloc_6997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6997_, 0, v___x_6991_);
v___x_6993_ = v_reuseFailAlloc_6997_;
goto v_reusejp_6992_;
}
v_reusejp_6992_:
{
lean_object* v___x_6994_; lean_object* v___x_6995_; lean_object* v___x_6996_; 
v___x_6994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6994_, 0, v___x_6993_);
v___x_6995_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6988_, v___x_6955_, v___x_6994_, v___f_6990_);
v___x_6996_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_6988_, v___x_6955_, v___x_6995_, v___f_6987_);
return v___x_6996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_h_6999_ = _args[0];
lean_object* v_handler_7000_ = _args[1];
lean_object* v___x_7001_ = _args[2];
lean_object* v_responseBodyInstance_7002_ = _args[3];
lean_object* v_config_7003_ = _args[4];
lean_object* v___x_7004_ = _args[5];
lean_object* v___f_7005_ = _args[6];
lean_object* v_wd_7006_ = _args[7];
lean_object* v_connectionContext_7007_ = _args[8];
lean_object* v_inst_7008_ = _args[9];
lean_object* v_socket_7009_ = _args[10];
lean_object* v_maximumRecvSize_7010_ = _args[11];
lean_object* v_extensions_7011_ = _args[12];
lean_object* v___f_7012_ = _args[13];
lean_object* v_lingeringTimeout_7013_ = _args[14];
lean_object* v_serverContext_7014_ = _args[15];
lean_object* v___f_7015_ = _args[16];
lean_object* v___f_7016_ = _args[17];
lean_object* v___x_7017_ = _args[18];
lean_object* v_x_7018_ = _args[19];
lean_object* v___y_7019_ = _args[20];
_start:
{
uint8_t v___x_10471__boxed_7020_; lean_object* v_res_7021_; 
v___x_10471__boxed_7020_ = lean_unbox(v___x_7004_);
v_res_7021_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__31(v_h_6999_, v_handler_7000_, v___x_7001_, v_responseBodyInstance_7002_, v_config_7003_, v___x_10471__boxed_7020_, v___f_7005_, v_wd_7006_, v_connectionContext_7007_, v_inst_7008_, v_socket_7009_, v_maximumRecvSize_7010_, v_extensions_7011_, v___f_7012_, v_lingeringTimeout_7013_, v_serverContext_7014_, v___f_7015_, v___f_7016_, v___x_7017_, v_x_7018_);
return v_res_7021_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__32(lean_object* v_config_7022_, lean_object* v_machine_7023_, lean_object* v_a_7024_, lean_object* v_h_7025_, lean_object* v_handler_7026_, lean_object* v_responseBodyInstance_7027_, lean_object* v___f_7028_, lean_object* v_wd_7029_, lean_object* v_connectionContext_7030_, lean_object* v_inst_7031_, lean_object* v_socket_7032_, lean_object* v_extensions_7033_, lean_object* v___f_7034_, lean_object* v_serverContext_7035_, lean_object* v___f_7036_, lean_object* v___f_7037_, lean_object* v_x_7038_){
_start:
{
if (lean_obj_tag(v_x_7038_) == 0)
{
lean_object* v_a_7040_; lean_object* v___x_7042_; uint8_t v_isShared_7043_; uint8_t v_isSharedCheck_7048_; 
lean_dec_ref(v___f_7037_);
lean_dec_ref(v___f_7036_);
lean_dec_ref(v_serverContext_7035_);
lean_dec_ref(v___f_7034_);
lean_dec(v_extensions_7033_);
lean_dec(v_socket_7032_);
lean_dec_ref(v_inst_7031_);
lean_dec_ref(v_connectionContext_7030_);
lean_dec_ref(v_wd_7029_);
lean_dec_ref(v___f_7028_);
lean_dec_ref(v_responseBodyInstance_7027_);
lean_dec(v_handler_7026_);
lean_dec_ref(v_h_7025_);
lean_dec_ref(v_a_7024_);
lean_dec_ref(v_machine_7023_);
lean_dec_ref(v_config_7022_);
v_a_7040_ = lean_ctor_get(v_x_7038_, 0);
v_isSharedCheck_7048_ = !lean_is_exclusive(v_x_7038_);
if (v_isSharedCheck_7048_ == 0)
{
v___x_7042_ = v_x_7038_;
v_isShared_7043_ = v_isSharedCheck_7048_;
goto v_resetjp_7041_;
}
else
{
lean_inc(v_a_7040_);
lean_dec(v_x_7038_);
v___x_7042_ = lean_box(0);
v_isShared_7043_ = v_isSharedCheck_7048_;
goto v_resetjp_7041_;
}
v_resetjp_7041_:
{
lean_object* v___x_7045_; 
if (v_isShared_7043_ == 0)
{
v___x_7045_ = v___x_7042_;
goto v_reusejp_7044_;
}
else
{
lean_object* v_reuseFailAlloc_7047_; 
v_reuseFailAlloc_7047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7047_, 0, v_a_7040_);
v___x_7045_ = v_reuseFailAlloc_7047_;
goto v_reusejp_7044_;
}
v_reusejp_7044_:
{
lean_object* v___x_7046_; 
v___x_7046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7046_, 0, v___x_7045_);
return v___x_7046_;
}
}
}
else
{
lean_object* v_a_7049_; lean_object* v___x_7051_; uint8_t v_isShared_7052_; uint8_t v_isSharedCheck_7072_; 
v_a_7049_ = lean_ctor_get(v_x_7038_, 0);
v_isSharedCheck_7072_ = !lean_is_exclusive(v_x_7038_);
if (v_isSharedCheck_7072_ == 0)
{
v___x_7051_ = v_x_7038_;
v_isShared_7052_ = v_isSharedCheck_7072_;
goto v_resetjp_7050_;
}
else
{
lean_inc(v_a_7049_);
lean_dec(v_x_7038_);
v___x_7051_ = lean_box(0);
v_isShared_7052_ = v_isSharedCheck_7072_;
goto v_resetjp_7050_;
}
v_resetjp_7050_:
{
lean_object* v_lingeringTimeout_7053_; lean_object* v_writeTimeout_7054_; lean_object* v_maximumRecvSize_7055_; lean_object* v___x_7056_; lean_object* v___x_7057_; lean_object* v___x_7058_; uint8_t v___x_7059_; uint8_t v___x_7060_; lean_object* v___x_7061_; lean_object* v___x_7062_; lean_object* v___f_7063_; lean_object* v___x_7064_; lean_object* v___x_7065_; lean_object* v___x_7066_; lean_object* v___x_7068_; 
v_lingeringTimeout_7053_ = lean_ctor_get(v_config_7022_, 4);
lean_inc(v_lingeringTimeout_7053_);
v_writeTimeout_7054_ = lean_ctor_get(v_config_7022_, 7);
lean_inc(v_writeTimeout_7054_);
v_maximumRecvSize_7055_ = lean_ctor_get(v_config_7022_, 8);
lean_inc(v_maximumRecvSize_7055_);
v___x_7056_ = lean_box(0);
v___x_7057_ = lean_box(0);
v___x_7058_ = lean_box(0);
v___x_7059_ = 1;
v___x_7060_ = 0;
v___x_7061_ = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(v___x_7061_, 0, v_machine_7023_);
lean_ctor_set(v___x_7061_, 1, v_a_7024_);
lean_ctor_set(v___x_7061_, 2, v___x_7056_);
lean_ctor_set(v___x_7061_, 3, v_a_7049_);
lean_ctor_set(v___x_7061_, 4, v___x_7057_);
lean_ctor_set(v___x_7061_, 5, v___x_7057_);
lean_ctor_set(v___x_7061_, 6, v___x_7058_);
lean_ctor_set(v___x_7061_, 7, v___x_7057_);
lean_ctor_set(v___x_7061_, 8, v___x_7057_);
lean_ctor_set_uint8(v___x_7061_, sizeof(void*)*9, v___x_7059_);
lean_ctor_set_uint8(v___x_7061_, sizeof(void*)*9 + 1, v___x_7060_);
v___x_7062_ = lean_box(v___x_7060_);
lean_inc(v_socket_7032_);
v___f_7063_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__31___boxed), 21, 19);
lean_closure_set(v___f_7063_, 0, v_h_7025_);
lean_closure_set(v___f_7063_, 1, v_handler_7026_);
lean_closure_set(v___f_7063_, 2, v___x_7057_);
lean_closure_set(v___f_7063_, 3, v_responseBodyInstance_7027_);
lean_closure_set(v___f_7063_, 4, v_config_7022_);
lean_closure_set(v___f_7063_, 5, v___x_7062_);
lean_closure_set(v___f_7063_, 6, v___f_7028_);
lean_closure_set(v___f_7063_, 7, v_wd_7029_);
lean_closure_set(v___f_7063_, 8, v_connectionContext_7030_);
lean_closure_set(v___f_7063_, 9, v_inst_7031_);
lean_closure_set(v___f_7063_, 10, v_socket_7032_);
lean_closure_set(v___f_7063_, 11, v_maximumRecvSize_7055_);
lean_closure_set(v___f_7063_, 12, v_extensions_7033_);
lean_closure_set(v___f_7063_, 13, v___f_7034_);
lean_closure_set(v___f_7063_, 14, v_lingeringTimeout_7053_);
lean_closure_set(v___f_7063_, 15, v_serverContext_7035_);
lean_closure_set(v___f_7063_, 16, v___f_7036_);
lean_closure_set(v___f_7063_, 17, v___f_7037_);
lean_closure_set(v___f_7063_, 18, v___x_7061_);
v___x_7064_ = l_Int_toNat(v_writeTimeout_7054_);
lean_dec(v_writeTimeout_7054_);
v___x_7065_ = lean_unsigned_to_nat(0u);
v___x_7066_ = l_Std_Http_Internal_Outbox_new___redArg(v_socket_7032_, v___x_7064_);
if (v_isShared_7052_ == 0)
{
lean_ctor_set(v___x_7051_, 0, v___x_7066_);
v___x_7068_ = v___x_7051_;
goto v_reusejp_7067_;
}
else
{
lean_object* v_reuseFailAlloc_7071_; 
v_reuseFailAlloc_7071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7071_, 0, v___x_7066_);
v___x_7068_ = v_reuseFailAlloc_7071_;
goto v_reusejp_7067_;
}
v_reusejp_7067_:
{
lean_object* v___x_7069_; lean_object* v___x_7070_; 
v___x_7069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7069_, 0, v___x_7068_);
v___x_7070_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_7065_, v___x_7060_, v___x_7069_, v___f_7063_);
return v___x_7070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__32___boxed(lean_object** _args){
lean_object* v_config_7073_ = _args[0];
lean_object* v_machine_7074_ = _args[1];
lean_object* v_a_7075_ = _args[2];
lean_object* v_h_7076_ = _args[3];
lean_object* v_handler_7077_ = _args[4];
lean_object* v_responseBodyInstance_7078_ = _args[5];
lean_object* v___f_7079_ = _args[6];
lean_object* v_wd_7080_ = _args[7];
lean_object* v_connectionContext_7081_ = _args[8];
lean_object* v_inst_7082_ = _args[9];
lean_object* v_socket_7083_ = _args[10];
lean_object* v_extensions_7084_ = _args[11];
lean_object* v___f_7085_ = _args[12];
lean_object* v_serverContext_7086_ = _args[13];
lean_object* v___f_7087_ = _args[14];
lean_object* v___f_7088_ = _args[15];
lean_object* v_x_7089_ = _args[16];
lean_object* v___y_7090_ = _args[17];
_start:
{
lean_object* v_res_7091_; 
v_res_7091_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__32(v_config_7073_, v_machine_7074_, v_a_7075_, v_h_7076_, v_handler_7077_, v_responseBodyInstance_7078_, v___f_7079_, v_wd_7080_, v_connectionContext_7081_, v_inst_7082_, v_socket_7083_, v_extensions_7084_, v___f_7085_, v_serverContext_7086_, v___f_7087_, v___f_7088_, v_x_7089_);
return v_res_7091_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__33(lean_object* v_config_7092_, lean_object* v_machine_7093_, lean_object* v_h_7094_, lean_object* v_handler_7095_, lean_object* v_responseBodyInstance_7096_, lean_object* v___f_7097_, lean_object* v_wd_7098_, lean_object* v_connectionContext_7099_, lean_object* v_inst_7100_, lean_object* v_socket_7101_, lean_object* v_extensions_7102_, lean_object* v___f_7103_, lean_object* v_serverContext_7104_, lean_object* v___f_7105_, lean_object* v___f_7106_, lean_object* v_x_7107_){
_start:
{
if (lean_obj_tag(v_x_7107_) == 0)
{
lean_object* v_a_7109_; lean_object* v___x_7111_; uint8_t v_isShared_7112_; uint8_t v_isSharedCheck_7117_; 
lean_dec_ref(v___f_7106_);
lean_dec_ref(v___f_7105_);
lean_dec_ref(v_serverContext_7104_);
lean_dec_ref(v___f_7103_);
lean_dec(v_extensions_7102_);
lean_dec(v_socket_7101_);
lean_dec_ref(v_inst_7100_);
lean_dec_ref(v_connectionContext_7099_);
lean_dec_ref(v_wd_7098_);
lean_dec_ref(v___f_7097_);
lean_dec_ref(v_responseBodyInstance_7096_);
lean_dec(v_handler_7095_);
lean_dec_ref(v_h_7094_);
lean_dec_ref(v_machine_7093_);
lean_dec_ref(v_config_7092_);
v_a_7109_ = lean_ctor_get(v_x_7107_, 0);
v_isSharedCheck_7117_ = !lean_is_exclusive(v_x_7107_);
if (v_isSharedCheck_7117_ == 0)
{
v___x_7111_ = v_x_7107_;
v_isShared_7112_ = v_isSharedCheck_7117_;
goto v_resetjp_7110_;
}
else
{
lean_inc(v_a_7109_);
lean_dec(v_x_7107_);
v___x_7111_ = lean_box(0);
v_isShared_7112_ = v_isSharedCheck_7117_;
goto v_resetjp_7110_;
}
v_resetjp_7110_:
{
lean_object* v___x_7114_; 
if (v_isShared_7112_ == 0)
{
v___x_7114_ = v___x_7111_;
goto v_reusejp_7113_;
}
else
{
lean_object* v_reuseFailAlloc_7116_; 
v_reuseFailAlloc_7116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7116_, 0, v_a_7109_);
v___x_7114_ = v_reuseFailAlloc_7116_;
goto v_reusejp_7113_;
}
v_reusejp_7113_:
{
lean_object* v___x_7115_; 
v___x_7115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7115_, 0, v___x_7114_);
return v___x_7115_;
}
}
}
else
{
lean_object* v_a_7118_; lean_object* v___x_7120_; uint8_t v_isShared_7121_; uint8_t v_isSharedCheck_7132_; 
v_a_7118_ = lean_ctor_get(v_x_7107_, 0);
v_isSharedCheck_7132_ = !lean_is_exclusive(v_x_7107_);
if (v_isSharedCheck_7132_ == 0)
{
v___x_7120_ = v_x_7107_;
v_isShared_7121_ = v_isSharedCheck_7132_;
goto v_resetjp_7119_;
}
else
{
lean_inc(v_a_7118_);
lean_dec(v_x_7107_);
v___x_7120_ = lean_box(0);
v_isShared_7121_ = v_isSharedCheck_7132_;
goto v_resetjp_7119_;
}
v_resetjp_7119_:
{
lean_object* v___f_7122_; lean_object* v___x_7123_; lean_object* v___x_7124_; uint8_t v___x_7125_; lean_object* v___x_7126_; lean_object* v___x_7128_; 
v___f_7122_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__32___boxed), 18, 16);
lean_closure_set(v___f_7122_, 0, v_config_7092_);
lean_closure_set(v___f_7122_, 1, v_machine_7093_);
lean_closure_set(v___f_7122_, 2, v_a_7118_);
lean_closure_set(v___f_7122_, 3, v_h_7094_);
lean_closure_set(v___f_7122_, 4, v_handler_7095_);
lean_closure_set(v___f_7122_, 5, v_responseBodyInstance_7096_);
lean_closure_set(v___f_7122_, 6, v___f_7097_);
lean_closure_set(v___f_7122_, 7, v_wd_7098_);
lean_closure_set(v___f_7122_, 8, v_connectionContext_7099_);
lean_closure_set(v___f_7122_, 9, v_inst_7100_);
lean_closure_set(v___f_7122_, 10, v_socket_7101_);
lean_closure_set(v___f_7122_, 11, v_extensions_7102_);
lean_closure_set(v___f_7122_, 12, v___f_7103_);
lean_closure_set(v___f_7122_, 13, v_serverContext_7104_);
lean_closure_set(v___f_7122_, 14, v___f_7105_);
lean_closure_set(v___f_7122_, 15, v___f_7106_);
v___x_7123_ = lean_box(0);
v___x_7124_ = lean_unsigned_to_nat(0u);
v___x_7125_ = 0;
v___x_7126_ = l_Std_CloseableChannel_new___redArg(v___x_7123_);
if (v_isShared_7121_ == 0)
{
lean_ctor_set(v___x_7120_, 0, v___x_7126_);
v___x_7128_ = v___x_7120_;
goto v_reusejp_7127_;
}
else
{
lean_object* v_reuseFailAlloc_7131_; 
v_reuseFailAlloc_7131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7131_, 0, v___x_7126_);
v___x_7128_ = v_reuseFailAlloc_7131_;
goto v_reusejp_7127_;
}
v_reusejp_7127_:
{
lean_object* v___x_7129_; lean_object* v___x_7130_; 
v___x_7129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7129_, 0, v___x_7128_);
v___x_7130_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_7124_, v___x_7125_, v___x_7129_, v___f_7122_);
return v___x_7130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__33___boxed(lean_object** _args){
lean_object* v_config_7133_ = _args[0];
lean_object* v_machine_7134_ = _args[1];
lean_object* v_h_7135_ = _args[2];
lean_object* v_handler_7136_ = _args[3];
lean_object* v_responseBodyInstance_7137_ = _args[4];
lean_object* v___f_7138_ = _args[5];
lean_object* v_wd_7139_ = _args[6];
lean_object* v_connectionContext_7140_ = _args[7];
lean_object* v_inst_7141_ = _args[8];
lean_object* v_socket_7142_ = _args[9];
lean_object* v_extensions_7143_ = _args[10];
lean_object* v___f_7144_ = _args[11];
lean_object* v_serverContext_7145_ = _args[12];
lean_object* v___f_7146_ = _args[13];
lean_object* v___f_7147_ = _args[14];
lean_object* v_x_7148_ = _args[15];
lean_object* v___y_7149_ = _args[16];
_start:
{
lean_object* v_res_7150_; 
v_res_7150_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__33(v_config_7133_, v_machine_7134_, v_h_7135_, v_handler_7136_, v_responseBodyInstance_7137_, v___f_7138_, v_wd_7139_, v_connectionContext_7140_, v_inst_7141_, v_socket_7142_, v_extensions_7143_, v___f_7144_, v_serverContext_7145_, v___f_7146_, v___f_7147_, v_x_7148_);
return v_res_7150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg(lean_object* v_inst_7154_, lean_object* v_h_7155_, lean_object* v_connection_7156_, lean_object* v_config_7157_, lean_object* v_serverContext_7158_, lean_object* v_connectionContext_7159_, lean_object* v_wd_7160_, lean_object* v_handler_7161_){
_start:
{
lean_object* v_responseBodyInstance_7163_; lean_object* v_socket_7164_; lean_object* v_machine_7165_; lean_object* v_extensions_7166_; lean_object* v___f_7167_; lean_object* v___f_7168_; lean_object* v___f_7169_; lean_object* v___f_7170_; lean_object* v___f_7171_; lean_object* v___x_7172_; uint8_t v___x_7173_; lean_object* v___x_7174_; lean_object* v___x_7175_; 
v_responseBodyInstance_7163_ = lean_ctor_get(v_h_7155_, 0);
lean_inc_ref_n(v_responseBodyInstance_7163_, 2);
v_socket_7164_ = lean_ctor_get(v_connection_7156_, 0);
lean_inc(v_socket_7164_);
v_machine_7165_ = lean_ctor_get(v_connection_7156_, 1);
lean_inc_ref(v_machine_7165_);
v_extensions_7166_ = lean_ctor_get(v_connection_7156_, 2);
lean_inc(v_extensions_7166_);
lean_dec_ref(v_connection_7156_);
v___f_7167_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__0));
v___f_7168_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__1));
v___f_7169_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__2));
v___f_7170_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_7170_, 0, v_responseBodyInstance_7163_);
v___f_7171_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___lam__33___boxed), 17, 15);
lean_closure_set(v___f_7171_, 0, v_config_7157_);
lean_closure_set(v___f_7171_, 1, v_machine_7165_);
lean_closure_set(v___f_7171_, 2, v_h_7155_);
lean_closure_set(v___f_7171_, 3, v_handler_7161_);
lean_closure_set(v___f_7171_, 4, v_responseBodyInstance_7163_);
lean_closure_set(v___f_7171_, 5, v___f_7168_);
lean_closure_set(v___f_7171_, 6, v_wd_7160_);
lean_closure_set(v___f_7171_, 7, v_connectionContext_7159_);
lean_closure_set(v___f_7171_, 8, v_inst_7154_);
lean_closure_set(v___f_7171_, 9, v_socket_7164_);
lean_closure_set(v___f_7171_, 10, v_extensions_7166_);
lean_closure_set(v___f_7171_, 11, v___f_7167_);
lean_closure_set(v___f_7171_, 12, v_serverContext_7158_);
lean_closure_set(v___f_7171_, 13, v___f_7170_);
lean_closure_set(v___f_7171_, 14, v___f_7169_);
v___x_7172_ = lean_unsigned_to_nat(0u);
v___x_7173_ = 0;
v___x_7174_ = l_Std_Http_Body_mkStream();
v___x_7175_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_7172_, v___x_7173_, v___x_7174_, v___f_7171_);
return v___x_7175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___boxed(lean_object* v_inst_7176_, lean_object* v_h_7177_, lean_object* v_connection_7178_, lean_object* v_config_7179_, lean_object* v_serverContext_7180_, lean_object* v_connectionContext_7181_, lean_object* v_wd_7182_, lean_object* v_handler_7183_, lean_object* v_a_7184_){
_start:
{
lean_object* v_res_7185_; 
v_res_7185_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg(v_inst_7176_, v_h_7177_, v_connection_7178_, v_config_7179_, v_serverContext_7180_, v_connectionContext_7181_, v_wd_7182_, v_handler_7183_);
return v_res_7185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run(lean_object* v_00_u03b1_7186_, lean_object* v_00_u03c3_7187_, lean_object* v_inst_7188_, lean_object* v_h_7189_, lean_object* v_connection_7190_, lean_object* v_config_7191_, lean_object* v_serverContext_7192_, lean_object* v_connectionContext_7193_, lean_object* v_wd_7194_, lean_object* v_handler_7195_){
_start:
{
lean_object* v___x_7197_; 
v___x_7197_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg(v_inst_7188_, v_h_7189_, v_connection_7190_, v_config_7191_, v_serverContext_7192_, v_connectionContext_7193_, v_wd_7194_, v_handler_7195_);
return v___x_7197_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___boxed(lean_object* v_00_u03b1_7198_, lean_object* v_00_u03c3_7199_, lean_object* v_inst_7200_, lean_object* v_h_7201_, lean_object* v_connection_7202_, lean_object* v_config_7203_, lean_object* v_serverContext_7204_, lean_object* v_connectionContext_7205_, lean_object* v_wd_7206_, lean_object* v_handler_7207_, lean_object* v_a_7208_){
_start:
{
lean_object* v_res_7209_; 
v_res_7209_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run(v_00_u03b1_7198_, v_00_u03c3_7199_, v_inst_7200_, v_h_7201_, v_connection_7202_, v_config_7203_, v_serverContext_7204_, v_connectionContext_7205_, v_wd_7206_, v_handler_7207_);
return v_res_7209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(lean_object* v_a_7210_, lean_object* v___x_7211_, lean_object* v_x_7212_){
_start:
{
lean_object* v___x_7214_; lean_object* v___x_7215_; lean_object* v___x_7216_; 
v___x_7214_ = l_Std_CancellationContext_cancel(v_a_7210_, v___x_7211_);
v___x_7215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7215_, 0, v___x_7214_);
v___x_7216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7216_, 0, v___x_7215_);
return v___x_7216_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed(lean_object* v_a_7217_, lean_object* v___x_7218_, lean_object* v_x_7219_, lean_object* v___y_7220_){
_start:
{
lean_object* v_res_7221_; 
v_res_7221_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1(v_a_7217_, v___x_7218_, v_x_7219_);
lean_dec(v_x_7219_);
return v_res_7221_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(lean_object* v_inst_7222_, lean_object* v_inst_7223_, lean_object* v_connection_7224_, lean_object* v_config_7225_, lean_object* v_serverContext_7226_, lean_object* v_a_7227_, lean_object* v_handler_7228_, lean_object* v___f_7229_, lean_object* v_x_7230_){
_start:
{
if (lean_obj_tag(v_x_7230_) == 0)
{
lean_object* v_a_7232_; lean_object* v___x_7234_; uint8_t v_isShared_7235_; uint8_t v_isSharedCheck_7240_; 
lean_dec_ref(v___f_7229_);
lean_dec(v_handler_7228_);
lean_dec_ref(v_a_7227_);
lean_dec_ref(v_serverContext_7226_);
lean_dec_ref(v_config_7225_);
lean_dec_ref(v_connection_7224_);
lean_dec_ref(v_inst_7223_);
lean_dec_ref(v_inst_7222_);
v_a_7232_ = lean_ctor_get(v_x_7230_, 0);
v_isSharedCheck_7240_ = !lean_is_exclusive(v_x_7230_);
if (v_isSharedCheck_7240_ == 0)
{
v___x_7234_ = v_x_7230_;
v_isShared_7235_ = v_isSharedCheck_7240_;
goto v_resetjp_7233_;
}
else
{
lean_inc(v_a_7232_);
lean_dec(v_x_7230_);
v___x_7234_ = lean_box(0);
v_isShared_7235_ = v_isSharedCheck_7240_;
goto v_resetjp_7233_;
}
v_resetjp_7233_:
{
lean_object* v___x_7237_; 
if (v_isShared_7235_ == 0)
{
v___x_7237_ = v___x_7234_;
goto v_reusejp_7236_;
}
else
{
lean_object* v_reuseFailAlloc_7239_; 
v_reuseFailAlloc_7239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7239_, 0, v_a_7232_);
v___x_7237_ = v_reuseFailAlloc_7239_;
goto v_reusejp_7236_;
}
v_reusejp_7236_:
{
lean_object* v___x_7238_; 
v___x_7238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7238_, 0, v___x_7237_);
return v___x_7238_;
}
}
}
else
{
lean_object* v_a_7241_; lean_object* v___x_7242_; lean_object* v___x_7243_; lean_object* v___f_7244_; lean_object* v___x_7245_; lean_object* v___x_7246_; uint8_t v___x_7247_; lean_object* v___x_7248_; lean_object* v___y_7250_; 
v_a_7241_ = lean_ctor_get(v_x_7230_, 0);
lean_inc(v_a_7241_);
lean_dec_ref_known(v_x_7230_, 1);
lean_inc_ref(v_a_7227_);
v___x_7242_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___boxed), 11, 10);
lean_closure_set(v___x_7242_, 0, lean_box(0));
lean_closure_set(v___x_7242_, 1, lean_box(0));
lean_closure_set(v___x_7242_, 2, v_inst_7222_);
lean_closure_set(v___x_7242_, 3, v_inst_7223_);
lean_closure_set(v___x_7242_, 4, v_connection_7224_);
lean_closure_set(v___x_7242_, 5, v_config_7225_);
lean_closure_set(v___x_7242_, 6, v_serverContext_7226_);
lean_closure_set(v___x_7242_, 7, v_a_7227_);
lean_closure_set(v___x_7242_, 8, v_a_7241_);
lean_closure_set(v___x_7242_, 9, v_handler_7228_);
v___x_7243_ = lean_box(2);
v___f_7244_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_7244_, 0, v_a_7227_);
lean_closure_set(v___f_7244_, 1, v___x_7243_);
v___x_7245_ = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(v___x_7245_, 0, lean_box(0));
lean_closure_set(v___x_7245_, 1, lean_box(0));
lean_closure_set(v___x_7245_, 2, lean_box(0));
lean_closure_set(v___x_7245_, 3, v___f_7229_);
v___x_7246_ = lean_unsigned_to_nat(0u);
v___x_7247_ = 0;
v___x_7248_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___x_7242_, v___f_7244_, v___x_7246_, v___x_7247_);
if (lean_obj_tag(v___x_7248_) == 0)
{
lean_object* v_a_7252_; 
lean_dec_ref(v___x_7245_);
v_a_7252_ = lean_ctor_get(v___x_7248_, 0);
lean_inc(v_a_7252_);
lean_dec_ref_known(v___x_7248_, 1);
if (lean_obj_tag(v_a_7252_) == 0)
{
lean_object* v_a_7253_; lean_object* v___x_7255_; uint8_t v_isShared_7256_; uint8_t v_isSharedCheck_7260_; 
v_a_7253_ = lean_ctor_get(v_a_7252_, 0);
v_isSharedCheck_7260_ = !lean_is_exclusive(v_a_7252_);
if (v_isSharedCheck_7260_ == 0)
{
v___x_7255_ = v_a_7252_;
v_isShared_7256_ = v_isSharedCheck_7260_;
goto v_resetjp_7254_;
}
else
{
lean_inc(v_a_7253_);
lean_dec(v_a_7252_);
v___x_7255_ = lean_box(0);
v_isShared_7256_ = v_isSharedCheck_7260_;
goto v_resetjp_7254_;
}
v_resetjp_7254_:
{
lean_object* v___x_7258_; 
if (v_isShared_7256_ == 0)
{
v___x_7258_ = v___x_7255_;
goto v_reusejp_7257_;
}
else
{
lean_object* v_reuseFailAlloc_7259_; 
v_reuseFailAlloc_7259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7259_, 0, v_a_7253_);
v___x_7258_ = v_reuseFailAlloc_7259_;
goto v_reusejp_7257_;
}
v_reusejp_7257_:
{
v___y_7250_ = v___x_7258_;
goto v___jp_7249_;
}
}
}
else
{
lean_object* v_a_7261_; lean_object* v___x_7263_; uint8_t v_isShared_7264_; uint8_t v_isSharedCheck_7269_; 
v_a_7261_ = lean_ctor_get(v_a_7252_, 0);
v_isSharedCheck_7269_ = !lean_is_exclusive(v_a_7252_);
if (v_isSharedCheck_7269_ == 0)
{
v___x_7263_ = v_a_7252_;
v_isShared_7264_ = v_isSharedCheck_7269_;
goto v_resetjp_7262_;
}
else
{
lean_inc(v_a_7261_);
lean_dec(v_a_7252_);
v___x_7263_ = lean_box(0);
v_isShared_7264_ = v_isSharedCheck_7269_;
goto v_resetjp_7262_;
}
v_resetjp_7262_:
{
lean_object* v_fst_7265_; lean_object* v___x_7267_; 
v_fst_7265_ = lean_ctor_get(v_a_7261_, 0);
lean_inc(v_fst_7265_);
lean_dec(v_a_7261_);
if (v_isShared_7264_ == 0)
{
lean_ctor_set(v___x_7263_, 0, v_fst_7265_);
v___x_7267_ = v___x_7263_;
goto v_reusejp_7266_;
}
else
{
lean_object* v_reuseFailAlloc_7268_; 
v_reuseFailAlloc_7268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7268_, 0, v_fst_7265_);
v___x_7267_ = v_reuseFailAlloc_7268_;
goto v_reusejp_7266_;
}
v_reusejp_7266_:
{
v___y_7250_ = v___x_7267_;
goto v___jp_7249_;
}
}
}
}
else
{
lean_object* v_a_7270_; lean_object* v___x_7272_; uint8_t v_isShared_7273_; uint8_t v_isSharedCheck_7278_; 
v_a_7270_ = lean_ctor_get(v___x_7248_, 0);
v_isSharedCheck_7278_ = !lean_is_exclusive(v___x_7248_);
if (v_isSharedCheck_7278_ == 0)
{
v___x_7272_ = v___x_7248_;
v_isShared_7273_ = v_isSharedCheck_7278_;
goto v_resetjp_7271_;
}
else
{
lean_inc(v_a_7270_);
lean_dec(v___x_7248_);
v___x_7272_ = lean_box(0);
v_isShared_7273_ = v_isSharedCheck_7278_;
goto v_resetjp_7271_;
}
v_resetjp_7271_:
{
lean_object* v___x_7274_; lean_object* v___x_7276_; 
v___x_7274_ = lean_task_map(v___x_7245_, v_a_7270_, v___x_7246_, v___x_7247_);
if (v_isShared_7273_ == 0)
{
lean_ctor_set(v___x_7272_, 0, v___x_7274_);
v___x_7276_ = v___x_7272_;
goto v_reusejp_7275_;
}
else
{
lean_object* v_reuseFailAlloc_7277_; 
v_reuseFailAlloc_7277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7277_, 0, v___x_7274_);
v___x_7276_ = v_reuseFailAlloc_7277_;
goto v_reusejp_7275_;
}
v_reusejp_7275_:
{
return v___x_7276_;
}
}
}
v___jp_7249_:
{
lean_object* v___x_7251_; 
v___x_7251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7251_, 0, v___y_7250_);
return v___x_7251_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed(lean_object* v_inst_7279_, lean_object* v_inst_7280_, lean_object* v_connection_7281_, lean_object* v_config_7282_, lean_object* v_serverContext_7283_, lean_object* v_a_7284_, lean_object* v_handler_7285_, lean_object* v___f_7286_, lean_object* v_x_7287_, lean_object* v___y_7288_){
_start:
{
lean_object* v_res_7289_; 
v_res_7289_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0(v_inst_7279_, v_inst_7280_, v_connection_7281_, v_config_7282_, v_serverContext_7283_, v_a_7284_, v_handler_7285_, v___f_7286_, v_x_7287_);
return v_res_7289_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(lean_object* v_inst_7290_, lean_object* v_inst_7291_, lean_object* v_connection_7292_, lean_object* v_config_7293_, lean_object* v_serverContext_7294_, lean_object* v_handler_7295_, lean_object* v___f_7296_, lean_object* v_x_7297_){
_start:
{
if (lean_obj_tag(v_x_7297_) == 0)
{
lean_object* v_a_7299_; lean_object* v___x_7301_; uint8_t v_isShared_7302_; uint8_t v_isSharedCheck_7307_; 
lean_dec_ref(v___f_7296_);
lean_dec(v_handler_7295_);
lean_dec_ref(v_serverContext_7294_);
lean_dec_ref(v_config_7293_);
lean_dec_ref(v_connection_7292_);
lean_dec_ref(v_inst_7291_);
lean_dec_ref(v_inst_7290_);
v_a_7299_ = lean_ctor_get(v_x_7297_, 0);
v_isSharedCheck_7307_ = !lean_is_exclusive(v_x_7297_);
if (v_isSharedCheck_7307_ == 0)
{
v___x_7301_ = v_x_7297_;
v_isShared_7302_ = v_isSharedCheck_7307_;
goto v_resetjp_7300_;
}
else
{
lean_inc(v_a_7299_);
lean_dec(v_x_7297_);
v___x_7301_ = lean_box(0);
v_isShared_7302_ = v_isSharedCheck_7307_;
goto v_resetjp_7300_;
}
v_resetjp_7300_:
{
lean_object* v___x_7304_; 
if (v_isShared_7302_ == 0)
{
v___x_7304_ = v___x_7301_;
goto v_reusejp_7303_;
}
else
{
lean_object* v_reuseFailAlloc_7306_; 
v_reuseFailAlloc_7306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7306_, 0, v_a_7299_);
v___x_7304_ = v_reuseFailAlloc_7306_;
goto v_reusejp_7303_;
}
v_reusejp_7303_:
{
lean_object* v___x_7305_; 
v___x_7305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7305_, 0, v___x_7304_);
return v___x_7305_;
}
}
}
else
{
lean_object* v_a_7308_; lean_object* v___x_7310_; uint8_t v_isShared_7311_; uint8_t v_isSharedCheck_7328_; 
v_a_7308_ = lean_ctor_get(v_x_7297_, 0);
v_isSharedCheck_7328_ = !lean_is_exclusive(v_x_7297_);
if (v_isSharedCheck_7328_ == 0)
{
v___x_7310_ = v_x_7297_;
v_isShared_7311_ = v_isSharedCheck_7328_;
goto v_resetjp_7309_;
}
else
{
lean_inc(v_a_7308_);
lean_dec(v_x_7297_);
v___x_7310_ = lean_box(0);
v_isShared_7311_ = v_isSharedCheck_7328_;
goto v_resetjp_7309_;
}
v_resetjp_7309_:
{
lean_object* v___f_7312_; lean_object* v___x_7313_; uint8_t v___x_7314_; lean_object* v_val_7316_; lean_object* v___x_7319_; 
lean_inc(v_a_7308_);
v___f_7312_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__0___boxed), 10, 8);
lean_closure_set(v___f_7312_, 0, v_inst_7290_);
lean_closure_set(v___f_7312_, 1, v_inst_7291_);
lean_closure_set(v___f_7312_, 2, v_connection_7292_);
lean_closure_set(v___f_7312_, 3, v_config_7293_);
lean_closure_set(v___f_7312_, 4, v_serverContext_7294_);
lean_closure_set(v___f_7312_, 5, v_a_7308_);
lean_closure_set(v___f_7312_, 6, v_handler_7295_);
lean_closure_set(v___f_7312_, 7, v___f_7296_);
v___x_7313_ = lean_unsigned_to_nat(0u);
v___x_7314_ = 0;
v___x_7319_ = l_Std_Async_Watchdog_new(v_a_7308_);
if (lean_obj_tag(v___x_7319_) == 0)
{
lean_object* v_a_7320_; lean_object* v___x_7322_; 
v_a_7320_ = lean_ctor_get(v___x_7319_, 0);
lean_inc(v_a_7320_);
lean_dec_ref_known(v___x_7319_, 1);
if (v_isShared_7311_ == 0)
{
lean_ctor_set(v___x_7310_, 0, v_a_7320_);
v___x_7322_ = v___x_7310_;
goto v_reusejp_7321_;
}
else
{
lean_object* v_reuseFailAlloc_7323_; 
v_reuseFailAlloc_7323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7323_, 0, v_a_7320_);
v___x_7322_ = v_reuseFailAlloc_7323_;
goto v_reusejp_7321_;
}
v_reusejp_7321_:
{
v_val_7316_ = v___x_7322_;
goto v___jp_7315_;
}
}
else
{
lean_object* v_a_7324_; lean_object* v___x_7326_; 
v_a_7324_ = lean_ctor_get(v___x_7319_, 0);
lean_inc(v_a_7324_);
lean_dec_ref_known(v___x_7319_, 1);
if (v_isShared_7311_ == 0)
{
lean_ctor_set_tag(v___x_7310_, 0);
lean_ctor_set(v___x_7310_, 0, v_a_7324_);
v___x_7326_ = v___x_7310_;
goto v_reusejp_7325_;
}
else
{
lean_object* v_reuseFailAlloc_7327_; 
v_reuseFailAlloc_7327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7327_, 0, v_a_7324_);
v___x_7326_ = v_reuseFailAlloc_7327_;
goto v_reusejp_7325_;
}
v_reusejp_7325_:
{
v_val_7316_ = v___x_7326_;
goto v___jp_7315_;
}
}
v___jp_7315_:
{
lean_object* v___x_7317_; lean_object* v___x_7318_; 
v___x_7317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7317_, 0, v_val_7316_);
v___x_7318_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_7313_, v___x_7314_, v___x_7317_, v___f_7312_);
return v___x_7318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed(lean_object* v_inst_7329_, lean_object* v_inst_7330_, lean_object* v_connection_7331_, lean_object* v_config_7332_, lean_object* v_serverContext_7333_, lean_object* v_handler_7334_, lean_object* v___f_7335_, lean_object* v_x_7336_, lean_object* v___y_7337_){
_start:
{
lean_object* v_res_7338_; 
v_res_7338_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2(v_inst_7329_, v_inst_7330_, v_connection_7331_, v_config_7332_, v_serverContext_7333_, v_handler_7334_, v___f_7335_, v_x_7336_);
return v_res_7338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(lean_object* v_inst_7339_, lean_object* v_inst_7340_, lean_object* v_connection_7341_, lean_object* v_config_7342_, lean_object* v_serverContext_7343_, lean_object* v_handler_7344_){
_start:
{
lean_object* v___f_7346_; lean_object* v___f_7347_; lean_object* v___x_7348_; uint8_t v___x_7349_; lean_object* v___x_7350_; lean_object* v___x_7351_; lean_object* v___x_7352_; lean_object* v___x_7353_; 
v___f_7346_ = ((lean_object*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_run___redArg___closed__2));
lean_inc_ref(v_serverContext_7343_);
v___f_7347_ = lean_alloc_closure((void*)(l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___lam__2___boxed), 9, 7);
lean_closure_set(v___f_7347_, 0, v_inst_7339_);
lean_closure_set(v___f_7347_, 1, v_inst_7340_);
lean_closure_set(v___f_7347_, 2, v_connection_7341_);
lean_closure_set(v___f_7347_, 3, v_config_7342_);
lean_closure_set(v___f_7347_, 4, v_serverContext_7343_);
lean_closure_set(v___f_7347_, 5, v_handler_7344_);
lean_closure_set(v___f_7347_, 6, v___f_7346_);
v___x_7348_ = lean_unsigned_to_nat(0u);
v___x_7349_ = 0;
v___x_7350_ = l_Std_CancellationContext_fork(v_serverContext_7343_);
v___x_7351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7351_, 0, v___x_7350_);
v___x_7352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7352_, 0, v___x_7351_);
v___x_7353_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_7348_, v___x_7349_, v___x_7352_, v___f_7347_);
return v___x_7353_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg___boxed(lean_object* v_inst_7354_, lean_object* v_inst_7355_, lean_object* v_connection_7356_, lean_object* v_config_7357_, lean_object* v_serverContext_7358_, lean_object* v_handler_7359_, lean_object* v_a_7360_){
_start:
{
lean_object* v_res_7361_; 
v_res_7361_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_7354_, v_inst_7355_, v_connection_7356_, v_config_7357_, v_serverContext_7358_, v_handler_7359_);
return v_res_7361_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(lean_object* v_00_u03b1_7362_, lean_object* v_00_u03c3_7363_, lean_object* v_inst_7364_, lean_object* v_inst_7365_, lean_object* v_connection_7366_, lean_object* v_config_7367_, lean_object* v_serverContext_7368_, lean_object* v_handler_7369_){
_start:
{
lean_object* v___x_7371_; 
v___x_7371_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_7364_, v_inst_7365_, v_connection_7366_, v_config_7367_, v_serverContext_7368_, v_handler_7369_);
return v___x_7371_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___boxed(lean_object* v_00_u03b1_7372_, lean_object* v_00_u03c3_7373_, lean_object* v_inst_7374_, lean_object* v_inst_7375_, lean_object* v_connection_7376_, lean_object* v_config_7377_, lean_object* v_serverContext_7378_, lean_object* v_handler_7379_, lean_object* v_a_7380_){
_start:
{
lean_object* v_res_7381_; 
v_res_7381_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle(v_00_u03b1_7372_, v_00_u03c3_7373_, v_inst_7374_, v_inst_7375_, v_connection_7376_, v_config_7377_, v_serverContext_7378_, v_handler_7379_);
return v_res_7381_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0(void){
_start:
{
uint8_t v___x_7382_; lean_object* v___x_7383_; 
v___x_7382_ = 0;
v___x_7383_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_7382_);
return v___x_7383_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_7384_; lean_object* v___x_7385_; 
v___x_7384_ = lean_unsigned_to_nat(4096u);
v___x_7385_ = lean_mk_empty_byte_array(v___x_7384_);
return v___x_7385_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_7386_; lean_object* v___x_7387_; 
v___x_7386_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__1);
v___x_7387_ = l_ByteArray_mkIterator(v___x_7386_);
return v___x_7387_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3(void){
_start:
{
uint8_t v___x_7388_; lean_object* v___x_7389_; lean_object* v___x_7390_; lean_object* v___x_7391_; lean_object* v___x_7392_; lean_object* v___x_7393_; 
v___x_7388_ = 0;
v___x_7389_ = lean_unsigned_to_nat(0u);
v___x_7390_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__0);
v___x_7391_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__2);
v___x_7392_ = lean_box(0);
v___x_7393_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_7393_, 0, v___x_7392_);
lean_ctor_set(v___x_7393_, 1, v___x_7391_);
lean_ctor_set(v___x_7393_, 2, v___x_7390_);
lean_ctor_set(v___x_7393_, 3, v___x_7389_);
lean_ctor_set(v___x_7393_, 4, v___x_7389_);
lean_ctor_set(v___x_7393_, 5, v___x_7389_);
lean_ctor_set_uint8(v___x_7393_, sizeof(void*)*6, v___x_7388_);
lean_ctor_set_uint8(v___x_7393_, sizeof(void*)*6 + 1, v___x_7388_);
return v___x_7393_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7(void){
_start:
{
uint8_t v___x_7401_; lean_object* v___x_7402_; 
v___x_7401_ = 1;
v___x_7402_ = l_Std_Http_Protocol_H1_instEmptyCollectionHead(v___x_7401_);
return v___x_7402_;
}
}
static lean_object* _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_7403_; uint8_t v___x_7404_; lean_object* v___x_7405_; lean_object* v___x_7406_; lean_object* v___x_7407_; lean_object* v___x_7408_; lean_object* v___x_7409_; lean_object* v___x_7410_; 
v___x_7403_ = lean_unsigned_to_nat(0u);
v___x_7404_ = 0;
v___x_7405_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__7);
v___x_7406_ = lean_box(0);
v___x_7407_ = lean_box(0);
v___x_7408_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__6));
v___x_7409_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__4));
v___x_7410_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_7410_, 0, v___x_7409_);
lean_ctor_set(v___x_7410_, 1, v___x_7408_);
lean_ctor_set(v___x_7410_, 2, v___x_7407_);
lean_ctor_set(v___x_7410_, 3, v___x_7406_);
lean_ctor_set(v___x_7410_, 4, v___x_7405_);
lean_ctor_set(v___x_7410_, 5, v___x_7403_);
lean_ctor_set_uint8(v___x_7410_, sizeof(void*)*6, v___x_7404_);
lean_ctor_set_uint8(v___x_7410_, sizeof(void*)*6 + 1, v___x_7404_);
return v___x_7410_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0(lean_object* v_config_7411_, lean_object* v_client_7412_, lean_object* v_extensions_7413_, lean_object* v_inst_7414_, lean_object* v_inst_7415_, lean_object* v_handler_7416_, lean_object* v_x_7417_){
_start:
{
if (lean_obj_tag(v_x_7417_) == 0)
{
lean_object* v_a_7419_; lean_object* v___x_7421_; uint8_t v_isShared_7422_; uint8_t v_isSharedCheck_7427_; 
lean_dec(v_handler_7416_);
lean_dec_ref(v_inst_7415_);
lean_dec_ref(v_inst_7414_);
lean_dec(v_extensions_7413_);
lean_dec(v_client_7412_);
lean_dec_ref(v_config_7411_);
v_a_7419_ = lean_ctor_get(v_x_7417_, 0);
v_isSharedCheck_7427_ = !lean_is_exclusive(v_x_7417_);
if (v_isSharedCheck_7427_ == 0)
{
v___x_7421_ = v_x_7417_;
v_isShared_7422_ = v_isSharedCheck_7427_;
goto v_resetjp_7420_;
}
else
{
lean_inc(v_a_7419_);
lean_dec(v_x_7417_);
v___x_7421_ = lean_box(0);
v_isShared_7422_ = v_isSharedCheck_7427_;
goto v_resetjp_7420_;
}
v_resetjp_7420_:
{
lean_object* v___x_7424_; 
if (v_isShared_7422_ == 0)
{
v___x_7424_ = v___x_7421_;
goto v_reusejp_7423_;
}
else
{
lean_object* v_reuseFailAlloc_7426_; 
v_reuseFailAlloc_7426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7426_, 0, v_a_7419_);
v___x_7424_ = v_reuseFailAlloc_7426_;
goto v_reusejp_7423_;
}
v_reusejp_7423_:
{
lean_object* v___x_7425_; 
v___x_7425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7425_, 0, v___x_7424_);
return v___x_7425_;
}
}
}
else
{
lean_object* v_a_7428_; uint8_t v___x_7429_; lean_object* v___x_7430_; lean_object* v___x_7431_; lean_object* v___x_7432_; lean_object* v___x_7433_; lean_object* v___x_7434_; uint8_t v_enableKeepAlive_7435_; lean_object* v___x_7436_; lean_object* v___x_7437_; lean_object* v___x_7438_; 
v_a_7428_ = lean_ctor_get(v_x_7417_, 0);
lean_inc(v_a_7428_);
lean_dec_ref_known(v_x_7417_, 1);
v___x_7429_ = 0;
v___x_7430_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__3);
v___x_7431_ = ((lean_object*)(l_Std_Http_Server_serveConnection___redArg___lam__0___closed__5));
v___x_7432_ = lean_box(0);
v___x_7433_ = lean_obj_once(&l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8, &l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8_once, _init_l_Std_Http_Server_serveConnection___redArg___lam__0___closed__8);
v___x_7434_ = l_Std_Http_Config_toH1Config(v_config_7411_);
v_enableKeepAlive_7435_ = lean_ctor_get_uint8(v___x_7434_, sizeof(void*)*21);
v___x_7436_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_7436_, 0, v___x_7430_);
lean_ctor_set(v___x_7436_, 1, v___x_7433_);
lean_ctor_set(v___x_7436_, 2, v___x_7434_);
lean_ctor_set(v___x_7436_, 3, v___x_7431_);
lean_ctor_set(v___x_7436_, 4, v___x_7432_);
lean_ctor_set(v___x_7436_, 5, v___x_7432_);
lean_ctor_set_uint8(v___x_7436_, sizeof(void*)*6, v_enableKeepAlive_7435_);
lean_ctor_set_uint8(v___x_7436_, sizeof(void*)*6 + 1, v___x_7429_);
v___x_7437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_7437_, 0, v_client_7412_);
lean_ctor_set(v___x_7437_, 1, v___x_7436_);
lean_ctor_set(v___x_7437_, 2, v_extensions_7413_);
v___x_7438_ = l___private_Std_Http_Server_Connection_0__Std_Http_Server_Connection_handle___redArg(v_inst_7414_, v_inst_7415_, v___x_7437_, v_config_7411_, v_a_7428_, v_handler_7416_);
return v___x_7438_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___lam__0___boxed(lean_object* v_config_7439_, lean_object* v_client_7440_, lean_object* v_extensions_7441_, lean_object* v_inst_7442_, lean_object* v_inst_7443_, lean_object* v_handler_7444_, lean_object* v_x_7445_, lean_object* v___y_7446_){
_start:
{
lean_object* v_res_7447_; 
v_res_7447_ = l_Std_Http_Server_serveConnection___redArg___lam__0(v_config_7439_, v_client_7440_, v_extensions_7441_, v_inst_7442_, v_inst_7443_, v_handler_7444_, v_x_7445_);
return v_res_7447_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg(lean_object* v_inst_7448_, lean_object* v_inst_7449_, lean_object* v_client_7450_, lean_object* v_handler_7451_, lean_object* v_config_7452_, lean_object* v_extensions_7453_, lean_object* v_a_7454_){
_start:
{
lean_object* v___f_7456_; lean_object* v___x_7457_; uint8_t v___x_7458_; lean_object* v___x_7459_; lean_object* v___x_7460_; lean_object* v___x_7461_; 
v___f_7456_ = lean_alloc_closure((void*)(l_Std_Http_Server_serveConnection___redArg___lam__0___boxed), 8, 6);
lean_closure_set(v___f_7456_, 0, v_config_7452_);
lean_closure_set(v___f_7456_, 1, v_client_7450_);
lean_closure_set(v___f_7456_, 2, v_extensions_7453_);
lean_closure_set(v___f_7456_, 3, v_inst_7448_);
lean_closure_set(v___f_7456_, 4, v_inst_7449_);
lean_closure_set(v___f_7456_, 5, v_handler_7451_);
v___x_7457_ = lean_unsigned_to_nat(0u);
v___x_7458_ = 0;
lean_inc_ref(v_a_7454_);
v___x_7459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7459_, 0, v_a_7454_);
v___x_7460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7460_, 0, v___x_7459_);
v___x_7461_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_7457_, v___x_7458_, v___x_7460_, v___f_7456_);
return v___x_7461_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___redArg___boxed(lean_object* v_inst_7462_, lean_object* v_inst_7463_, lean_object* v_client_7464_, lean_object* v_handler_7465_, lean_object* v_config_7466_, lean_object* v_extensions_7467_, lean_object* v_a_7468_, lean_object* v_a_7469_){
_start:
{
lean_object* v_res_7470_; 
v_res_7470_ = l_Std_Http_Server_serveConnection___redArg(v_inst_7462_, v_inst_7463_, v_client_7464_, v_handler_7465_, v_config_7466_, v_extensions_7467_, v_a_7468_);
lean_dec_ref(v_a_7468_);
return v_res_7470_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection(lean_object* v_t_7471_, lean_object* v_00_u03c3_7472_, lean_object* v_inst_7473_, lean_object* v_inst_7474_, lean_object* v_client_7475_, lean_object* v_handler_7476_, lean_object* v_config_7477_, lean_object* v_extensions_7478_, lean_object* v_a_7479_){
_start:
{
lean_object* v___x_7481_; 
v___x_7481_ = l_Std_Http_Server_serveConnection___redArg(v_inst_7473_, v_inst_7474_, v_client_7475_, v_handler_7476_, v_config_7477_, v_extensions_7478_, v_a_7479_);
return v___x_7481_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_serveConnection___boxed(lean_object* v_t_7482_, lean_object* v_00_u03c3_7483_, lean_object* v_inst_7484_, lean_object* v_inst_7485_, lean_object* v_client_7486_, lean_object* v_handler_7487_, lean_object* v_config_7488_, lean_object* v_extensions_7489_, lean_object* v_a_7490_, lean_object* v_a_7491_){
_start:
{
lean_object* v_res_7492_; 
v_res_7492_ = l_Std_Http_Server_serveConnection(v_t_7482_, v_00_u03c3_7483_, v_inst_7484_, v_inst_7485_, v_client_7486_, v_handler_7487_, v_config_7488_, v_extensions_7489_, v_a_7490_);
lean_dec_ref(v_a_7490_);
return v_res_7492_;
}
}
lean_object* runtime_initialize_Std_Async_TCP(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_ContextAsync(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Transport(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Transport_Outbox(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Protocol_H1(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Config(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Server_Handler(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Watchdog(uint8_t builtin);
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
res = runtime_initialize_Std_Async_Watchdog(builtin);
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
lean_object* initialize_Std_Async_Watchdog(uint8_t builtin);
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
res = initialize_Std_Async_Watchdog(builtin);
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
